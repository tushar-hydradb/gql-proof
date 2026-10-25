//! Runs the witness oracle's records (`gql-proof oracle`) on turbolay's experimental gql
//! engine: for each record with a turbolay setup, loads the graph into the in-memory
//! storage, runs the sentence, and compares the rows with what the record expects. One
//! json line per record: {sentence, outcome, status, message, verdict, detail, rows}.
//! outcome is as in `turbolay_probe.rs`; verdict is agree, disagree, refused, failed,
//! timeout, panic or unjudged (a record of the status tier, run for its outcome only).
//!
//! Not part of gql-proof's build: `just turbolay-oracle <worktree>` copies it into a
//! turbolay worktree as `crates/cypher-engine/tests/zz_gql_proof_oracle.rs` and runs it. It
//! needs `serde_json = { workspace = true }` under that crate's `[dev-dependencies]`.

mod common;

use common::MemoryStorage;
use hydradb_cypher_engine::{
    CypherEngine, ListParameterMap, ParameterMap, QueryValue, RelationshipRecord, ScalarValue,
    VertexRecord,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::time::Duration;

fn scalar(v: &Value) -> ScalarValue {
    match v {
        Value::Null => ScalarValue::Null,
        Value::Bool(b) => ScalarValue::Boolean(*b),
        Value::Number(n) => match n.as_i64() {
            Some(i) => ScalarValue::Integer(i as i128),
            None => ScalarValue::Float(n.to_string().into_boxed_str()),
        },
        Value::String(s) => ScalarValue::String(s.as_str().into()),
        other => ScalarValue::String(other.to_string().into_boxed_str()),
    }
}

fn properties(v: &Value) -> BTreeMap<String, ScalarValue> {
    v.as_object()
        .map(|m| m.iter().map(|(k, v)| (k.clone(), scalar(v))).collect())
        .unwrap_or_default()
}

fn storage(setup: &Value) -> MemoryStorage {
    let vertices = setup["vertices"].as_array().cloned().unwrap_or_default();
    let relationships = setup["relationships"].as_array().cloned().unwrap_or_default();
    let vertices = vertices.iter().map(|v| VertexRecord {
        id: v["id"].as_u64().unwrap_or(0),
        labels: v["labels"]
            .as_array()
            .map(|l| l.iter().filter_map(|x| x.as_str().map(str::to_string)).collect())
            .unwrap_or_else(BTreeSet::new),
        properties: properties(&v["properties"]),
    });
    let relationships = relationships.iter().map(|r| RelationshipRecord {
        id: r["id"].as_u64().unwrap_or(0),
        source: r["source"].as_u64().unwrap_or(0),
        target: r["target"].as_u64().unwrap_or(0),
        relationship_type: r["relationship_type"].as_str().unwrap_or("").to_string(),
        properties: properties(&r["properties"]),
    });
    MemoryStorage::with_graph(vertices, relationships)
}

/// A result value in the oracle's own shape (`{kind, value}`, elements by id), so a row
/// compares with the record's `bag`, `row` and `binding` directly.
fn to_json(v: &QueryValue) -> Value {
    match v {
        QueryValue::Null => json!({ "kind": "Null" }),
        QueryValue::VertexId(id) => json!({ "kind": "Node", "value": id }),
        QueryValue::RelationshipId(id) => json!({ "kind": "Edge", "value": id }),
        QueryValue::Count(n) => json!({ "kind": "Int", "value": n }),
        QueryValue::Scalar(s) => match s {
            ScalarValue::Null => json!({ "kind": "Null" }),
            ScalarValue::Boolean(b) => json!({ "kind": "Bool", "value": b }),
            ScalarValue::Integer(i) => json!({ "kind": "Int", "value": i }),
            ScalarValue::Float(f) => json!({ "kind": "Float", "value": f.parse::<f64>().unwrap_or(f64::NAN) }),
            ScalarValue::String(s) => json!({ "kind": "Str", "value": s }),
            other => json!({ "kind": "Other", "value": format!("{other:?}") }),
        },
        QueryValue::List(items) => json!({ "kind": "List", "value": items.iter().map(to_json).collect::<Vec<_>>() }),
        QueryValue::Path(p) => {
            let mut ids = Vec::new();
            for (i, n) in p.nodes.iter().enumerate() {
                ids.push(json!(n.id));
                if let Some(r) = p.relationships.get(i) {
                    ids.push(json!(r.id));
                }
            }
            json!({ "kind": "Path", "value": ids })
        }
        QueryValue::Record(fields) => {
            let m: serde_json::Map<String, Value> = fields.iter().map(|(k, v)| (k.to_string(), to_json(v))).collect();
            json!({ "kind": "Record", "value": m })
        }
        other => json!({ "kind": "Other", "value": format!("{other:?}") }),
    }
}

/// Whether a returned value is the expected one: same kind and value, floats within a
/// relative tolerance, lists and records element by element.
fn matches(expected: &Value, got: &Value) -> bool {
    let (ek, gk) = (expected["kind"].as_str(), got["kind"].as_str());
    if ek != gk {
        // An exact literal 1 against an engine's float 1.0 is a finding, not a match.
        return false;
    }
    let (ev, gv) = (&expected["value"], &got["value"]);
    match ek {
        Some("Null") => true,
        Some("Float") => match (ev.as_f64(), gv.as_f64()) {
            (Some(a), Some(b)) => (a - b).abs() <= 1e-9 * a.abs().max(b.abs()).max(1.0),
            _ => false,
        },
        Some("List") => match (ev.as_array(), gv.as_array()) {
            (Some(e), Some(g)) => e.len() == g.len() && e.iter().zip(g).all(|(e, g)| matches(e, g)),
            _ => false,
        },
        Some("Record") => match (ev.as_object(), gv.as_object()) {
            (Some(e), Some(g)) => e.len() == g.len() && e.iter().all(|(k, v)| g.get(k).is_some_and(|w| matches(v, w))),
            _ => false,
        },
        _ => ev == gv,
    }
}

/// Whether two rows (column name to value) match column by column.
fn row_matches(expected: &serde_json::Map<String, Value>, columns: &[String], got: &[Value]) -> bool {
    if expected.len() != columns.len() {
        return false;
    }
    expected.iter().all(|(col, v)| {
        columns.iter().position(|c| c == col).is_some_and(|i| matches(v, &got[i]))
    })
}

/// Bag equality: every expected row matched by a distinct returned row, in order when the
/// expectation is ordered.
fn bag_matches(expected: &[Value], ordered: bool, columns: &[String], rows: &[Vec<Value>]) -> Result<(), String> {
    if expected.len() != rows.len() {
        return Err(format!("expected {} rows, got {}", expected.len(), rows.len()));
    }
    if ordered {
        for (i, (e, g)) in expected.iter().zip(rows).enumerate() {
            let Some(e) = e.as_object() else { return Err("a malformed expected row".to_string()) };
            if !row_matches(e, columns, g) {
                return Err(format!("row {i} differs: expected {e:?}, got {g:?}"));
            }
        }
        return Ok(());
    }
    let mut used = vec![false; rows.len()];
    for e in expected {
        let Some(e) = e.as_object() else { return Err("a malformed expected row".to_string()) };
        match rows.iter().enumerate().position(|(i, g)| !used[i] && row_matches(e, columns, g)) {
            Some(i) => used[i] = true,
            None => return Err(format!("expected row {e:?} not among the rows: {:?}", rows.iter().take(3).collect::<Vec<_>>())),
        }
    }
    Ok(())
}

fn judge(expect: &Value, columns: &[String], rows: &[Vec<Value>]) -> (&'static str, String) {
    if let Some(bag) = expect["bag"].as_array() {
        return match bag_matches(bag, expect["ordered"] == json!(true), columns, rows) {
            Ok(()) => ("agree", format!("the whole bag of {} rows", bag.len())),
            Err(why) => ("disagree", why),
        };
    }
    if expect["rows"] == json!(0) {
        return if rows.is_empty() {
            ("agree", "no rows, as expected".to_string())
        } else {
            ("disagree", format!("expected no rows, got {}", rows.len()))
        };
    }
    if expect["result"] == json!(false) {
        return ("agree", "completed, no result expected".to_string());
    }
    let Some(row) = expect["row"].as_object() else {
        return ("agree", format!("completed, {} rows, no row claimed", rows.len()));
    };
    for got in rows {
        let values: BTreeMap<&str, &Value> = columns.iter().map(String::as_str).zip(got).collect();
        if row
            .iter()
            .all(|(col, bound)| values.get(col.as_str()).is_some_and(|g| matches(bound, g)))
        {
            return ("agree", format!("the witness row is among {}", rows.len()));
        }
    }
    (
        "disagree",
        format!("the witness row is not among {} rows", rows.len()),
    )
}

#[tokio::test(flavor = "multi_thread")]
async fn run_oracle_records() {
    let input = std::env::var("GQL_PROOF_IN").expect("GQL_PROOF_IN");
    let output = std::env::var("GQL_PROOF_OUT").expect("GQL_PROOF_OUT");
    let mut out = std::fs::File::create(output).unwrap();
    for line in std::fs::read_to_string(input).unwrap().lines() {
        let record: Value = serde_json::from_str(line).unwrap();
        let Some(sentence) = record["sentence"].as_str().map(str::to_string) else {
            continue;
        };
        let setup = &record["setup"]["turbolay"];
        if setup.is_null() {
            continue;
        }
        let witness = record["expect"]["tier"] == json!("witness");
        let _ = witness;
        let parameters: ParameterMap = properties(&record["parameters"]);
        let engine = CypherEngine::new(storage(setup));
        let prepared = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            engine.prepare_with_lists(&sentence, &parameters, &ListParameterMap::new())
        }));
        let mut rows_json: Vec<Vec<Value>> = Vec::new();
        let mut columns: Vec<String> = Vec::new();
        let (outcome, status, message) = match prepared {
            Err(_) => ("panic", String::new(), "prepare panicked".to_string()),
            Ok(Err(e)) => ("refused", e.gql_status().to_string(), e.to_string()),
            Ok(Ok(p)) => {
                let run = tokio::time::timeout(Duration::from_secs(5), async {
                    tokio::spawn(async move {
                        engine.execute_prepared_with_status(&p).await.map(|o| {
                            let columns: Vec<String> =
                                o.result.columns.iter().map(|c| c.name.clone()).collect();
                            let rows: Vec<Vec<Value>> = o
                                .result
                                .rows
                                .iter()
                                .map(|r| r.values.iter().map(to_json).collect())
                                .collect();
                            (o.status.status.to_string(), columns, rows)
                        })
                    })
                    .await
                })
                .await;
                match run {
                    Err(_) => ("timeout", String::new(), String::new()),
                    Ok(Err(_)) => ("panic", String::new(), "execute panicked".to_string()),
                    Ok(Ok(Err(e))) => ("failed", e.gql_status().to_string(), e.to_string()),
                    Ok(Ok(Ok((s, c, r)))) => {
                        let n = r.len();
                        columns = c;
                        rows_json = r;
                        ("ok", s, format!("{n} rows"))
                    }
                }
            }
        };
        let mut observed: Vec<Vec<Value>> = Vec::new();
        let expected_exception = record["expect"]["outcome"] == json!("exception");
        let judged = record["expect"]["tier"] == json!("bag") || witness;
        let (verdict, detail) = match (outcome, judged) {
            (_, true) if expected_exception => {
                let want = record["expect"]["status"].as_str().unwrap_or("");
                if outcome == "failed" && status == want {
                    ("agree", format!("raised {status} as expected"))
                } else if outcome == "failed" && status.get(..2) == want.get(..2) {
                    ("agree", format!("raised {status} for expected {want}: same class, another subclass"))
                } else if outcome == "failed" {
                    ("disagree", format!("expected {want}, raised {status}: {message}"))
                } else {
                    ("disagree", format!("expected {want}, outcome {outcome}: {message}"))
                }
            }
            ("ok", true) if !record["observe"].is_null() => {
                // The observation query: the same patterns with their variables returned.
                let query = record["observe"]["query"].as_str().unwrap_or("").to_string();
                let engine = CypherEngine::new(storage(setup));
                let prepared = engine.prepare_with_lists(&query, &parameters, &ListParameterMap::new());
                match prepared {
                    Err(e) => ("observe refused", format!("{}: {e}", e.gql_status())),
                    Ok(p) => {
                        let run = tokio::time::timeout(Duration::from_secs(5), async {
                            engine.execute_prepared_with_status(&p).await.map(|o| {
                                let columns: Vec<String> =
                                    o.result.columns.iter().map(|c| c.name.clone()).collect();
                                let rows: Vec<Vec<Value>> = o
                                    .result
                                    .rows
                                    .iter()
                                    .map(|r| r.values.iter().map(to_json).collect())
                                    .collect();
                                (columns, rows)
                            })
                        })
                        .await;
                        match run {
                            Err(_) => ("observe timeout", String::new()),
                            Ok(Err(e)) => ("observe failed", format!("{}: {e}", e.gql_status())),
                            Ok(Ok((c, r))) => {
                                let (v, d) = judge(&record["observe"], &c, &r);
                                observed = r;
                                (v, d)
                            }
                        }
                    }
                }
            }
            ("ok", true) => judge(&record["expect"], &columns, &rows_json),
            ("ok", false) => ("unjudged", "status tier".to_string()),
            (other, _) => (other, message.clone()),
        };
        if !observed.is_empty() {
            rows_json = observed;
        }
        let shown: Vec<&Vec<Value>> = rows_json.iter().take(3).collect();
        let row = json!({
            "sentence": sentence,
            "outcome": outcome,
            "status": status,
            "message": message,
            "verdict": verdict,
            "detail": detail,
            "columns": columns,
            "rows": shown,
        });
        writeln!(out, "{row}").unwrap();
    }
}
