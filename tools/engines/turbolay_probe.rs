//! Runs gql-proof sentences on turbolay's experimental gql engine, over an empty graph, and
//! writes one json line per sentence: {sentence, outcome, status, message}. outcome is ok,
//! refused (at preparation), failed (at execution), timeout or panic.
//!
//! Not part of gql-proof's build: `just turbolay <worktree> <sentences>` copies it into a
//! turbolay worktree as `crates/cypher-engine/tests/zz_gql_proof.rs` and runs it. It needs
//! `serde_json = { workspace = true }` under that crate's `[dev-dependencies]`.

mod common;

use common::MemoryStorage;
use hydradb_cypher_engine::{CypherEngine, ListParameterMap, ParameterMap};
use std::io::Write;
use std::time::Duration;

#[tokio::test(flavor = "multi_thread")]
async fn run_generated_sentences() {
    let input = std::env::var("GQL_PROOF_IN").expect("GQL_PROOF_IN");
    let output = std::env::var("GQL_PROOF_OUT").expect("GQL_PROOF_OUT");
    let mut out = std::fs::File::create(output).unwrap();
    for line in std::fs::read_to_string(input).unwrap().lines() {
        let record: serde_json::Value = serde_json::from_str(line).unwrap();
        let sentence = record["sentence"].as_str().unwrap().to_string();
        let engine = CypherEngine::new(MemoryStorage::with_graph(Vec::new(), Vec::new()));
        let prepared = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            engine.prepare_with_lists(&sentence, &ParameterMap::new(), &ListParameterMap::new())
        }));
        let (outcome, status, message) = match prepared {
            Err(_) => ("panic", String::new(), "prepare panicked".to_string()),
            Ok(Err(e)) => ("refused", e.gql_status().to_string(), e.to_string()),
            Ok(Ok(p)) => {
                let run = tokio::time::timeout(Duration::from_secs(5), async {
                    tokio::spawn(async move {
                        engine
                            .execute_prepared_with_status(&p)
                            .await
                            .map(|o| (o.status.status.to_string(), o.result.rows.len()))
                    })
                    .await
                })
                .await;
                match run {
                    Err(_) => ("timeout", String::new(), String::new()),
                    Ok(Err(_)) => ("panic", String::new(), "execute panicked".to_string()),
                    Ok(Ok(Err(e))) => ("failed", e.gql_status().to_string(), e.to_string()),
                    Ok(Ok(Ok((s, rows)))) => ("ok", s, format!("{rows} rows")),
                }
            }
        };
        let row = serde_json::json!({
            "sentence": sentence,
            "outcome": outcome,
            "status": status,
            "message": message,
        });
        writeln!(out, "{row}").unwrap();
    }
}
