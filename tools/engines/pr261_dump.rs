
// Appended by `just corpus-261` for one run, then removed: every query turbolay#261's
// generators build, as jsonl, for gql-proof's `cover`.
#[test]
fn zz_gql_proof_dump() {
    let Ok(path) = std::env::var("GQL_PROOF_OUT") else {
        return;
    };
    let config = GenerationConfig::from_env();
    let mut out = String::new();
    for family in families(&config) {
        let all = family
            .positive_controls
            .iter()
            .map(|c| (true, c))
            .chain(family.cases.iter().map(|c| (false, c)));
        for (control, case) in all {
            let expected = match &case.expected {
                api::Expected::PrepareError => "prepare-error",
                api::Expected::ExecuteError => "execute-error",
                api::Expected::Execute => "execute",
                api::Expected::Result(_) => "result",
            };
            let record = serde_json::json!({
                "family": family.name,
                "id": case.id,
                "rule": format!("{:?}", case.rule),
                "control": control,
                "expected": expected,
                "status": format!("{:?}", case.expected_status),
                "query": case.query,
            });
            out.push_str(&record.to_string());
            out.push('\n');
        }
    }
    std::fs::write(path, out).unwrap();
}
