//! Fills definitions the standard gives in prose ("!! See the Syntax Rules"). This is the
//! seam the context provider will plug into later; for now it hands out fixed stubs.

use rand_chacha::ChaCha8Rng;

pub trait LeafProvider {
    fn leaf(&mut self, name: &str, rng: &mut ChaCha8Rng) -> String;
}

/// One fixed, valid-looking stub per prose definition. Anything without a stub prints as
/// `<name>` so the gap shows up in the output instead of being papered over. Deliberately
/// unstubbed: `implementation-defined access mode`, `external object reference` and
/// `other language character`, which depend on the implementation or have no sensible default.
#[derive(Debug, Default)]
pub struct StubProvider;

impl LeafProvider for StubProvider {
    fn leaf(&mut self, name: &str, _rng: &mut ChaCha8Rng) -> String {
        let stub = match name {
            "identifier start" => "a",
            "identifier extend" => "b",
            "character representation"
            | "single quoted character representation"
            | "double quoted character representation"
            | "accent quoted character representation"
            | "string literal character" => "x",
            "unsigned decimal in scientific notation" => "1E3",
            "double single quote" => "''",
            "double double quote" => "\"\"",
            "double grave accent" => "``",
            "SQL-datetime literal" => "DATE '2024-01-01'",
            "SQL-interval literal" => "INTERVAL '1' DAY",
            "whitespace" | "truncating whitespace" => " ",
            "newline" => "\n",
            "bidirectional control character" => "\u{200E}",
            "simple comment character" | "bracketed comment contents" => "x",
            // A decimal digit outside 0-9: ARABIC-INDIC DIGIT THREE.
            "other digit" => "\u{0663}",
            _ => return format!("<{name}>"),
        };
        stub.to_string()
    }
}
