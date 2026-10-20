//! Fills definitions the standard gives only in prose ("!! See the Syntax Rules"). This is the
//! seam the context provider will plug into later; for now it hands out fixed stubs.

use rand_chacha::ChaCha8Rng;

pub trait LeafProvider {
    /// Whether this provider can fill `name` at all. Productions that need a leaf it cannot
    /// fill are excluded from generation and reported, instead of printing a placeholder.
    fn supports(&self, name: &str) -> bool;

    fn leaf(&mut self, name: &str, rng: &mut ChaCha8Rng) -> String;
}

/// One fixed stub per prose definition, each checked against the Syntax Rule that defines it
/// (ISO/IEC 39075:2024, clause and rule noted per entry).
#[derive(Debug, Default)]
pub struct StubProvider;

impl StubProvider {
    fn stub(name: &str) -> Option<&'static str> {
        Some(match name {
            // 21.3 SR 1, 2: XID_Start (or underscore) and XID_Continue. SR 18 forbids a
            // reserved word, which `a`, `ab`, `abb`, ... never are.
            "identifier start" => "a",
            "identifier extend" => "b",
            // 21.2 SR 40, 41: any source character that is not a quote, reverse solidus or
            // control character.
            "character representation" | "string literal character" => "x",
            // 21.2 SR 69, 70: the datetime and interval literals of ISO/IEC 9075-2:2023.
            "SQL-datetime literal" => "DATE '2024-01-01'",
            "SQL-interval literal" => "INTERVAL '1' DAY",
            // 21.3 SR 6, 7: any White_Space run; truncating whitespace always includes space.
            "whitespace" | "truncating whitespace" => " ",
            // 21.3 SR 12: the end-of-line indicator is implementation-defined (IA023). Line
            // feed is the usual choice.
            "newline" => "\n",
            // 21.3 SR 8: one of U+202A..U+202E, U+2066..U+2069. FIRST STRONG ISOLATE.
            "bidirectional control character" => "\u{2068}",
            // 21.3 SR 9, 10: anything without a newline, anything without `*/`.
            "simple comment character" | "bracketed comment contents" => "x",
            // 21.4 SR 2: general category Nd outside 0-9. ARABIC-INDIC DIGIT THREE.
            "other digit" => "\u{0663}",
            // 21.4 SR 1: any character outside <GQL language character>.
            "other language character" => "\u{00E9}",
            // 17.8 SR 2, 3: a URI with a mandatory scheme, containing a colon. A `urn:` keeps
            // `//` out, which would otherwise read as a <simple comment introducer>.
            "external object reference" => "urn:example:graph",
            // 8.2 SR 3: Format and Syntax Rules are implementation-defined (IE002), so there is
            // nothing portable to generate.
            "implementation-defined access mode" => return None,
            _ => return None,
        })
    }
}

impl LeafProvider for StubProvider {
    fn supports(&self, name: &str) -> bool {
        Self::stub(name).is_some()
    }

    fn leaf(&mut self, name: &str, _rng: &mut ChaCha8Rng) -> String {
        Self::stub(name)
            .unwrap_or_else(|| panic!("no stub for <{name}>"))
            .to_string()
    }
}
