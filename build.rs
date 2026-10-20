fn main() {
    let bnf = "grammar/ISO_IEC_39075(en)+Cor1.bnf.xml";
    println!("cargo::rerun-if-changed={bnf}");
    if !std::path::Path::new(bnf).exists() {
        panic!("{bnf} is missing, run `just grammar`");
    }
}
