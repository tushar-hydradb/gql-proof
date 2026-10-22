"""Concrete violations of not-modelled syntax rules in generated sentences: approximate,
text-level detectors, each printing its count and shortest example."""
import json, re, sys

def ints(tok):
    t = tok.lower()
    try:
        if t.startswith("0x"): return int(t[2:], 16)
        if t.startswith("0o"): return int(t[2:], 8)
        if t.startswith("0b"): return int(t[2:], 2)
        return int(t)
    except ValueError:
        return None

def braces(s, start):
    """The text inside the brace block opening at `start`."""
    depth = 0
    for i in range(start, len(s)):
        if s[i] == "{": depth += 1
        elif s[i] == "}":
            depth -= 1
            if depth == 0: return s[start + 1:i]
    return s[start + 1:]

NUM = r"(0[xob][0-9a-fA-F]+|\d+)"
checks = {}
def check(name):
    def wrap(f):
        checks[name] = f
        return f
    return wrap

@check("21.3 SR 4: empty delimited identifier")
def _(s): return '""' in s or "``" in s

@check("16.11 SR 3: quantifier upper bound 0 or below lower")
def _(s):
    for m in re.finditer(r"\{\s*" + NUM + r"?\s*,\s*" + NUM + r"\s*\}", s):
        lo, hi = ints(m.group(1)) if m.group(1) else 0, ints(m.group(2))
        if hi is not None and (hi == 0 or (lo is not None and hi < lo)):
            return True
    return False

@check("18.9 SR 7/10/29: zero length or precision")
def _(s):
    return re.search(r"\b(CHAR|VARCHAR|STRING|BINARY|VARBINARY|BYTES|DECIMAL|DEC)\s*\(\s*(0[xob]0+|0)\s*[,)]", s) is not None

@check("20.6 SR 10: VALUE subquery without LIMIT 1")
def _(s):
    for m in re.finditer(r"\bVALUE\s*\{", s):
        body = braces(s, m.end() - 1)
        if not re.search(r"\bLIMIT\s+(0[xob]0*1|1)\b", body) and not re.search(r"\b(COUNT|SUM|AVG|MIN|MAX|COLLECT_LIST)\s*\(", body):
            return True
    return False

@check("19.4 SR 5, 20.6 SR 8, 11.2 SR 2: EXISTS, VALUE or table body is FINISH")
def _(s):
    # The declared type of the body is the last statement's; FINISH is the empty type. Text
    # level: only a body that is FINISH alone or ends in NEXT FINISH, a lower bound.
    for m in re.finditer(r"\b(VALUE|EXISTS)\s*\{", s):
        body = braces(s, m.end() - 1).strip()
        if re.fullmatch(r"(\{\s*)*FINISH(\s*\})*", body) or re.search(r"\bNEXT\s+FINISH\s*$", body):
            return True
    return False

@check("9.1 SR 7: data-modifying or catalog statement inside a query body")
def _(s):
    for m in re.finditer(r"\b(VALUE|EXISTS)\s*\{", s):
        body = braces(s, m.end() - 1)
        if re.search(r"\b(INSERT|SET|REMOVE|DELETE|CREATE|DROP)\b", body):
            return True
    return False

@check("14.2 SR 3: mixed query conjunctions at one level")
def _(s):
    depth, kinds = 0, {}
    for tok in re.findall(r"[{}]|\b(?:UNION|EXCEPT|INTERSECT|OTHERWISE)\b", s):
        if tok == "{": depth += 1
        elif tok == "}": kinds.pop(depth, None); depth -= 1
        else:
            kinds.setdefault(depth, set()).add(tok)
            if len(kinds[depth]) > 1: return True
    return False

@check("8.2 SR 2: more than one access mode")
def _(s): return re.search(r"READ\s+(ONLY|WRITE)\s*,\s*READ\s+(ONLY|WRITE)", s) is not None

@check("20.24 SR 3: TRIM with neither specification nor trim string")
def _(s): return re.search(r"\bTRIM\s*\(\s*FROM\b", s) is not None

@check("22.1 SR 3: $$ parameter with no request behind it")
def _(s): return "$$" in s

@check("14.12 SR 7: SELECT * with GROUP BY")
def _(s): return re.search(r"\bSELECT\s+(ALL\s+|DISTINCT\s+)?\*.*\bGROUP\s+BY\b", s) is not None

# Not a syntax rule: valid GQL that raises at run time. 4.4.4 invalidates a reference whose
# referent is deleted, and touching its content raises 22G11. No rule in the generator keeps
# it out (typestate), so a list holds such sentences or not by which witness extraction picks.
@check("4.4.4, 22G11 (dynamic): a variable used after DELETE")
def _(s):
    for m in re.finditer(r"\bDELETE\s+(?:DETACH\s+|NODETACH\s+)?([a-z]\w*)", s):
        v, rest = m.group(1), s[m.end():]
        if re.search(rf"\b(SET|REMOVE)\s+{v}\b|\b{v}\s*\.\s*\w|\b{v}\s*=\s*\{{|,\s*{v}\s*(IS|:)", rest):
            return True
    return False

for path in sys.argv[1:]:
    rows = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"): continue
        try: rows.append(json.loads(line)["sentence"])
        except (ValueError, KeyError): rows.append(line)
    print(f"== {path.split('/')[-1]}: {len(rows)} sentences")
    for name, f in checks.items():
        hits = [s for s in rows if f(s)]
        if hits:
            ex = min(hits, key=len)
            print(f"  {len(hits):5}  {name}\n         e.g. {ex[:150]}")
