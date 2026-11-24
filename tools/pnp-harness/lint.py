#!/usr/bin/env python3
"""Pre-flight linter: the format rules from join.txt / CONTRIBUTING.md that are refused
outright, plus the exact-statement check. Catching these here costs no check run."""
import json, os, re, sys

S = os.path.dirname(os.path.abspath(__file__))
REPO = "/home/user/pequalnp-proofs"
gid = sys.argv[1]
meta = json.load(open(os.path.join(S, "steps", gid + ".json")))
g = meta["gap"]
path, module, stmt = g["file"], g["module"], g["statement"]
allowed = set(g.get("imports") or [])
full = os.path.join(REPO, path)
bad, warn = [], []

raw = open(full, "rb").read()
if len(raw) > 512 * 1024: bad.append("file is larger than 512 KiB")
try: text = raw.decode("utf-8")
except UnicodeDecodeError as e: print("FATAL: not UTF-8:", e); sys.exit(1)
lines = text.split("\n")

# --- imports: a prefix of plain `import X` lines, nothing else among them ---
i, imports = 0, []
while i < len(lines) and lines[i].startswith("import "):
    m = re.fullmatch(r"import ([A-Za-z0-9_.]+)", lines[i].rstrip())
    if not m: bad.append("line %d is not a plain `import Some.Module`: %r" % (i + 1, lines[i]))
    else: imports.append(m.group(1))
    i += 1
if not imports: bad.append("no import lines at the top")
rest = "\n".join(lines[i:])
if re.search(r"\bimport\b", rest): bad.append("the word `import` appears after the import lines (rule c/3)")
for m in imports:
    if m == "Mathlib" or m.startswith("Mathlib."): continue
    if m in allowed: continue
    bad.append("import not allowed for this step: %s (allowed besides Mathlib: %s)" % (m, sorted(allowed) or "none"))

# --- hard refusals ---
if '"' in text: bad.append("a double quote appears in the file (rule c): no string literals")
for tok in ["initialize", "macro", "syntax", "notation", "elab", "native_decide"]:
    for n, l in enumerate(lines[i:], start=i + 1):
        if re.search(r"\b%s\b" % tok, l): bad.append("forbidden word `%s` on line %d (rule a) - reword even in comments" % (tok, n))
for n, l in enumerate(lines[i:], start=i + 1):
    if re.match(r"\s*#", l): bad.append("a `#` command on line %d (rule a)" % n)
    if re.match(r"\s*attribute\b", l): bad.append("an `attribute` command on line %d (rule a)" % n)
for m in re.finditer(r"@\[([^\]]*)\]", rest):
    if m.group(1).strip() not in ("simp", "local simp"):
        bad.append("attribute @[%s] is not allowed; only @[simp] and @[local simp] (rule d)" % m.group(1).strip())
for n, l in enumerate(lines[i:], start=i + 1):
    if re.match(r"\s*set_option", l):
        if not re.fullmatch(r"set_option (maxRecDepth|maxHeartbeats|synthInstance\.maxSize|synthInstance\.maxHeartbeats) \d+ in", l.strip()):
            bad.append("line %d: set_option must be exactly `set_option <one of the four> <number> in` on its own line (rule d): %r" % (n, l.strip()))
if re.search(r"\bsorry\b", rest) or re.search(r"\bsorryAx\b", rest): bad.append("`sorry` is still in the file")
if re.search(r"^\s*axiom\b", rest, re.M): bad.append("a new `axiom` is declared")

# --- the one theorem, with the posted statement verbatim ---
anchor = "theorem %s : %s :=" % (module, stmt)
if anchor not in text:
    bad.append("the theorem is not present with the posted statement VERBATIM. The file must contain,\n"
               "    character for character, `theorem %s : <the posted statement> :=`.\n"
               "    Do not reformat, rewrap, rename a binder or add parentheses in the statement." % module)
decls = [(n, l) for n, l in enumerate(lines[i:], start=i + 1)
         if re.match(r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b", l)]
outside, depth = [], 0
for n, l in enumerate(lines[i:], start=i + 1):
    if re.match(r"(namespace|section)\b", l): depth += 1
    elif re.match(r"end\b", l): depth -= 1
    elif depth == 0 and re.match(r"(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b", l): outside.append((n, l.split(":")[0][:90]))
for n, l in outside:
    if not l.startswith("theorem " + module): bad.append("line %d declares `%s` outside any namespace block; only the one theorem `%s` may stand there (rule 7)" % (n, l.strip(), module))
if sum(1 for n, l in outside if l.startswith("theorem " + module)) != 1:
    bad.append("expected exactly one top-level `theorem %s`, found %d" % (module, sum(1 for n, l in outside if l.startswith("theorem " + module))))

# --- the slow path (judged, but waits for a human reader) ---
for n, l in enumerate(lines[i:], start=i + 1):
    s = l.strip()
    if s.startswith("--") or not s: continue
    if re.match(r"(structure|inductive|instance|class)\b", s): warn.append("line %d declares its own data type or instance (rule e): the pull request is judged but waits for a person. Prefer Mathlib's types." % n)
for n, l in enumerate(lines[i:], start=i + 1):
    if "--" in l and not l.strip().startswith("--"):
        pass
print("FILE  ", path)
print("MODULE", module)
if bad:
    print("\nLINT FAILED - fix these before submitting (they are refused outright):")
    for b in bad: print("  *", b)
if warn:
    print("\nLINT WARNINGS (still judged, but merged only after a person reads it):")
    for w in sorted(set(warn)): print("  -", w)
if not bad: print("\nLINT OK" + (" (with warnings)" if warn else ""))
sys.exit(1 if bad else 0)
