#!/usr/bin/env python3
"""Check that every solution file contains, verbatim, the definitions and the theorem statement of
its challenge file.  Run from `lean/`."""
import pathlib, re, sys

def read(p):
    return pathlib.Path(p).read_text()

def between(s, start, end):
    i = s.index(start)
    j = s.index(end, i)
    return s[i:j]

def statement(s, name):
    m = re.search(r'theorem ' + re.escape(name) + r'\b.*?:=', s, re.S)
    return m.group(0)

results = []
# Disanto–Rosenberg: definitions = from the namespace line up to the docstring of the theorem.
ch = read('ComparatorChallenges/AncestralConfigurations.lean')
defs = between(ch, 'namespace KOS.AncestralConfigurations\n', '/-- **Disanto–Rosenberg conjecture.**')
thm = statement(ch, 'disanto_rosenberg')
for sol, ns in [('KOS/Phylogenetics/AncestralConfigurations/Main.lean', 'KOS.AncestralConfigurations'),
                ('KOS/Phylogenetics/AncestralConfigurations/Independent.lean',
                 'KOS.AncestralConfigurationsIndependent')]:
    s = read(sol)
    d = defs.replace('namespace KOS.AncestralConfigurations\n', f'namespace {ns}\n')
    results.append((sol, d in s, thm in s))
# OEIS A100475: definitions = the block between `namespace OeisA100475` and `end OeisA100475`.
ch = read('ComparatorChallenges/OEISA100475.lean')
defs = between(ch, 'namespace OeisA100475\n', 'end OeisA100475')
thm = statement(ch, 'not_conjecture')
s = read('KOS/NumberTheory/OEIS/A100475.lean')
results.append(('KOS/NumberTheory/OEIS/A100475.lean', defs in s, thm in s))

ok = True
for sol, d, t in results:
    print(f'{sol}: definitions verbatim: {d}; statement verbatim: {t}')
    ok &= d and t
sys.exit(0 if ok else 1)
