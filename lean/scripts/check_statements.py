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

# Dickey–Rosenberg Conjecture 14: definitions = from the namespace line up to the first theorem.
ch = read('ComparatorChallenges/DickeyRosenberg.lean')
defs = between(ch, 'namespace DickeyRosenberg\n', '/-- Dickey–Rosenberg Conjecture 14 (i)')
s = read('KOS/Phylogenetics/LabeledHistories/Main.lean')
results.append(('KOS/Phylogenetics/LabeledHistories/Main.lean', defs.rstrip() in s,
                re.search(r'theorem conjecture14i\b\s*:\s*Conjecture14i', s) is not None and
                re.search(r'theorem conjecture14ii\b\s*:\s*Conjecture14ii', s) is not None))

# Results 004-007: definitions = from the namespace line up to the first challenge theorem.
for ch_file, sol, ns, end_marker, thms in [
        ('ComparatorChallenges/ForcingNumbers.lean', 'KOS/GraphTheory/ForcingNumbers/Main.lean',
         'Forcing', '/-- Problem 5.5.', ['problem55']),
        ('ComparatorChallenges/ThirdLargestCosetLeader.lean', 'KOS/CodingTheory/ThirdLargestCosetLeader/Main.lean',
         'CosetB', 'theorem conjecture25_false', ['conjecture25_false', 'counterexample_q4_m12']),
        ('ComparatorChallenges/LocalEnergy.lean', 'KOS/ChemicalGraphTheory/LocalEnergy/Main.lean',
         'DedePopat', '/-- **Main theorem.**',
         ['not_conjecture1', 'not_conjecture1NonEquienergetic', 'not_corollary2']),
        ('ComparatorChallenges/DepthVariance.lean', 'KOS/Phylogenetics/DepthVariance/Main.lean',
         'DepthVariance', '/-- Discussion, first conjecture', ['minimum_variance_depth_unique_false']),
        ('ComparatorChallenges/TwoLargestCosetLeaders.lean', 'KOS/CodingTheory/TwoLargestCosetLeaders/Main.lean',
         'CosetA', '-- Domain clarification made before proof', ['conjecturesA'])]:
    ch = read(ch_file)
    defs = between(ch, f'namespace {ns}\n', end_marker)
    s = read(sol)
    results.append((sol, defs in s, all(statement(ch, t) in s for t in thms)))

ok = True
for sol, d, t in results:
    print(f'{sol}: definitions verbatim: {d}; statement verbatim: {t}')
    ok &= d and t
sys.exit(0 if ok else 1)
