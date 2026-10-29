# Readme

This repository contains mathematical manuscripts and supporting proof artifacts produced by AI models — Claude Opus 5.5 and Claude Fable 5.1 (Anthropic) and GPT-6-Astra (OpenAI) — working together as a team of agents. The models are the authors of every manuscript, proof and program here.

The goal of the project was to find open problems that are still unsolved, solve them completely, verify the results in Lean 4, and write them up. All eight results in the current release have their main theorems formalized in Lean.

In our view, these manuscripts are best understood as raw research data rather than polished academic papers. We defer to the mathematical community on matters of credit, precedence and concurrent work. If you know of earlier work on these questions, or find an error, please open an issue.

## Navigating the collection

The current catalogue contains 8 manuscripts organized into 8 families. All top-line results are formalized.

- Start with the [overview](overview.pdf) for descriptions of the families.
- Use the [manuscript map](CONTENTS.md) to find individual papers and their supporting materials.
- The [`preprints/`](preprints/) directory contains PDFs, LaTeX sources, supporting code, and manuscript-specific citation and build instructions.
- The [Lean library](lean/README.md) and [formalization catalogue](lean/formalization.yaml) describe the formal proofs, their associated papers, and how to check them.
- Updates to the repository are described in the [history](history.md).

| Family | Result | Field | Lean |
|---|---|---|---|
| 001 | [Proof of the Disanto–Rosenberg conjecture on non-equivalent ancestral configurations](preprints/The-maximum-number-of-non-equivalent-ancestral-configurations-October-29-2026/paper.pdf) | Mathematical biology / combinatorics | two independent proofs |
| 002 | [The reversed-prime iteration of OEIS A100475 never enters a cycle](preprints/The-reversed-prime-iteration-of-OEIS-A100475-never-enters-a-cycle-October-29-2026/paper.pdf) | Number theory | yes |
| 003 | [Proof of the Dickey–Rosenberg conjecture on maximally probable labeled topologies with simultaneity](preprints/Maximally-probable-labeled-topologies-with-simultaneity-October-29-2026/paper.pdf) | Mathematical biology / combinatorics | yes |
| 004 | [Answer to a question of Liu, Diwan and Zhang on the minimum and maximum forcing numbers of bipartite graphs](preprints/The-minimum-and-maximum-forcing-numbers-of-bipartite-graphs-October-29-2026/paper.pdf) | Graph theory / mathematical chemistry | yes |
| 005 | [Disproof of the uniqueness conjecture of Coronado, Mir, Rosselló and Rotger for minimum-variance phylogenetic trees](preprints/Minimum-variance-phylogenetic-trees-are-not-unique-up-to-depth-equivalence-October-29-2026/paper.pdf) | Mathematical biology | yes |
| 006 | [Disproof of Conjecture 1 and Corollary 2 of Dede and Popat on locally equienergetic graphs](preprints/Connected-locally-equienergetic-graphs-October-29-2026/paper.pdf) | Mathematical chemistry / spectral graph theory | yes |
| 007 | [Proof of two conjectures of Liu, Wu and Zhu on the two largest coset leaders modulo (q+1)(q^m±1)](preprints/A-proof-of-two-conjectures-of-Liu-Wu-and-Zhu-on-coset-leaders-October-29-2026/paper.pdf) | Coding theory | yes |
| 008 | [Disproof of Conjecture 25 of Liu, Li, Guo and Song on the third largest coset leader modulo q^m+1](preprints/A-counterexample-to-a-conjecture-of-Liu-Li-Guo-and-Song-on-coset-leaders-October-29-2026/paper.pdf) | Coding theory | yes |

## How the results were produced

All work was done on October 29, 2026, in a single session.

- **Orchestration.** Claude Opus 5.5, running in Claude Code, coordinated the work and delegated tasks to further Claude Opus 5.5 agents, to GPT-6-Astra through the Codex CLI at maximum reasoning effort, and to Claude Fable 5.1.
- **Choosing problems.** Four agents triaged the roughly 980 statements marked open in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit of 2026-10-28; Erdős problems, OEIS, Ben Green's list, Wikipedia, papers), checking the current status of each promising item on the web. Many of these lists have been heavily worked on by AI systems during 2025–2026, so further agents and both advisor models searched for precise conjectures posed in papers from chemistry, theoretical computer science, theoretical physics and mathematical biology. Results 001 and 003–008 came out of that cross-disciplinary search: 001, 005 and 006 were proposed by GPT-6-Astra, 003 by Claude Fable 5.1, and 004, 007 and 008 by Claude Opus 5.5 agents searching the chemistry, biology and coding-theory literature; result 002 came out of the OEIS triage. The proofs of results 003, 004 and 007 and the counterexample and minimality proof of result 005 were found by GPT-6-Astra; the counterexamples of result 006 were found by GPT-6-Astra (order 16) and by Claude Opus 5.5 (the second pair of order 16 and the exhaustive search up to order 10), and the counterexample of result 008 by a Claude Opus 5.5 agent.
- **Proofs and checks.** Every statement was checked by exhaustive computation for small cases. The proofs of results 001 and 003–007 were refereed independently by Claude Fable 5.1 against the definitions of the original papers; for the disproofs, the counterexamples were also re-checked independently by separate programs.
- **Search for earlier work.** For each question we checked citation lists (Semantic Scholar, OpenAlex), arXiv, the OEIS and general web search, and, since many recent results are posted only on GitHub, also GitHub itself: code, repository, issue and pull-request search, the full text of the manuscript map, overview and LaTeX sources of [openai/math](https://github.com/openai/math), and collections of AI-produced solutions (for example Kuberwastaken/c5-k4, where A100475 is listed as unresolved). We found no earlier resolution of any of the eight questions. One further result of this session, a Lean-verified proof of a conjecture of Mir, Rotger and Rosselló on the Colless index, turned out to have been obtained earlier by others (in the GitHub repositories kei825/open-questions-2026 and valyuAI/research) and is therefore not included. GitHub code search does not index PDF files or private repositories, so this search cannot be complete.
- **Formal verification.** For each result the Lean statement was fixed before any proof was written (the files in [`lean/ComparatorChallenges/`](lean/ComparatorChallenges/)). Result 001 was then formalized twice, independently, by GPT-6-Astra and by a Claude Opus 5.5 agent, and connected in Lean to the original definition of ancestral configurations through realizations of the gene tree; result 003 was formalized by GPT-6-Astra, including the paper's own recursive definition of the extremal tree. All main theorems depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry` and no `native_decide` are used, and the proof files contain no metaprogramming or code that runs at build time. All eight statements are also checked with [Comparator](https://github.com/leanprover/comparator) (configurations in `lean/ComparatorChallenges/`), using both the Lean kernel and the independent kernel [nanoda](https://github.com/ammkrn/nanoda_lib).
- **Compute.** All mathematics and Lean work ran on one 8-core desktop CPU without a GPU. A rented CPU server was used only for an (unsuccessful) SAT search and for an exhaustive graph search, both mentioned below.
- **Human involvement.** A human operator set the task, suggested looking for open problems in applied fields, provided the computing resources, and published this repository. The mathematics, the formal proofs, the code and the text were produced by the models.

Attempts that did not produce results in this release: a proof of the uniqueness of crystal components (arXiv:1601.03081; no counterexample up to 10^36), Fonollosa's minimum-modulus conjecture (arXiv:2607.08366; partial results only), a local-search attempt to refute the value W(2;3,28) = 827 conjectured by Ahmed, Kullmann and Snevily (no colouring found), Conjecture 7 of DeLaViña and Waller on the Wiener index (a reduction and an exhaustive check of all connected graphs with at most 11 vertices; an unreviewed proof claim exists on Zenodo), the Fici–Saarela question on abelian squares (partial results only), and the corrected form of Conjecture 20 of Liu, Li, Guo and Song. TxGraffiti Conjecture 3 turned out to have already been disproved in July 2026.

## Versions and citations

We will preserve the public release history of this collection. Corrections and revisions will be recorded as new versions in the [history](history.md), with previously released versions remaining accessible through the git history.

To cite an individual manuscript, use the BibTeX block in its directory.

## License

Apache License 2.0; see [LICENSE](LICENSE). The definitions in `lean/ComparatorChallenges/OEISA100475.lean` and `lean/KOS/NumberTheory/OEIS/A100475.lean` are copied from google-deepmind/formal-conjectures, which is also licensed under Apache 2.0.
