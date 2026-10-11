# Credits

[Back to the README](../README.md)

How this formalization was made, from the run log and the session transcripts. Times are US Central Time
(UTC−5). The figures come from the Claude Code session transcripts, computed with the formalize-math-paper
skill's `session_stats.py`. They leave out the work of ChatGPT Pro 6, which was not recorded.

## Who

The-Anh Vu-Le, the author and maintainer, asked for the research, the formalization and its documentation, and
decided the scope and the publication.

ChatGPT Pro 6 (OpenAI) found the proof. From 8 to 10 October 2026 it wrote research notes on the ambidextrous
sofa in lean4-moving-sofa (pull request #3), ending with a manuscript ([archive](archive/README.md)). On 10
October it wrote an uncompiled Lean draft of the proof in 13 commits of this repository's pull request #1 (from
`4f2a3f6` to `a609db1`): 514 modules, 51 of them copies of lean4-moving-sofa's formalization of Baek's paper,
about 132,000 lines in all.

Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), in Claude Code 2.1.296, did the rest in one session,
following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill (its version of
7 October 2026) for an existing uncompiled draft. It made the draft compile, wrote the Challenge, the Solution
and the audit script, had the statements reviewed, wrote the documentation and the figures, and moved the
project to a newer Mathlib. In a second session, on 10 and 11 October, it simplified the proof, added a ninth
statement of record, and expanded the review of prior work.

No person has reviewed the proofs or the statements; Lean's kernel checks every proof. An agent separate from
their writer checked every definition and theorem of the Challenge against the research notes and Romik's paper,
and another summarized every module ([layout](layout.md)).

## Making the draft compile (10 October 2026)

The owner asked to make pull request #1 compile, to commit and push, and to document it as lean4-moving-sofa
is.

- 15:27 to 16:00. The draft's copy of lean4-moving-sofa's library was replaced by a dependency on
  lean4-moving-sofa at commit `1174c5c`, identical except for three private helpers, which
  [`Analysis/SurfaceAreaFacts.lean`](../AmbidextrousSofa/Analysis/SurfaceAreaFacts.lean) proves again. Every
  file was converted to Lean's module system. Then every statement and definition was brought to elaborate,
  with every proof replaced by `sorry`, in the order of the imports. In 14 passes over the import graph, which
  is 80 modules deep, the errors that stopped the statements were fixed by hand: missing notations and
  imports, the identifier `λ`, definitions shadowed by theorems of the same name, dot notation on subtypes and
  on local notations, and the decidability of filters. Commit `b79f017`.
- 16:00 to 16:53. Each of the draft's proofs was checked against the elaborated statements, and the 849 that
  failed were replaced by `sorry`. Forty-two sub-agents, each owning a group of about twenty, restored them from
  the draft by repairing tactics and names. The causes were Mathlib lemmas renamed since the draft
  (`add_le_add_left` and `add_le_add_right` have exchanged meanings, `notMem`, `fst_nhds`, …), rewrites and simp
  sets that no longer match, implicit arguments, coercions, and elaboration timeouts. None changed an argument or
  raised `maxHeartbeats`. Seventy-seven theorems in sections with `variable` hypotheses had lost hypotheses that
  their proofs and the draft's callers use, because Lean leaves out of a statement the section variables that it
  does not mention, and some were false as compiled. A script that compared the draft's proofs with their
  statements found them, and `include` put the hypotheses back. Each agent checked its files against a snapshot
  of every module's statements, rebuilt when statements changed, and the coordinating agent checked every
  group's statements against the draft before integrating it.
- Meanwhile, the Challenge (with its definitions in Mathlib's vocabulary), the bridge to the library and the
  Solution were written. An independent agent reviewed them against the research notes and Romik's paper and
  found no error. Its corrections of the Challenge's documentation were made, and two theorems were added: the
  convex hull of Romik's sofa, and its rotated and translated copies. Another agent summarized the 466 modules.
- 16:53 to 17:08. `lake build` succeeded (9,481 jobs, 8 minutes) with no `sorry` outside the Challenge, the audit
  found only the three standard axioms in the 7,474 declarations of the library, and Comparator accepted the
  Solution. Commits `d3d749c` and `49fa0d0`, pushed to pull request #1.

Figures, from 15:27 to 17:08:

- elapsed time: 1 hour 41 minutes;
- sub-agents: 44 (42 repairing proofs, one reviewing the statements, one summarizing the modules), at most 20 at
  once, about 10.0 hours of work;
- tool calls: 3,023 by the sub-agents, 388 by the main session;
- tokens of the sub-agents: 2.20 million output, 8.20 million input, 392 million cache reads; of the main
  session: 0.32 million output, 0.80 million input, 157 million cache reads;
- model calls: 2,953 by the sub-agents and 360 by the main session, all to `claude-opus-5-5`.

## The repository and its documentation (10 October 2026)

The owner asked to make the repository public, to merge pull request #1, to move the research of
lean4-moving-sofa's pull request #3 here, keeping only its final manuscript, to point lean4-moving-sofa to this
repository, and for a README with figures in the manner of lean4-moving-sofa's. When Palomar's check found no
`formalization.yaml`, they asked for the metadata as well.

- Pull request #1 was merged into `main`. The manuscript was archived in [`docs/archive/`](archive); the research
  notes stay in lean4-moving-sofa's history, and its README points here.
- The figures were drawn from the definitions of the Challenge ([`scripts/figures/`](../scripts/figures)), with
  checks that the computed sofa has area `M` and stays inside the hallways. The main session wrote the README and
  the pages of `docs/`.
- The Palomar metadata, [`formalization.yaml`](../formalization.yaml), was written from the run log and the
  review of the statements, and checked with the metadata, source and dependency checks of Palomar's verifier
  (PalomarSubmission at commit `d4e41c1`) on a fresh clone.

Figures, from 17:08 to 17:43:

- elapsed time: 35 minutes;
- sub-agents: none;
- tool calls: 126 by the main session;
- tokens: 0.15 million output, 0.29 million input, 76 million cache reads;
- model calls: 128, all to `claude-opus-5-5`.

## A newer Mathlib, and plainer documentation (10 October 2026)

The owner asked to move to a newer Mathlib without keeping up with lean4-moving-sofa, to present this
formalization as the proof itself, with the manuscript kept only as provenance, and to write the documentation
in plainer language.

- Lean and Mathlib went from `v4.35.0-rc3` to `v4.35.0-rc4`. lean4-moving-sofa at commit `1174c5c` does not
  compile with the newer Mathlib, so its library `MovingSofaOptimality`, which the proof uses, was copied into
  the repository ([`MovingSofaOptimality/`](../MovingSofaOptimality/README.md)), and the Lake dependency was
  removed. The copy needed one more import, and the library one change: `Integrable.piecewise` now takes a
  null-measurable set. The build succeeded (9,542 jobs), the audit now also checks the 4,235 declarations of
  the copy, and Comparator accepted the Solution.
- The README, the pages of `docs/` and `formalization.yaml` were rewritten in plainer language, presenting the
  formalization as the proof, with the manuscript as provenance.

Figures, from 17:43 to 18:02:

- elapsed time: 19 minutes;
- sub-agents: none;
- tool calls: 103 by the main session;
- tokens: 0.12 million output, 0.20 million input, 26 million cache reads;
- model calls: 94, all to `claude-opus-5-5`.

## Back to Mathlib v4.35.0-rc3, and Palomar's preflight (10 October 2026)

The owner submitted `a22fcc4` to Palomar. Its mechanical verification passed, but the rendering of the
Challenge failed twice. A local reproduction showed why: on `v4.35.0-rc4`, Verso's `verso-literate` loads the
Challenge's imports at the private level, while Lake hands it only their public data, so it stops with "missing
data file for module Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan". Given the private data, it renders
the Challenge. Palomar's issue [#161](https://github.com/PalomarRegistry/PalomarSubmission/issues/161) reports the
same failure for every `v4.35.0-rc4` submission. The owner asked to go back to `v4.35.0-rc3` and to add Palomar's
preflight.

- Lean and Mathlib went back to `v4.35.0-rc3`, with the manifest of `cb4b3ed` less lean4-moving-sofa. The copy of
  `MovingSofaOptimality` is again identical to lean4-moving-sofa's, and the change to `Value.lean` was undone.
  The build, the audit and Comparator passed, and the Challenge rendered locally with Verso's `v4.35.0-rc3`.
- [`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml) runs Palomar's complete
  mechanical verification on demand, pinned to PalomarSubmission commit `d4e41c1`.

Figures, from 18:50 to 20:13:

- elapsed time: 1 hour 23 minutes, much of it waiting for builds;
- sub-agents: none;
- tool calls: 67 by the main session;
- tokens: 0.06 million output, 0.11 million input, 35 million cache reads;
- model calls: 75, all to `claude-opus-5-5`.

## Simplifying the proof (10 and 11 October 2026)

The owner asked to simplify the Lean proof greatly, and during the work for a deeper review of prior work and
for the quarter turns of an optimal sofa to be stated.

- Dead code. A Lean script followed the dependencies of the theorems of the Solution: 395 declarations that no
  main theorem used, and three modules left empty, were removed (commit `4f86267`).
- File by file. The library was split into 43 groups of about 2,000 lines, and a sub-agent rewrote each group
  for shorter proofs. A check script elaborated each file against the build and compared every declaration
  that other modules use with its original form (statement, definition body, `rfl` proof), so the groups could
  be rewritten at the same time. The run was paused for two hours at the owner's request; afterwards the files
  of the 16 groups then in progress were checked one by one, and the unfinished ones went to 7 new groups. The
  library went from 88,974 to 60,904 lines, and its 622 warnings to none (`663cf81`). A second pass removed
  what the shorter proofs no longer used (`9e47ce9`), and the docstrings lost the labels and status notes of
  the draft (`308f2cf`).
- Family by family. Twelve sub-agents then worked in separate git worktrees, each on a family of related
  modules, with the statements that other families use held fixed. They merged the arguments that the draft
  proved twice, such as the full-turn and partial-turn versions of the same estimate, in the scalar
  exclusions, the graph fluxes, the curvature estimates, the selected polygons, the terminal facet, and the
  tilted, first-unit, joint-source, partial, horizontal, adaptive and reference modules. One of them added
  the ninth statement of record, `quarter_turns` (`aa12833` to `15ad0ed`). A last sub-agent merged the facts
  that several families had each proved, replaced wrappers of Mathlib lemmas, and dropped hypotheses that no
  proof used (`49483da` to `7237edb`); a third pass removed what was left unused (`3aee3df`).
- Result. The library has 458 modules, 55,015 lines and 5,581 declarations, against 466, 94,375 and 7,474
  before. The build has no warnings besides the nine `sorry` of the Challenge, the audit finds only the three
  standard axioms, Comparator accepts the Solution with Lean's kernel and with NanoDa, and Palomar's checks
  (PalomarSubmission at commit `d4e41c1`, on a fresh clone) accept the metadata and the 512 Lean files.
- Prior work. Four sub-agents searched the literature on the history of the problem, on computer-assisted
  bounds, on formalizations and on AI-assisted proofs, and a fifth wrote the new [prior work](prior-work.md)
  page from their notes (`51af464`).
- Merge. The work was done on `v4.35.0-rc4`. When it was merged into `main`, which had meanwhile gone back to
  `v4.35.0-rc3` (previous section), two proofs needed the older Mathlib: an integrability step now converts
  `IntegrableOn` to `Integrable` explicitly, and the limit of `tan x / x` is again proved from the derivative of
  `tan`, since `Real.tendsto_tan_div_nhdsNE_zero` is newer than `v4.35.0-rc3`. The build, the audit, Comparator
  and Palomar's checks pass on `v4.35.0-rc3`. At the owner's request the README became shorter and no longer
  recounts how the formalization was made; this page does.

Figures, from 18:26 on 10 October to 05:30 on 11 October, including a pause of 1 hour 49 minutes:

- elapsed time: 11 hours;
- sub-agents: 68 (50 rewriting files, 12 rewriting families of files, one merging across families, five on
  prior work), at most 20 at once, about 63.8 hours of work;
- tool calls: 9,711 by the sub-agents, 337 by the main session;
- tokens of the sub-agents: 16.95 million output, 51.20 million input, 3,013 million cache reads; of the main
  session: 0.33 million output, 1.77 million input, 117 million cache reads;
- model calls: 9,440 by the sub-agents and 290 by the main session, all to `claude-opus-5-5`.
