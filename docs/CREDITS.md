# Credits

[Back to the README](../README.md)

How this formalization was made, from the run log and the session transcripts. Times are US Central Time (UTC−5).

## Who

- The-Anh Vu-Le, the author and maintainer ("the owner" below), directed the work: the owner asked for the
  research, the formalization and its documentation, and decided the scope and the publication.
- ChatGPT Pro 6 (OpenAI) found the proof and wrote the first Lean draft.
  - From 8 to 10 October 2026 it wrote research notes on the ambidextrous sofa in lean4-moving-sofa (pull request
    #3), ending with a manuscript ([archive](archive/README.md)).
  - On 10 October it wrote the draft, uncompiled, in 13 commits of this repository's pull request #1 (`4f2a3f6` to
    `a609db1`): 514 modules, 51 of them copies of lean4-moving-sofa's library, about 132,000 lines.
- Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), in Claude Code 2.1.296, compiled and simplified the proof in two sessions. The
  first followed the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill (its version of 7
  October 2026) for an existing uncompiled draft; the second, on 10 and 11 October, simplified the proof.
- No person has reviewed the proofs or the statements; Lean's kernel checks every proof.

## Making the draft compile (10 October 2026)

- The owner asked to make pull request #1 compile, to commit and push, and to document it as lean4-moving-sofa is.
- From 15:27 to 16:00 the files were converted to Lean's module system and the statements fixed (commit `b79f017`).
  - The draft's copy of lean4-moving-sofa's library became a dependency on lean4-moving-sofa at commit `1174c5c`,
    identical except for three private helpers, which
    [`Analysis/SurfaceAreaFacts.lean`](../AmbidextrousSofa/Analysis/SurfaceAreaFacts.lean) proves again.
  - With every proof replaced by `sorry`, the statements and definitions were brought to elaborate in import order,
    in 14 passes over an import graph 80 modules deep. The errors, fixed by hand, were missing notations and
    imports, the identifier `λ`, definitions shadowed by theorems of the same name, dot notation on subtypes and on
    local notations, and the decidability of filters.
- From 16:00 to 16:53 the proofs were restored.
  - The 849 proofs of the draft that failed against the elaborated statements were replaced by `sorry`, and 42
    sub-agents, each owning a group of about twenty, restored them from the draft by repairing tactics and names.
  - The causes were Mathlib lemmas renamed since the draft (`add_le_add_left` and `add_le_add_right` have exchanged
    meanings, `notMem`, `fst_nhds`, …), rewrites and simp sets that no longer match, implicit arguments, coercions,
    and elaboration timeouts. No repair changed an argument or raised `maxHeartbeats`.
  - 77 theorems in sections with `variable` hypotheses had lost hypotheses that their proofs and the draft's
    callers use, since Lean leaves out of a statement the section variables it does not mention; some were false as
    compiled. A script comparing the draft's proofs with their statements found them; `include` put the hypotheses
    back.
  - Each agent checked its files against a snapshot of every module's statements, rebuilding when statements
    changed, and the coordinating agent checked each group's statements against the draft before integrating it.
- Meanwhile, the Challenge (with its definitions in Mathlib's vocabulary), the bridge to the library and the
  Solution were written. An agent separate from their writer checked every definition and theorem of the Challenge
  against the research notes and Romik's paper, and found no error.
  - Its corrections of the Challenge's documentation were made, and two theorems were added: the convex hull of
    Romik's sofa, and its rotated and translated copies.
  - Another agent summarized the 466 modules ([layout](layout.md)).
- From 16:53 to 17:08 `lake build` succeeded (9,481 jobs, 8 minutes) with no `sorry` outside the Challenge, the
  audit found only the three standard axioms in the 7,474 declarations of the library, and Comparator accepted the
  Solution (commits `d3d749c` and `49fa0d0`, pushed to pull request #1).

## The repository and its documentation (10 October 2026)

- The owner asked to make the repository public and merge pull request #1, to move here only the final manuscript
  of the research in lean4-moving-sofa's pull request #3, and for a README with figures like lean4-moving-sofa's.
- Pull request #1 was merged into `main` (`45d5ef5`). The manuscript was archived in [`docs/archive/`](archive),
  and the main session wrote the README and the pages of `docs/` (`a0595b1`); the research notes stay in
  lean4-moving-sofa's history, and its README points here.
- The figures were drawn from the definitions of the Challenge ([`scripts/figures/`](../scripts/figures)), with
  checks that the computed sofa has area `M` and stays inside the hallways.
- When Palomar's check found no metadata, the owner asked for it. [`formalization.yaml`](../formalization.yaml) was
  written from the run log and the review of the statements, and passed the metadata, source and dependency checks
  of Palomar's verifier (PalomarSubmission at commit `d4e41c1`) on a fresh clone (`cb4b3ed`).

## A newer Mathlib, and plainer documentation (10 October 2026)

- The owner asked to move to a newer Mathlib without waiting for lean4-moving-sofa, to present the formalization as
  the proof, with the manuscript only as provenance, and to write the documentation more plainly.
- Lean and Mathlib went from `v4.35.0-rc3` to `v4.35.0-rc4` (commit `5700eae`). lean4-moving-sofa at commit
  `1174c5c` does not compile with it, so its library `MovingSofaOptimality`, which the proof uses, was copied here
  ([`MovingSofaOptimality/`](../MovingSofaOptimality/README.md)), and the Lake dependency was removed.
  - The copy needed one more import, and the library one change: `Integrable.piecewise` now takes a null-measurable
    set.
  - The build succeeded (9,542 jobs), the audit also checks the copy's 4,235 declarations, and Comparator passed.
- In the same commit, the README, the pages of `docs/` and `formalization.yaml` were rewritten as asked.

## Back to Mathlib v4.35.0-rc3, and Palomar's preflight (10 October 2026)

- The owner submitted `a22fcc4` to Palomar. Its mechanical verification passed, but the rendering of the Challenge
  failed twice.
- A local reproduction showed why: on `v4.35.0-rc4`, Verso's `verso-literate` loads the Challenge's imports at the
  private level, while Lake hands it only their public data, so it stops with "missing data file for module
  Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan". Given the private data, it renders the Challenge.
  - Palomar's issue [#161](https://github.com/PalomarRegistry/PalomarSubmission/issues/161) reports the same
    failure for every `v4.35.0-rc4` submission.
- The owner asked to go back to `v4.35.0-rc3` and to add Palomar's preflight.
  - Lean and Mathlib went back to `v4.35.0-rc3` (commit `5bddfb9`), with the manifest of `cb4b3ed` less
    lean4-moving-sofa. The copy of `MovingSofaOptimality` is again identical to lean4-moving-sofa's, and the change
    to `Value.lean` was undone.
  - The build, the audit and Comparator passed, and the Challenge rendered locally with Verso's `v4.35.0-rc3`.
  - [`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml) runs Palomar's complete
    mechanical verification on demand, pinned to PalomarSubmission commit `d4e41c1`.

## Simplifying the proof (10 and 11 October 2026)

- The owner asked to simplify the Lean proof greatly and, during the work, for a deeper review of prior work and
  for the quarter turns of an optimal sofa to be stated.
- A Lean script followed the dependencies of the theorems of the Solution; the 395 declarations that no main
  theorem used, and the three modules this left empty, were removed (commit `4f86267`).
- The library was split into 43 groups of about 2,000 lines, and a sub-agent rewrote each for shorter proofs.
  - A check script elaborated each file against the build and compared every declaration used by other modules with
    its original form (statement, definition body, `rfl` proof), so the groups could be rewritten at the same time.
  - The run was paused for two hours at the owner's request; afterwards the files of the 16 groups then in progress
    were checked one by one, and the unfinished ones went to 7 new groups.
  - The library went from 88,974 to 60,904 lines, and its 622 warnings to none (`663cf81`). A second pass removed
    what became unused (`9e47ce9`), and the docstrings lost the draft's labels and status notes (`308f2cf`).
- Twelve sub-agents then worked in separate git worktrees, each on a family of related modules, with the statements
  that other families use held fixed (`aa12833` to `15ad0ed`).
  - They merged the arguments the draft proved twice, such as full-turn and partial-turn versions of one estimate.
  - One of them added the ninth statement of record, `quarter_turns`.
- A last sub-agent merged facts that several families each proved, replaced wrappers of Mathlib lemmas and dropped
  unused hypotheses (`49483da` to `7237edb`); a third pass removed what was left unused (`3aee3df`).
- The library now has 458 modules, 55,015 lines and 5,581 declarations, against 466, 94,375 and 7,474 before.
  - The only build warnings are the Challenge's nine `sorry`, and the audit finds only the three standard axioms.
  - Comparator accepts the Solution with Lean's kernel and with NanoDa, and Palomar's checks (PalomarSubmission at
    commit `d4e41c1`, on a fresh clone) accept the metadata and the 512 Lean files.
- Four sub-agents searched the literature on the problem's history, computer-assisted bounds, formalizations and
  AI-assisted proofs, and a fifth expanded the [prior-work page](prior-work.md) from their notes (`51af464`).
- The work, done on `v4.35.0-rc4`, was merged into `main`, which had meanwhile gone back to `v4.35.0-rc3`
  (`acaa34e`); the build, the audit, Comparator and Palomar's checks pass there.
  - Two proofs needed the older Mathlib: an integrability step now converts `IntegrableOn` to `Integrable`
    explicitly, and the limit of `tan x / x` is again proved from the derivative of `tan`, since
    `Real.tendsto_tan_div_nhdsNE_zero` is newer than `v4.35.0-rc3`.
- At the owner's request the README was shortened and no longer tells how the work was done; this page does.

## The paper (11 October 2026)

- The owner asked for a paper like lean4-moving-sofa's, then for a simple first draft as Claude's credit ran low.
- Claude Opus 5.5 prepared the LaTeX scaffold, bibliography, six figures, and notation and caption notes. Its session reached the weekly usage limit before writing the sections.
- Codex, based on GPT-6, recovered those notes and first completed a 27-page outline. The owner then asked for the complete pen-and-paper proof and for the reference paper's structure, especially its introduction and appendices.
- The resulting [107-page paper](paper/main.pdf) has eleven main sections, separate optimality and uniqueness strategies, an organization subsection, and eight mathematical appendices. The [source and build instructions](paper/README.md) and [review record](paper/REVIEW.md) accompany it.
- Three sub-agents worked on the cap argument, selection and variations, and terminal-angle estimates. Each reviewed sections written by another; the coordinating agent wrote the introduction, setting, reduction, reference construction, preliminary estimates, and body recovery, and integrated the reviews. At most three sub-agents ran at once.
- The first round's recorded clock readings run from 08:52 CDT to about 09:07 CDT. The rewrite finished at 09:51 CDT; its exact starting time was not recorded. Exact model variant, token totals, sub-agent working times, and costs were not available and are not estimated.
- The initial round checked the existing proof library and figures. The revised PDF passes reference, bibliography, and overflow checks; its 31-entry source archive compiles separately with `pdflatex` alone. Representative pages were inspected visually.
- The reviews found no unresolved substantive mathematical error. The proof library and archived research manuscript are unchanged; human mathematical review remains outstanding.

## Figures

From the Claude Code session transcripts, computed with the formalize-math-paper skill's `session_stats.py`; the
work of ChatGPT Pro 6 was not recorded and is left out. Tokens are in millions, and every model call went to
`claude-opus-5-5`.

| Round | Time (10 October) | Elapsed | By | Tool calls | Model calls | Output tokens | Input tokens | Cache reads |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Making the draft compile | 15:27 to 17:08 | 1 h 41 min | main session | 388 | 360 | 0.32 | 0.80 | 157 |
| | | | 44 sub-agents | 3,023 | 2,953 | 2.20 | 8.20 | 392 |
| The repository and its documentation | 17:08 to 17:43 | 35 min | main session | 126 | 128 | 0.15 | 0.29 | 76 |
| A newer Mathlib | 17:43 to 18:02 | 19 min | main session | 103 | 94 | 0.12 | 0.20 | 26 |
| Back to v4.35.0-rc3 | 18:50 to 20:13 | 1 h 23 min, much of it waiting for builds | main session | 67 | 75 | 0.06 | 0.11 | 35 |
| Simplifying the proof | 18:26 to 05:30 (11 October) | 11 h, with a pause of 1 h 49 min | main session | 337 | 290 | 0.33 | 1.77 | 117 |
| | | | 68 sub-agents | 9,711 | 9,440 | 16.95 | 51.20 | 3,013 |

- The middle three rounds used no sub-agents; at most 20 ran at once in the others.
- In the first round, 42 sub-agents repaired proofs, one reviewed the statements and one summarized the modules,
  for about 10.0 hours of work.
- In the simplification, 50 sub-agents rewrote files, 12 rewrote families of files, one merged across families and
  five worked on prior work, for about 63.8 hours of work.
