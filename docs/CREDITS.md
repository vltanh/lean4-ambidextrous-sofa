# Credits

[Back to the README](../README.md)

How this formalization was made, from the run log and the session transcripts. Times are US Central Time
(UTC−5). The figures come from the Claude Code session transcripts, computed with the formalize-math-paper
skill's `session_stats.py`; they do not include the work of ChatGPT Pro 6, which was not recorded.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the research, the formalization and its
  documentation, and decided the scope and the publication.
- **The manuscript and the Lean draft:** ChatGPT Pro 6 (OpenAI). From 8 to 10 October 2026 it wrote the research
  notes on the ambidextrous sofa in lean4-moving-sofa (pull request #3), ending with the manuscript
  ([archive](archive/README.md)), and on 10 October an uncompiled Lean draft of its proof, in 13 commits of this
  repository's pull request #1 (from `4f2a3f6` to `a609db1`): 514 modules, of which 51 were copies of
  lean4-moving-sofa's formalization of Baek's paper, about 132,000 lines in all, never compiled.
- **The formalization:** Claude Opus 5.5 (Anthropic, model `claude-opus-5-5`), in Claude Code 2.1.296, in one
  session: it made the draft compile, wrote the Challenge, the Solution and the audit script, had the
  statements reviewed, and wrote the documentation and the figures.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill (its version
  of 7 October 2026), for an existing uncompiled draft.
- **Review:** no person has reviewed the proofs, the statements or the manuscript; Lean's kernel checks every
  proof. An agent independent of their writer checked every definition and theorem of the Challenge
  against the manuscript and against Romik's paper, and another mapped the modules to the sections of the
  manuscript ([layout](layout.md)).

## Making the draft compile (10 October 2026)

The owner asked to make pull request #1 compile, to commit and push, and to document it as lean4-moving-sofa
is.

How it was made:
- 15:27 to 16:00: the draft's copy of lean4-moving-sofa's library was replaced by a dependency on
  lean4-moving-sofa at commit `1174c5c`, identical but for three private helpers, which
  [`Analysis/SurfaceAreaFacts.lean`](../AmbidextrousSofa/Analysis/SurfaceAreaFacts.lean) proves again. Every
  file was converted to Lean's module system. Then every statement and definition was brought to
  elaborate, with every proof replaced by `sorry`, in the order of the imports: in 14 passes over the
  80-module-deep import graph, the errors that stopped the statements were fixed by hand (missing notations
  and imports, the identifier `λ`, definitions shadowed by theorems of the same name, dot notation on
  subtypes and on local notations, decidability of filters). Commit `b79f017`.
- 16:00 to 16:53: each of the draft's proofs was checked against the elaborated statements, and the 849 that
  failed were replaced by `sorry`. Forty-two sub-agents, each owning a group of about twenty of them, restored
  them from the draft, repairing tactics and names: Mathlib lemmas renamed since the draft
  (`add_le_add_left` and `add_le_add_right` have exchanged meanings, `notMem`, `fst_nhds`, …), rewrites and
  simp sets that no longer match, implicit arguments, coercions, and elaboration timeouts. None changed an
  argument or raised `maxHeartbeats`. Seventy-seven theorems, in sections with `variable` hypotheses, lacked
  hypotheses that their proofs and the draft's callers use, because Lean leaves out of a statement the section
  variables that it does not mention; some were false as compiled. A script that compared the draft's proofs
  with their statements found them, and `include` restored them. Each agent checked its files against a snapshot of every module's
  statements, rebuilt when statements changed; the coordinating agent checked every group's statements
  against the draft and integrated it.
- Meanwhile: the Challenge, with its definitions in Mathlib's vocabulary, the bridge to the library and the
  Solution were written; an independent agent reviewed them against the manuscript and Romik's paper and
  found no error, and its corrections of the Challenge's documentation and two more theorems (the convex hull
  of Romik's sofa, and its rotated and translated copies) were added; another agent mapped the 466 modules to
  the manuscript.
- 16:53 to 17:08: `lake build` succeeded (9,481 jobs, 8 minutes), with no `sorry` outside the Challenge; the audit
  found only the three standard axioms in the 7,474 declarations of the library; Comparator accepted the
  Solution. Commits `d3d749c` and `49fa0d0`, pushed to pull request #1.

Figures, from 15:27 to 17:08:
- elapsed time: 1 hour 41 minutes;
- sub-agents: 44 (42 repairing proofs, one reviewing the statements, one mapping the modules), at most 20 at
  once, about 10.0 hours of work;
- tool calls: 3,023 by the sub-agents, 388 by the main session;
- tokens of the sub-agents: 2.20 million output, 8.20 million input, 392 million cache reads; of the main
  session: 0.32 million output, 0.80 million input, 157 million cache reads;
- model calls: 2,953 by the sub-agents and 360 by the main session, all to `claude-opus-5-5`.

## The repository and its documentation (10 October 2026)

The owner asked to make the repository public, to merge pull request #1, to move the research of
lean4-moving-sofa's pull request #3 here, keeping only its final manuscript, to point lean4-moving-sofa to this
repository, and for a README with figures in the manner of lean4-moving-sofa's.

How it was made:
- Pull request #1 was merged into `main`. The manuscript was archived in [`docs/archive/`](archive); the
  research notes stay in lean4-moving-sofa's history, and its README points here.
- The figures were drawn from the definitions of the Challenge
  ([`scripts/figures/`](../scripts/figures)), with checks that the computed sofa has area `M` and stays inside
  the hallways; the README and the pages of `docs/` were written by the main session.
