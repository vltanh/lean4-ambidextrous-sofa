# Archive: the manuscript

[Back to the README](../../README.md)

[`GATE3-MANUSCRIPT.md`](GATE3-MANUSCRIPT.md) is the manuscript that this repository formalizes:
*Sharp area and exact uniqueness for the ambidextrous moving sofa problem* (18,087 lines of Markdown with
LaTeX). It is kept here unchanged, and it is the only document kept from the research that produced it.

- **Origin.** ChatGPT Pro 6 (OpenAI) wrote it at the request of The-Anh Vu-Le, in research sessions from
  8 to 10 October 2026, in the branch `research/ambidextrous-pen-and-paper` of
  [lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa) (pull request
  [#3](https://github.com/vltanh/lean4-moving-sofa/pull/3)). The file is
  `docs/ambidextrous/GATE3-MANUSCRIPT.md` at the branch's last commit,
  [`2048972`](https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/GATE3-MANUSCRIPT.md)
  (10 October 2026), which the Lean draft cites. The branch, its 168 commits and the research notes before
  the manuscript (about 500 files: numbered notes, gate reviews, numerical checkers, a builder script and
  manifest for the manuscript) remain in lean4-moving-sofa's history at that commit; links inside the
  manuscript to those notes point there, pinned to commits.
- **Status.** The manuscript has not been refereed, and no person has checked it. Its main theorem
  (MS.3, Theorem G3C2) is now a theorem of Lean: [`Challenge.lean`](../../Challenge.lean) states it, and
  [`Solution.lean`](../../Solution.lean) proves it, checked by Lean's kernel. The formal proofs follow
  ChatGPT Pro 6's Lean draft of the manuscript's argument, not its text line by line.
- **Numbering.** Equations and results keep the manuscript's labels: MS.1 to MS.18 in Chapter 1, G3C.1
  to G3C.3 in Chapter 5, and two-letter codes (AF, SR, LH, TW, …) in the technical proofs that follow
  Chapter 5. [docs/layout.md](../layout.md) maps the Lean modules to its sections.
