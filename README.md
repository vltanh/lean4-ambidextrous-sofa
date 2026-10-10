# Optimality and uniqueness of Romik's ambidextrous sofa, in Lean 4

[![Lean Action CI](https://github.com/vltanh/lean4-ambidextrous-sofa/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-ambidextrous-sofa/actions/workflows/lean_action_ci.yml)

The ambidextrous moving sofa problem asks for the largest area of a shape that can be moved around the
right-angled corner of a hallway of unit width that turns right, and also, from the same starting
position, around the corner of a hallway that turns left. Dan Romik (2016) constructed a shape of area

  `1 + 4Y² + arctan Y = ∛(3 + 2√2) + ∛(3 − 2√2) − 1 + arctan(½(∛(√2 + 1) − ∛(√2 − 1))) = 1.64495…`,

where `Y = 0.2980…` is the positive root of `4Y³ + 3Y = 1`, and proposed it as a likely solution. This
repository proves in Lean 4, with Mathlib, that Romik's ambidextrous sofa

- **is optimal**: every ambidextrous sofa has area at most `1 + 4Y² + arctan Y`;
- **is the only optimal shape**: an ambidextrous sofa of that area is the image of Romik's sofa by a
  rotation and a translation.

The proof formalizes the manuscript *Sharp area and exact uniqueness for the ambidextrous moving sofa
problem* (the "Gate 3 manuscript",
[lean4-moving-sofa@2048972, docs/ambidextrous/GATE3-MANUSCRIPT.md](https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/GATE3-MANUSCRIPT.md)).
ChatGPT 6 Pro (OpenAI) wrote the manuscript and an uncompiled Lean draft of this formalization; Claude
Opus 5.5 (Anthropic) made the draft compile. No person has reviewed the manuscript or the proofs; Lean's
kernel checks every proof. The proof uses one result from the literature, Jineon Baek's theorem that
Gerver's sofa is optimal for the ordinary problem (arXiv:2411.19826), through its Lean formalization
[lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa), on which this project depends.

## Statements

[`Challenge.lean`](Challenge.lean) states the results in Mathlib's vocabulary only, with all the
definitions they need: the two hallways, motions, ambidextrous sofas (compact connected sets that move
through both hallways by two continuous rigid motions with the same starting orientation) and Romik's
ambidextrous sofa `referenceSofa Y` (its convex hull, given by an explicit support function, minus the
two regions swept by the hallways' inner corners). Its eight theorems, for `Y` with
`0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1`:

| Theorem | Statement |
| --- | --- |
| `existsUnique_root` | the equation `4Y³ + 3Y = 1` has exactly one positive solution |
| `value_eq_romik` | `1 + 4Y² + arctan Y` is Romik's closed form above |
| `volume_le` | every ambidextrous sofa has area at most `1 + 4Y² + arctan Y` |
| `isAmbidextrous_referenceSofa` | Romik's sofa is an ambidextrous sofa |
| `volume_referenceSofa` | Romik's sofa has area `1 + 4Y² + arctan Y` |
| `isAmbidextrous_image_referenceSofa` | so is every image of it by a rotation and a translation |
| `convexHull_referenceSofa` | its convex hull is the explicit hull `referenceHull Y` |
| `volume_eq_iff` | an ambidextrous sofa has area `1 + 4Y² + arctan Y` iff it is such an image of Romik's sofa |

[`Solution.lean`](Solution.lean) proves them from the library; [`comparator.json`](comparator.json)
configures Comparator to check that it proves exactly the Challenge.

## Layout

```text
Challenge.lean, Solution.lean   the statements of record and their proofs
comparator.json                 Comparator's configuration
AmbidextrousSofa/               the formalization of the manuscript (466 modules)
  ChallengeDefs.lean            the definitions that Challenge.lean copies
  Main.lean                     the main theorems in the Challenge's vocabulary
  Theorems/Optimality.lean      the main theorems in the library's vocabulary
  ExactConstant.lean            the root Y and the value M = 1 + 4Y² + arctan Y
  Geometry/, Measure/, Topology/, Algebra/   the plane, motions, caps, hulls, areas
  Reference/                    Romik's ambidextrous sofa: support function, body, motions, area
  Analysis/                     the cap-score bound and its equality cases
scripts/                        the axiom audit and the tools that CI runs
```

## Building and checking

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean
python3 scripts/sync_challenge_defs.py --check
lake env lake comparator --config=comparator.json
```

Lean and Mathlib are pinned at `v4.35.0-rc3`, and lean4-moving-sofa at commit `1174c5c`.

## License

Apache-2.0 ([`LICENSE`](LICENSE)), as for Mathlib.

## Credits

- The-Anh Vu-Le directed the work.
- ChatGPT 6 Pro (OpenAI) wrote the manuscript and the uncompiled Lean draft (about 92,000 lines in 463
  modules, pull request #1).
- Claude Opus 5.5 (Anthropic), in Claude Code, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill, made the draft compile,
  wrote the Challenge and the Solution, and reviewed the statements against the manuscript.
