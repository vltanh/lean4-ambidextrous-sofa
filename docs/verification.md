# Verification

[Back to the README](../README.md)

```sh
lake exe cache get                                  # Mathlib's compiled files
lake build                                          # the library, the Challenge and the Solution
lake env lean scripts/Audit.lean                    # axioms and dependencies
python3 scripts/sync_challenge_defs.py --check      # the Challenge's copy of the definitions
lake env lake comparator --config=comparator.json   # Solution.lean proves Challenge.lean
```

Needs [elan](https://github.com/leanprover/elan), network access for Mathlib and for
[lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa), and
[bubblewrap](https://github.com/containers/bubblewrap) for Comparator. The toolchain is
`leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](../lean-toolchain)); Mathlib is pinned to its release tag
`v4.35.0-rc3`, and lean4-moving-sofa to commit `1174c5c`, with the exact revisions in
[`lake-manifest.json`](../lake-manifest.json). With Mathlib's cache and lean4-moving-sofa's library already
compiled, building the 466 modules of this library took 8 minutes on 20 cores.

- `lake build` must succeed, and its only `sorry` warnings are the eight of
  [`Challenge.lean`](../Challenge.lean), whose theorems are the statements of record.
- [`scripts/Audit.lean`](../scripts/Audit.lean) collects the axioms of every declaration of the library
  (7,474 declarations, private and auxiliary ones included) and of the eight theorems that Comparator checks.
  It fails unless each one uses only [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
  [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and
  [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound): an unproved lemma would add
  `sorryAx`, and `native_decide`, which trusts the compiler, `Lean.ofReduceBool`. It also prints, for the main
  results of the manuscript, the results from the literature that their proofs use: the optimality and
  the uniqueness use Baek's theorem, `MovingSofaOptimality.gm_area_le`, and the bound on the area of
  Gerver's sofa, `MovingSofaOptimality.gerverSofa_area_mem`, through the ordinary bound 2.2199 (MS.18). The
  audit reaches the proofs through one `import all` line per module (the module system hides proofs from a
  plain import), and CI checks that these lines name exactly the modules of the library.
- `scripts/sync_challenge_defs.py --check` checks that [`Challenge.lean`](../Challenge.lean) copies the marked
  block of definitions of [`AmbidextrousSofa/ChallengeDefs.lean`](../AmbidextrousSofa/ChallengeDefs.lean) word for
  word (without `--check`, it copies it). The Challenge may import only Mathlib, and Comparator compares
  constants by name, so the Solution states its theorems with the constants of `ChallengeDefs`.

## Comparator

Lake's Comparator checks in a sandbox that [`Solution.lean`](../Solution.lean) proves exactly the statements of
[`Challenge.lean`](../Challenge.lean), over identical definitions, with the three standard axioms only, and
replays the proofs through Lean's kernel and the NanoDa kernel. It ends with `Your solution is okay!`.

## Continuous integration

[`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) builds the project on every push and
pull request, checks that the axiom audit imports every module of the library, runs the audit and the check
of the Challenge's definitions, and checks the Markdown tables of the README.

## The figures

[`scripts/figures/make_figures.py`](../scripts/figures/make_figures.py) draws the figures of
[`docs/figures/`](figures) from the definitions of the Challenge ([`scripts/figures/romik.py`](../scripts/figures/romik.py)):
it computes the support function, the hull, the niche and the sofa, checks that the computed sofa has area
`M` up to the discretization, and checks that it stays inside the hallway at every sampled angle of the turn
and every frame of the animation. It needs Python with NumPy, Matplotlib and Pillow.
