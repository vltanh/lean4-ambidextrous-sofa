# Verification

[Back to the README](../README.md)

```sh
lake exe cache get                                  # Mathlib's compiled files
lake build                                          # the libraries, the Challenge and the Solution
lake env lean scripts/Audit.lean                    # axioms and dependencies
python3 scripts/sync_challenge_defs.py --check      # the Challenge's copy of the definitions
lake env lake comparator --config=comparator.json   # Solution.lean proves Challenge.lean
```

You need [elan](https://github.com/leanprover/elan), network access for Mathlib, and
[bubblewrap](https://github.com/containers/bubblewrap) for Comparator. The toolchain is
`leanprover/lean4:v4.35.0-rc3` ([`lean-toolchain`](../lean-toolchain)), and Mathlib is pinned to its release tag
`v4.35.0-rc3`, with the exact revisions in [`lake-manifest.json`](../lake-manifest.json). Mathlib is the only
dependency: the formalization of Baek's theorem is a copy in
[`MovingSofaOptimality/`](../MovingSofaOptimality/README.md). The project stays on `v4.35.0-rc3` for now, because
Palomar cannot yet render a Challenge built with `v4.35.0-rc4`
([PalomarSubmission#161](https://github.com/PalomarRegistry/PalomarSubmission/issues/161)).

`lake build` must succeed, and its only `sorry` warnings are the nine of [`Challenge.lean`](../Challenge.lean),
whose theorems are the statements of record.

[`scripts/Audit.lean`](../scripts/Audit.lean) collects the axioms of every declaration of the library (5,545,
private and auxiliary ones included), of the copied `MovingSofaOptimality` (4,235), and of the nine theorems
that Comparator checks. It fails unless each one uses only
[`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext),
[`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and
[`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound). An unproved
lemma would add `sorryAx`, and `native_decide`, which trusts the compiler, would add `Lean.ofReduceBool`. For the
main results and the main steps of the proof, the audit also prints the results from the literature that their
proofs use. The optimality and the uniqueness use Baek's theorem, `MovingSofaOptimality.gm_area_le`, and the
bound on the area of Gerver's sofa, `MovingSofaOptimality.gerverSofa_area_mem`, through the bound 2.2199 for the
ordinary problem. The audit reaches the proofs through one `import all` line per module, since the module
system hides proofs from a plain import, and CI checks that these lines name exactly the modules of the two
libraries.

`scripts/sync_challenge_defs.py --check` checks that [`Challenge.lean`](../Challenge.lean) copies the marked block
of definitions of [`AmbidextrousSofa/ChallengeDefs.lean`](../AmbidextrousSofa/ChallengeDefs.lean) word for word
(without `--check`, it makes the copy). The Challenge may import only Mathlib, and Comparator compares constants
by name, so the Solution states its theorems with the constants of `ChallengeDefs`.

[`scripts/check_numeric_estimates.py`](../scripts/check_numeric_estimates.py) independently checks the revised
scalar estimates using exact fractions: the shared triangle tilt payment, whole-score
parameter comparison, generated endpoints and clipping checks; generated reference-root and diagonal-offset enclosures,
geometric short-width comparisons, the exact wide demand, weighted triangle prices and tilt cancellation, the intermediate tilt comparison at height one third, horizontal stopping and dry-endpoint area bounds,
uniform tilt cancellation, joint stopping comparisons for every reflected height,
circle discriminants, the intrinsic terminal circle gap and its direct cubic payment,
the reflected angular deadline and cubic payment, the natural initial-angle and terminal-corner widths, complementary tent gap,
the energy-balance height, its radius width and two floor-energy endpoint checks, the common small-height pressure budget
and circle-radius payment, integrated leakage allowance and radius-derived projection prices, and small-tilt and folded-wing endpoint comparisons.
It also audits all active proof and manuscript
files for large literal rational coefficients. Run it with `python3 scripts/check_numeric_estimates.py`.

## Comparator

Lake's Comparator checks, in a sandbox, that [`Solution.lean`](../Solution.lean) proves exactly the statements of
[`Challenge.lean`](../Challenge.lean), over identical definitions and with the three standard axioms only. It
replays the proofs through Lean's kernel and the NanoDa kernel, and ends with `Your solution is okay!`.

## Palomar

[`formalization.yaml`](../formalization.yaml) describes the formalization for the
[Palomar](https://palomar-registry.org) registry: its sources, its scope, how it was made, how it reads the
problem, and the nine theorems that Comparator checks. Earlier checks of Palomar's verifier
([PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission)), run on a fresh clone, accepted the
metadata and the then-current 512 Lean files. The pins of [`lake-manifest.json`](../lake-manifest.json) agree with Mathlib's
own, as the verifier requires, and with those of Verso, which renders the Challenge.

[`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml) runs Palomar's complete
mechanical verification of a commit, as Palomar does after a submission, and uploads its report as the artifact
`mechanical-report-preflight001`. It runs only on demand
(`gh workflow run palomar_preflight.yml --ref main`), since a run can take hours, and it is pinned to
PalomarSubmission commit `d4e41c1`.

## Continuous integration

[`.github/workflows/lean_action_ci.yml`](../.github/workflows/lean_action_ci.yml) builds the project on every push
and pull request. It checks that the axiom audit imports every module of the two libraries, runs the audit and
the check of the Challenge's definitions, and checks the Markdown tables of the documentation.

## The figures

[`scripts/figures/make_figures.py`](../scripts/figures/make_figures.py) draws the figures of
[`docs/figures/`](figures) from the definitions of the Challenge ([`scripts/figures/romik.py`](../scripts/figures/romik.py)).
It computes the support function, the hull, the niche and the sofa, checks that the computed sofa has area `M`
up to the discretization, and checks that it stays inside the hallway at every sampled angle of the turn and in
every frame of the animation. It needs Python with NumPy, Matplotlib and Pillow.
