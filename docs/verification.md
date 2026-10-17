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

[`scripts/check_numeric_estimates.py`](../scripts/check_numeric_estimates.py) checks the scalar estimates of the
proof with exact fractions, independently of Lean. Run it with `python3 scripts/check_numeric_estimates.py`.

- Enclosures: the generated reference enclosures, two Newton width endpoints, and the energy-balance height with
  its radius width and its two floor-energy endpoints.
- Widths and areas: the geometric short-width margins, the initial-angle and terminal-corner widths, the
  complementary tent gap, the exact wide demand with weighted triangle prices and tilt cancellation, the
  intermediate height bound one third, the common triangle tilt payment and Newton corners, and the folded-wing
  endpoint comparisons.
- Stopping and circles: horizontal stopping and dry-endpoint area bounds, uniform tilt cancellation and joint
  stopping comparisons, the terminal-circle gap and its cubic price, two circle discriminants, the angular deadline
  and its cubic payment, and the small-tilt pressure budget and circle-radius payment.
- It also checks that none of the proof and manuscript files keeps a large literal fraction.

## Comparator

Lake's Comparator checks, in a sandbox, that [`Solution.lean`](../Solution.lean) proves exactly the statements of
[`Challenge.lean`](../Challenge.lean), over identical definitions and with the three standard axioms only. It
replays the proofs through Lean's kernel and the NanoDa kernel, and ends with `Your solution is okay!`.

## Palomar

- [PALOMAR-2026-10-13-000003](https://palomar-registry.org/entry?id=PALOMAR-2026-10-13-000003) is the entry of
  this repository in the [Palomar](https://palomar-registry.org) registry. Its version 1, from commit `0f24fe4`, was
  registered on 13 October 2026 (UTC).
  - Palomar's verifier built that commit and ran Comparator on the nine theorems of the Challenge with the NanoDa
    and con-ron kernels, allowing only `propext`, `Quot.sound` and `Classical.choice`
    ([run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/38256912846)).
  - The registry rates its trust as high: the Challenge has 270 lines and imports only Mathlib. Palomar's review
    of the metadata raised no warning.
  - Palomar archives the repository and its dependencies at the registered commits.
- [`formalization.yaml`](../formalization.yaml) is the entry's metadata: its sources, its scope, how it was made,
  how it reads the problem, and the nine theorems that Comparator checks. The pins of
  [`lake-manifest.json`](../lake-manifest.json) agree with Mathlib's own, as the verifier requires, and with those of
  Verso, which renders the Challenge.
- A change to the Challenge, the Solution or the metadata reaches the registry only as a new version of the entry.
- [`.github/workflows/palomar_preflight.yml`](../.github/workflows/palomar_preflight.yml) runs Palomar's complete
  mechanical verification of a commit, pinned to PalomarSubmission commit `d4e41c1`, the one that verified version
  1, and uploads its report as the artifact `mechanical-report-preflight001`. It runs only on demand
  (`gh workflow run palomar_preflight.yml --ref main`), since a run can take hours.

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
