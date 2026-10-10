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
`leanprover/lean4:v4.35.0-rc4` ([`lean-toolchain`](../lean-toolchain)), and Mathlib is pinned to its release tag
`v4.35.0-rc4`, with the exact revisions in [`lake-manifest.json`](../lake-manifest.json). Mathlib is the only
dependency: the formalization of Baek's theorem is a copy in
[`MovingSofaOptimality/`](../MovingSofaOptimality/README.md).

`lake build` must succeed, and its only `sorry` warnings are the eight of [`Challenge.lean`](../Challenge.lean),
whose theorems are the statements of record.

[`scripts/Audit.lean`](../scripts/Audit.lean) collects the axioms of every declaration of the library (7,474,
private and auxiliary ones included), of the copied `MovingSofaOptimality` (4,235), and of the eight theorems
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

## Comparator

Lake's Comparator checks, in a sandbox, that [`Solution.lean`](../Solution.lean) proves exactly the statements of
[`Challenge.lean`](../Challenge.lean), over identical definitions and with the three standard axioms only. It
replays the proofs through Lean's kernel and the NanoDa kernel, and ends with `Your solution is okay!`.

## Palomar

[`formalization.yaml`](../formalization.yaml) describes the formalization for the
[Palomar](https://palomar-registry.org) registry: its sources, its scope, how it was made, how it reads the
problem, and the eight theorems that Comparator checks. The checks of Palomar's verifier
([PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission)), run on a fresh clone, accept the
metadata and the 520 Lean files. The pins of [`lake-manifest.json`](../lake-manifest.json) agree with Mathlib's
own, as the verifier requires, and with those of Verso, which renders the Challenge.

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
