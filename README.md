# Lean ambidextrous sofa

An initial Lean 4 formalization of the ambidextrous moving sofa problem.

**Status: uncompiled draft.** Every theorem currently declared has a complete
source proof body. The full optimality and uniqueness theorem is **not yet
formalized**. No Lean, Lake, language server, compilation, or CI has been run
for this draft, and no CI workflow is included.

## The mathematical target

Let `Y` be the positive solution of

\[
4Y^3+3Y-1=0,
\qquad M=1+4Y^2+\arctan Y.
\]

The target is that every compact connected planar body admitting passages
through both unit-width right-angle corridors, from a common incoming
orientation, has area at most `M`, with equality exactly for bodies congruent
to Romik's ambidextrous construction. The two paths may backtrack and have
independent terminal rotations. Uniqueness concerns the physical compact
set up to congruence; it does not concern the time parametrization of a motion.

The [Gate 3 research manuscript][manuscript] presents a complete written
argument for this claim, following the written Gate 0–3 closures. Those
closures record separate reviews within the research session. External
refereeing and Lean kernel verification remain outstanding. Its ordinary
one-turn theorem and Gerver-area enclosure are explicit external inputs;
they will also need fully proved formal dependencies.

## What this draft contains

| Module | Completed source content | Boundary of the result |
| --- | --- | --- |
| [ExactConstant](AmbidextrousSofa/ExactConstant.lean) | Existence and uniqueness of the cubic root, `2/7 < Y < 3/10`, switching-angle bounds, and exact identities for `M` | No geometric area is assigned to `M` yet |
| [Geometry/Plane](AmbidextrousSofa/Geometry/Plane.lean) | Coordinate rotations, Euclidean squared-length preservation, and the two reflected corridors | The product norm is not used as a Euclidean metric |
| [Geometry/Motions](AmbidextrousSofa/Geometry/Motions.lean) | Independent continuous two-passage domain and inheritance by compact connected subsets | Angle lifting from arbitrary proper isometry paths remains to be proved |
| [Geometry/Caps](AmbidextrousSofa/Geometry/Caps.lean) | Actual convex hulls, broad downward caps, exact projection and downward-filling identities | No normalization to full height or special contact chart is assumed |
| [Algebra/Deficit](AmbidextrousSofa/Algebra/Deficit.lean) | Signed four-wall fibers, exact partition defects, four-term arithmetic deficit, and extrusion identity | Identifying geometric integrals and proving sharp cap bounds remain separate tasks |
| [Topology/RegularClosed](AmbidextrousSofa/Topology/RegularClosed.lean) | Closed-subset recovery from finite equal measure and regular closedness | The reference body's geometry and regular closedness remain to be constructed |

The entry point is [AmbidextrousSofa.lean](AmbidextrousSofa.lean).
The [formalization roadmap](docs/FORMALIZATION-ROADMAP.md) gives the dependency
order and acceptance criteria for extending this foundation through all four
written gates. The [source-review record](docs/SOURCE-REVIEW.md) describes the
checks actually performed.

## Trust policy

- The permitted foundational axioms are `propext`, `Classical.choice`, and
  `Quot.sound`; a theorem may use a subset of these.
- No new axioms, admissions, `sorry`, `admit`, or native proof shortcuts are
  allowed. `Y` uses classical choice from a proved existence theorem.
- Unfinished mathematics is documented in the roadmap, without placeholder
  theorems or assumptions that encode the headline result.
- The project imports Mathlib and its own modules. It does not import the
  earlier research repository or its unfinished challenge modules.
- [AxiomAudit.lean](AxiomAudit.lean) contains `#print axioms` queries for every
  explicitly named declaration in the project modules. **It has not been
  executed.** Actual transitive dependencies remain to be checked by Lean.

The source-only checker can be run with:

```sh
python3 scripts/check_source_policy.py
```

It checks prohibited source constructs, import closure, declaration coverage
in the future audit, dependency pins, and absence of CI configuration. It
does not elaborate Lean, establish theorem correctness, or compute kernel
axiom dependencies.

## Reproducible dependency pins

- Lean: `leanprover/lean4:v4.35.0-rc3`.
- Mathlib: [`c55e6e786f49471c72fbddbec5415808896aec1e`][mathlib].
- The lockfile's transitive revisions were copied from Mathlib's own manifest
  at that exact commit; the root package entry was assembled without Lake.

The versions and relevant declaration signatures were read through the GitHub
API. Dependencies were not installed and build compatibility has not been
tested. Compilation and the prepared axiom audit are explicitly deferred to
a later, separately requested verification pass. There is no CI setup.

[manuscript]: https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/GATE3-MANUSCRIPT.md
[mathlib]: https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e
