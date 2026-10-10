# Lean ambidextrous sofa

A Lean 4 formalization draft of the ambidextrous moving sofa problem.

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

## What this draft now contains

| Source modules | Completed source content | Boundary of the result |
| --- | --- | --- |
| [ExactConstant](AmbidextrousSofa/ExactConstant.lean) | Existence and uniqueness of the cubic root, `2/7 < Y < 3/10`, switching-angle bounds, and exact identities for `M` | No geometric area is assigned to `M` yet |
| [Plane](AmbidextrousSofa/Geometry/Plane.lean), [Motions](AmbidextrousSofa/Geometry/Motions.lean) | Coordinate rigid motions, Euclidean squared-length preservation, reflected corridors, independent continuous passages | The product norm is not a Euclidean norm; lifting arbitrary proper-isometry paths remains open |
| [Caps](AmbidextrousSofa/Geometry/Caps.lean), [CapGeometry](AmbidextrousSofa/Geometry/CapGeometry.lean), [HullCompact](AmbidextrousSofa/Geometry/HullCompact.lean) | Compactness of the actual convex hull by finite Carathéodory parametrizations; compact downward caps; attained concave roofs; exact fibers; roof measurability | The domain includes subunit height, zero width, facets, and nonsmooth caps |
| [Support](AmbidextrousSofa/Geometry/Support.lean), [Reflection](AmbidextrousSofa/Geometry/Reflection.lean) | Attained continuous supports, separation and support determination, support transformations, exact original connected projection, literal hull recovery from its two caps | No feasible motion of the whole convex hull is inferred |
| [Hallway](AmbidextrousSofa/Geometry/Hallway.lean), [Barriers](AmbidextrousSofa/Geometry/Barriers.lean), [BarrierAnalysis](AmbidextrousSofa/Geometry/BarrierAnalysis.lean) | Genuine frame constraints, support tightening, all-angle swept niches, true terminal first walls, boundedness, lower semicontinuity, and integrability | The proper-terminal wall is kept; its omission is proved only at a full quarter turn |
| [AngularDomain](AmbidextrousSofa/Geometry/AngularDomain.lean) | IVT extraction of every intervening frame despite backtracking; full-turn reach and genuine terminal-angle cases; explicit reflected rigid path | The global wrong-way exclusion and angular-reach dichotomy remain open |
| [Deficit](AmbidextrousSofa/Algebra/Deficit.lean), [Fibers](AmbidextrousSofa/Measure/Fibers.lean), [Partition](AmbidextrousSofa/Measure/Partition.lean) | Tonelli area formulas; positive-part versus signed fibers; integrated partition identity; exact a.e. equality conditions; ordinary missing-envelope area | Signed length is identified with ordinary area only after nonempty fibers are proved |
| [CapScore](AmbidextrousSofa/Measure/CapScore.lean), [CapAssembly](AmbidextrousSofa/Measure/CapAssembly.lean) | Actual cap scores and the elementary width bound; actual-body area bounded by its two cap scores; exact four-term geometric deficit; assembly from independent normalized terminal passages | The universal sharp full-turn and partial-turn cap bounds remain open |
| [Reference/Parameters](AmbidextrousSofa/Reference/Parameters.lean), [Reference/Support](AmbidextrousSofa/Reference/Support.lean), [Reference/Hull](AmbidextrousSofa/Reference/Hull.lean) | Exact cubic-to-trigonometric matching; six phase formulas and curvature identities; globally C¹ support coordinates; explicit nonempty compact convex symmetric half-plane intersection | Reverse support inequalities, physical sofa construction, feasible motions, and exact area attainment remain open |
| [RegularClosed](AmbidextrousSofa/Topology/RegularClosed.lean) | Closed-subset recovery from finite equal measure and regular closedness | Application to the genuine reference physical sofa remains open |

### The assembled geometric result

`volumeReal_le_capScore_sum_of_terminal_passages` starts with two genuine
continuous passages of the same compact connected body in the incoming unit
strip. With normalized initial angle zero and independent correctly directed
terminal angles `α, γ ∈ (0, π/2]`, it proves

\[
\operatorname{area}(S)
\le P_\alpha(U_S)+P_\gamma(V_S),
\]

where `U_S = upperCap (actualHull S)` and
`V_S = upperCap (reflect '' actualHull S)`. Both are the actual hull caps.
No monotonicity of either path, smoothness of the body, or nonempty-fiber
assumption is added: intervening angles come from continuity, and physical
fibers come from the connected original projection. A separate theorem
handles a visited full quarter turn even if the path subsequently reverses.

`actual_cap_four_term_deficit` also proves the exact identity

\[
C-\operatorname{area}(S)
=\bigl(C/2-P_\alpha(U_S)\bigr)
+\bigl(C/2-P_\gamma(V_S)\bigr)
+D_{\rm partition}
+\operatorname{area}(E_{S,\alpha,\gamma}\setminus S).
\]

The partition defect and missing area are genuine geometric quantities.
The identity holds for every real `C`. To use `C = M` to conclude sharp
optimality and uniqueness, the scalar cap bounds and their equality
classification still have to be proved. Those claims are not assumed by
these theorems.

The entry point is [AmbidextrousSofa.lean](AmbidextrousSofa.lean).
The [formalization roadmap](docs/FORMALIZATION-ROADMAP.md) gives the dependency
order and acceptance criteria for extending this draft through all four
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
