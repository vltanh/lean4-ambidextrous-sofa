# Lean ambidextrous sofa

A Lean 4 formalization draft of the ambidextrous moving sofa problem.

**Status: uncompiled source work in progress toward F7.** Every declared
theorem has an explicit proof body. The universal cap bounds and the final
unconditional optimality-and-uniqueness theorem still require mathematics
listed in the [roadmap](docs/FORMALIZATION-ROADMAP.md). No project Lean source
has been compiled, no axiom queries have been executed, and no CI is included.

## Mathematical target

Let `Y` be the positive solution of

\[
4Y^3+3Y-1=0,\qquad M=1+4Y^2+\arctan Y.
\]

The target quantifies over every compact connected planar body admitting
both genuine unit-corridor passages from a common incoming orientation. It
asserts area at most `M` and equality exactly for compact sets congruent to
Romik's ambidextrous construction. The two continuous motions may backtrack
and have independent terminal rotations. Uniqueness concerns the actual
compact body, not its motion's time parametrization.

The [written Gate 3 manuscript][manuscript] is the research source. Its Gate
0–3 closure records are reviews within that research session. External
refereeing and Lean kernel verification are separate from those records.

## Completed source layers

| Layer | Actual content in the draft | Main source |
| --- | --- | --- |
| Geometry and integration | Actual compact convex hulls, downward caps, attained concave roofs, support determination, both attached walls, true terminal wall, Tonelli and signed-fiber identities | [CapGeometry](AmbidextrousSofa/Geometry/CapGeometry.lean), [Support](AmbidextrousSofa/Geometry/Support.lean), [CapAssembly](AmbidextrousSofa/Measure/CapAssembly.lean) |
| Original motion reduction | Rigid normalization and area invariance; strip-area exclusions; IVT angular reach despite backtracking; independent effective angles and actual upper/lower hull caps | [MotionReduction](AmbidextrousSofa/Geometry/MotionReduction.lean) |
| Reference realization and feasibility | Reverse support inequalities, exact faces, actual niche-cut physical body, path connectedness, two explicit valid passages, regular closedness | [Realization](AmbidextrousSofa/Reference/Realization.lean), [Body](AmbidextrousSofa/Reference/Body.lean), [Regularity](AmbidextrousSofa/Reference/Regularity.lean) |
| Exact reference attainment | Actual support-area and niche integrals give reference cap score `M/2` and ordinary reference sofa area `M` | [Value](AmbidextrousSofa/Reference/Value.lean) |
| Full-cap optimization | Width coercivity; Hausdorff compactness; actual roof, niche and score continuity; global maximum existence; genuine middle-chord and height saturation | [GlobalCapMaximum](AmbidextrousSofa/Analysis/GlobalCapMaximum.lean) |
| Finite selection and variations | Literal finite min/max source derivatives; floating and axis wall variations; exact support circumscription; uniform dense-grid score approximation; selected polygons converging to any prescribed full maximum | [PolygonExposure](AmbidextrousSofa/Analysis/PolygonExposure.lean), [SelectedSequence](AmbidextrousSofa/Analysis/SelectedSequence.lean) |
| Endpoint geometry | Actual inward cuts and erosions, exact shortened projections, support perturbation bounds, inward pressures, top insertion, and low-middle-height exclusion | [EndpointPressure](AmbidextrousSofa/Analysis/EndpointPressure.lean), [LowHeightMaximizer](AmbidextrousSofa/Analysis/LowHeightMaximizer.lean) |
| Analytic comparison | Two-endpoint Dirichlet coercivity, exact clipped-functional expansion, fixed-trace strictness, Euler boundary formula, reference stationarity, global sharp value `M/2` for arbitrary support pairs of competitive width, and exact equality up to horizontal translation | [AdaptiveFunctional](AmbidextrousSofa/Analysis/AdaptiveFunctional.lean), [AdaptiveGlobalComparison](AmbidextrousSofa/Analysis/AdaptiveGlobalComparison.lean) |
| Geometric equality infrastructure | Exact four-term physical deficit, a.e. partition equality, actual hull recovery and finite-measure regular-closed set recovery | [CapAssembly](AmbidextrousSofa/Measure/CapAssembly.lean), [RegularClosed](AmbidextrousSofa/Topology/RegularClosed.lean) |

All statements in this table refer to source proof bodies, not successful
elaboration or kernel validation.

### Concrete assembled statements

`IsAmbidextrous.original_domain_score_reduction` derives from the original
two-motion predicate either a strict small-area branch or

\[
\operatorname{area}(S)\le P_\alpha(U_S)+P_\gamma(V_S)
\]

for the actual normalized hull caps and independently obtained angles in
`(π/4, π/2]`. The whole terminal wall remains in each proper-angle score.

`Reference.isAmbidextrous_referenceSofa` supplies two actual continuous
corridor passages. `Reference.volumeReal_referenceSofa` proves its ordinary
area equals `M`, and `Reference.capScore_referenceCap` proves the full-angle
reference cap score is `M/2`. These are explicit attainment statements.

`exists_fullCapMaximizer` quantifies over the entire downward-cap domain.
`AngularGrid.exists_selected_sequence` targets any prescribed maximum with
actual finite selected polygons. Neither result presupposes its sharp value.
`IsFullCapMaximizer.middle_endpoints_gt_half_of_affine` proves both middle
endpoint roofs exceed one half after the actual canonical reduction.

`adaptiveFunctional_sub_halfWidth_le_half_M` proves the sharp analytic
comparison for every `QuarterPair` with the natural top traces and total
width at least `8/5`. Its equality theorem gives the reference width and
actual support functions up to a horizontal translation. The geometric
conditions needed to apply it universally remain to be established.

These results do not yet assemble an upper bound `M` for every ambidextrous
body. The remaining curvature/exposure, full and partial sharp bounds, and
equality classifications are substantive obligations.

## Source policy and dependencies

The only permitted foundational axioms are `propext`, `Classical.choice`,
and `Quot.sound`. There are no custom axioms, admissions, `sorry`, `admit`,
native proof shortcuts, or target-shaped certificates replacing a global
mathematical obligation. Classical choice selects objects only after an
existence theorem has been proved.

Mathlib is the sole direct package dependency, pinned to
[`c55e6e786f49471c72fbddbec5415808896aec1e`][mathlib], with Lean
`leanprover/lean4:v4.35.0-rc3`. The pinned Mathlib source is used to inspect
relevant APIs. Package build compatibility remains unchecked.

Four objective-independent convex-body/Stieltjes source modules are adapted
from the [pinned earlier repository][research] under
[Imported](AmbidextrousSofa/Imported/SurfaceArea.lean). Their original license,
source paths, revision and modifications are recorded there. They construct
the actual surface-area measure; they do not import an optimality theorem.
The retained ordinary one-turn bound is still a dependency to discharge.

The entry point [AmbidextrousSofa.lean](AmbidextrousSofa.lean) imports every
implementation module. [AxiomAudit.lean](AxiomAudit.lean) prepares one
`#print axioms` query for every explicitly named declaration. Those queries
have not been run. Actual transitive axiom sets remain unverified.

The Python-only source guard is:

```sh
python3 scripts/check_source_policy.py
```

It checks prohibited tokens, namespace-qualified declaration and audit
coverage, import cycles, package pins and absence of CI configuration. It
does not execute Lean or prove that the files elaborate. The
[source-review record](docs/SOURCE-REVIEW.md) gives the current inventory and
review scope. F7 source closure and eventual kernel verification remain
separate acceptance items.

[manuscript]: https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/GATE3-MANUSCRIPT.md
[research]: https://github.com/vltanh/lean4-moving-sofa/commit/20489723dc8777a82ee70ae60510115dc6f21085
[mathlib]: https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e
