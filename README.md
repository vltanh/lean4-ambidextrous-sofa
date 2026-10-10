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
| Finite curvature and endpoint limits | Actual facet atoms, neighboring-wall source bounds, finite curvature concentration, punctured-axis mass estimates, moving pressure convergence and exact limits of finite erosion moments | [DiscreteCurvature](AmbidextrousSofa/Analysis/DiscreteCurvature.lean), [DyadicCurvatureMass](AmbidextrousSofa/Analysis/DyadicCurvatureMass.lean), [SelectedErosionMoments](AmbidextrousSofa/Analysis/SelectedErosionMoments.lean) |
| Actual endpoint stationarity and central niche height | Axis-height limits identified with actual faces, full-maximizer complementarity, strictly positive canonical pressures, vanishing finite erosion moments and the central niche bound `n ≤ (eR+eL)/2` | [EndpointComplementarity](AmbidextrousSofa/Analysis/EndpointComplementarity.lean), [EndpointPositivity](AmbidextrousSofa/Analysis/EndpointPositivity.lean), [SelectedNicheHeight](AmbidextrousSofa/Analysis/SelectedNicheHeight.lean) |
| Actual sharp wing density | Middle-facet mass vanishes away from its normal; moving support secants and finite source bounds give an actual measurable curvature density bounded by `max |q| ((|q|+1)/2)` | [MiddleMassLimit](AmbidextrousSofa/Analysis/MiddleMassLimit.lean), [SharpCurvatureDensity](AmbidextrousSofa/Analysis/SharpCurvatureDensity.lean) |
| Regular support calculus and source occupation | One actual sharp density off the two exceptional normals, support/tangent absolute continuity and coupled velocity equations, literal inner-source interval convergence, and zero curvature at strictly negative corners | [RegularCurvatureDomain](AmbidextrousSofa/Analysis/RegularCurvatureDomain.lean), [SupportDensityCalculus](AmbidextrousSofa/Analysis/SupportDensityCalculus.lean), [SourceOccupation](AmbidextrousSofa/Analysis/SourceOccupation.lean), [NegativeCornerCurvature](AmbidextrousSofa/Analysis/NegativeCornerCurvature.lean) |
| Actual floor-contact curvature | Ordinary level-set derivative nullity, actual corner velocity and acceleration equations, and strict unit density at almost every floor contact | [LevelSetDerivative](AmbidextrousSofa/Analysis/LevelSetDerivative.lean), [CornerDynamics](AmbidextrousSofa/Analysis/CornerDynamics.lean), [FloorContactCurvature](AmbidextrousSofa/Analysis/FloorContactCurvature.lean) |
| Actual Green and wing chord comparison | Exact finite Green identity including top mass and both endpoint defects; vanishing weighted defect; actual selected wing-length limit; Euclidean chord comparison and the stronger ordinary-area constraint | [FiniteGraphGreen](AmbidextrousSofa/Analysis/FiniteGraphGreen.lean), [SelectedGreenLimit](AmbidextrousSofa/Analysis/SelectedGreenLimit.lean), [CanonicalWingChord](AmbidextrousSofa/Analysis/CanonicalWingChord.lean) |
| Facet geometry and reference recovery | Whole-angle support inactivity, exact position of a tilted middle facet, and reversal of the actual chord and height operations at the reference | [FacetPinning](AmbidextrousSofa/Analysis/FacetPinning.lean), [InverseCanonicalization](AmbidextrousSofa/Analysis/InverseCanonicalization.lean) |
| Analytic comparison | Two-endpoint Dirichlet coercivity, exact clipped-functional expansion, fixed-trace strictness, Euler boundary formula, reference stationarity, global sharp value `M/2` for arbitrary support pairs of competitive width, and exact equality up to horizontal translation | [AdaptiveFunctional](AmbidextrousSofa/Analysis/AdaptiveFunctional.lean), [AdaptiveGlobalComparison](AmbidextrousSofa/Analysis/AdaptiveGlobalComparison.lean) |
| Ordinary one-turn input | Complete retained source dependency, actual continuous-passage bridge, and the rational area bound `22199/10000` | [OrdinarySofaBound](AmbidextrousSofa/Analysis/OrdinarySofaBound.lean), [Imported source map](AmbidextrousSofa/Imported/README.md) |
| Actual tilted survivor | Exact corner confinement, convex wing niches, actual cap containment, a compact connected survivor with a genuine passage, and its ordinary-area necessary inequality | [CanonicalOneTurn](AmbidextrousSofa/Analysis/CanonicalOneTurn.lean), [OneTurnArea](AmbidextrousSofa/Analysis/OneTurnArea.lean) |
| Proper-angle maximizer structure | Joint angle/cap continuity, a largest-angle maximum, actual top insertion, used-support saturation, unused curvature gaps, terminal three-support bounds and exclusion of angles through `arctan(5/4)` | [JointCapMaximum](AmbidextrousSofa/Analysis/JointCapMaximum.lean), [UnusedCurvature](AmbidextrousSofa/Analysis/UnusedCurvature.lean), [TerminalThreeSupports](AmbidextrousSofa/Analysis/TerminalThreeSupports.lean), [TerminalScalar](AmbidextrousSofa/Analysis/TerminalScalar.lean) |
| Actual terminal variation and completion | Integrated one-sided angle derivative with the full historical tie term; genuine partial facet pinning; actual missing-support tails; same-cap completion of the specified negative-tilt branches | [TerminalAngleIntegral](AmbidextrousSofa/Analysis/TerminalAngleIntegral.lean), [PartialFacetPinning](AmbidextrousSofa/Analysis/PartialFacetPinning.lean), [TerminalSupportTails](AmbidextrousSofa/Analysis/TerminalSupportTails.lean), [NegativeCompletion](AmbidextrousSofa/Analysis/NegativeCompletion.lean) |
| Exact finite-angle comparisons in progress | Actual tilted diagonal relaxation and global supporting-plane bounds; exact critical clipping and value of the initial-angle relaxation | [DiagonalRelaxation](AmbidextrousSofa/Analysis/DiagonalRelaxation.lean), [DiagonalScalar](AmbidextrousSofa/Analysis/DiagonalScalar.lean), [InitialAngleCritical](AmbidextrousSofa/Analysis/InitialAngleCritical.lean) |
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

`IsFullCapMaximizer.endpoint_complementarity` identifies each actual axis
height with the positive part of its endpoint pressure. In a height-one
maximum with an affine middle, both pressures are strictly positive.
`IsFullCapMaximizer.sweptNiche_le_half_endpoint_height_sum_of_affine` then
bounds the entire central niche using the actual selected polygon moments.
The construction includes disappearing floor intervals and all source ties.

`IsFullCapMaximizer.curvature_density_sharp_on_wing` constructs its own
selected sequence and outputs the actual sharp curvature density on each
compactly contained wing interval away from the top and middle-facet normals.
No supplied density or variational certificate is used.

`IsFullCapMaximizer.wing_chords_le_twice_score_of_affine` derives the
two-wing chord inequality from actual selected polygons and their exact
Green identity. `ordinary_area_chord_necessary_of_canonical_range` combines
it with the genuine one-turn survivor. These statements construct their
own approximations and do not assume a limiting perimeter identity.

`adaptiveFunctional_sub_halfWidth_le_half_M` proves the sharp analytic
comparison for every `QuarterPair` with the natural top traces and total
width at least `8/5`. Its equality theorem gives the reference width and
actual support functions up to a horizontal translation. The geometric
conditions needed to apply it universally remain to be established.

`IsDownwardCap.eq_reference_of_heightSaturation_middleChordCap_eq` recovers
an original equality cap from its actual reference canonicalization. The
proof uses the zero reference niche at the middle endpoints to force zero
extrusion, then recovers the original middle roof from the unit ceiling.
The classification of all canonical equality caps is still required.

`volumeReal_le_ordinaryBound_of_lowerPassage` now derives the retained
ordinary area bound from a genuine compact connected lower passage, with
its original unrestricted terminal angle. `CanonicalOneTurn` now applies it
to the actual niche-cut cap in the required tilted parameter range: the
source proves its fit, connectedness and actual continuous passage first.

`exists_canonical_jointCapMaximizer_largest_angle` supplies a genuine
height-one affine-middle maximum over both caps and terminal angles.
`TerminalThreeSupports` derives the clipped integral relaxation directly
from its actual support. The remaining sharp terminal comparison is still
required.

These results do not yet assemble an upper bound `M` for every ambidextrous
body. The remaining floor/positive-corner source laws, full and partial
sharp bounds, and equality classifications are substantive obligations.

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

The complete 51-module transitive source dependency of the retained ordinary
one-turn theorem is adapted from the [pinned earlier repository][research]
under [Imported](AmbidextrousSofa/Imported/README.md). It includes the actual
convex-body/Stieltjes calculus, Gerver parameter existence, ordinary value
theorem and rational area enclosure. Source paths, revision, namespace/import
transformations and the original Apache-2.0 license are recorded there.
No ordinary uniqueness theorem is used. This source adaptation has not been
compiled or independently re-reviewed in its entirety.

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
