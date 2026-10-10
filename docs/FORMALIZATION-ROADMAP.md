# Roadmap to F7 source closure

## Acceptance and current status

The requested deliverable is an **uncompiled Lean proof source**, with no
admissions, custom axioms or CI. F7 has two distinct acceptance items:

1. **Source closure:** the unconditional original-domain optimality and exact
   compact-set uniqueness theorem has a complete source proof, and all its
   mathematical dependencies have complete proof bodies.
2. **Kernel verification:** successful elaboration and the actual transitive
   axiom audit. This item is explicitly excluded from the current task by the
   user's instruction not to compile.

Source closure is still in progress. A lexical policy pass alone does not
close it. No project source has been compiled. The prepared axiom queries
remain unexecuted. Every theorem presently declared has an explicit proof
body; missing mathematics is listed below, not inserted as a hypothesis
encoding the desired final theorem.

The mathematical source is the [Gate 3 manuscript][manuscript] at research
commit [`20489723dc8777a82ee70ae60510115dc6f21085`][research]. Its written gate
closures and research-session reviews are distinct from formal verification.

## Stage map

| Stage | Required source result | Current source status |
| --- | --- | --- |
| F0 | Exact constant, original coordinate domain, signed-fiber algebra and regular-closed recovery | Implemented |
| F1 | Actual compact hull/caps, attained roofs/supports, complete barriers, measurability and actual area integration | Implemented |
| F2 | Original two-motion normalization, area invariance, angular reach, genuine terminal constraints and actual-cap score reduction | Implemented for the unchanged `IsAmbidextrous` predicate with continuous real-angle rigid paths |
| F3 | Actual reference support/hull/body, both feasible passages, regular closedness and exact area `M` | Implemented, including exact reference cap score `M/2` |
| F4 | Universal full-angle cap score at most `M/2`, including nonsmooth, asymmetric and subunit caps | Actual regular-domain density/ODE, inner-source interval occupation, negative-corner nullity, endpoint laws, central height, Green/chord limit and one-turn survivor implemented; floor and same-sign corner laws and actual short-width exclusion implemented; fractional positive-corner occupation, global unit-wing and remaining tilted sharpness steps remain |
| F5 | Universal proper-angle cap bound retaining the whole outgoing wall, independently for the two motions | Actual joint/largest-angle maximum, top insertion, used-support saturation, unused curvature gaps, initial-angle exclusion through arctan(8/3), actual terminal facet/exposure bounds and circle margin implemented; top-projection/source moment and final terminal comparison remain |
| F6 | Every equality cap, inverse canonicalization, strict proper-angle inequality and literal original compact-body recovery | Exact deficit, reference regularity and actual inverse canonicalization implemented; sharp cap classification and original-body assembly remain |
| F7 source closure | Unconditional original-domain area bound and exact uniqueness, with no missing mathematical input | In progress; depends on F4–F6 |
| F7 kernel check | Elaboration and actual standard-axiom output | Not performed; compilation and CI prohibited for this task |

## Source already completed since the initial draft

### Original-motion and reference bridges

`Geometry/RigidMotion`, `Measure/RigidInvariance`, `Measure/StripBounds` and
`Geometry/MotionReduction` normalize genuine independent passages and prove
the area bound for wrong-way or insufficient angular excursions. The main
`IsAmbidextrous.original_domain_score_reduction` obtains independent effective
angles in `(π/4,π/2]`, or the strict small-area alternative. The proper
terminal strip is retained; no monotonicity or full-turn hypothesis was
added to the original predicate.

The reference modules now construct actual supporting boundary points and
prove the reverse support inequalities. `Reference/Body` defines the actual
niche-cut sofa, proves path connectedness and both corridor passages.
`Reference/Regularity` proves the regular-closed property needed for literal
set recovery. `Reference/Value` evaluates actual cap and niche integrals:
`capScore_referenceCap = M/2` and `volumeReal_referenceSofa = M`.

### Actual cap optimization and polygon selection

`Analysis/CapCompactness`, `CapVolumeContinuity`, `CapNicheContinuity`,
`CapRoofConvergence` and `CapScoreContinuity` establish the relevant actual
Hausdorff limits. Roof convergence uses indicator convergence and Fubini;
whole-angle niche continuity includes the singular angular endpoints.
`WideCap` uses an actual 45-degree tent. `GlobalCapMaximum` combines width
coercivity, translation and compact maximization to produce a full-domain
maximum. `Chord` and `Extrusion` construct its canonical height-one cap with
an affine middle roof.

`FiniteEnvelope` differentiates actual finite min/max expressions and tracks
literal source sets, including repeated leaves. `PolygonVariation`,
`PolygonEnvelope`, `PolygonExposure` and `AxisVariation` turn those formulas
into actual cap variations. An outward axis variation is used only for a
positive endpoint face.

`GridNiche`, `DyadicGrid`, `GridPolygon` and `GridScore` give actual uniform
finite-grid approximation. `Circumscription` retains sampled support values
and the actual projection. `PersistentPenalty`, `GridSeparation` and
`SelectedSequence` produce selected polygons converging to **any prescribed**
full-cap maximum. Positive coefficients at every fixed dense sample identify
the actual limiting cap; no assumed optimizer-selection property is used.

### Endpoint and analytic results

`EndpointTrimming` proves actual cuts and erosions, including their exact
roofs, shortened projection, support inequalities and product-metric
Hausdorff bounds. `EndpointPolygons` proves exact finite-class closure and
retightening. `EndpointPressure` derives inward pressure inequalities from
those actual competitors, including the unpenalized full score.
`ErosionVariation` proves the exact finite moving-wall/moving-endpoint
derivative with its quadratic sliver error; `ExposureMoments` proves actual
source masses and the total translation balance. `ErosionMoments` and
`SelectedEndpointMoments` instantiate actual selected inequalities with a
uniform vanishing error. `CapInteriorRoof` and `SelectedPressureLimit` prove
the moving middle-roof and niche limits and hence the selected pressure and
endpoint-height limits. `SelectedErosionMoments` gives the exact limits of
both erosion moments as the negative parts of the target pressures.
`AxisFaces` and `AxisHeightLimit` now identify the height limits with the
actual target faces using the punctured-axis curvature bounds.
`EndpointComplementarity` proves the law for every actual full maximum;
`EndpointPositivity` forces both canonical pressures to be positive and
therefore both actual selected erosion moments to tend to zero.

`FiniteSpatialVariation`, `FiniteRoofVariation` and `FiniteNicheOscillation`
identify the literal sum of finite erosion velocities with minus absolute
wall slope. A concave-roof total-variation estimate handles all positions
of a selected polygon's top. `SelectedNicheHeight` passes the resulting
pointwise inequality at moving abscissae to any prescribed canonical full
maximum and derives `n(x) ≤ (eR+eL)/2` on the entire middle interval.
This closes the central height estimate without a weak-occupation identity.

`MiddleNormalStability` and `MiddleMassLimit` eliminate the uncharged middle
curvature away from its normal without assuming a rate between Hausdorff
distance and mesh. `WingCurvatureIntervals` and `WingCurvatureDensity` give
the actual bounded Stieltjes density. `MovingSupportSecants`, `SourceVelocity`,
`LocalSourceDensity` and `SharpCurvatureDensity` sharpen it to
`ρ ≤ max |q| ((|q|+1)/2)` by local finite source bounds and Lebesgue
differentiation. These are actual density constructions, not certificate
hypotheses. The support-velocity and occupation consequences remain below.

`CapInsertion` and `TopInsertion` prove that inserting a height-one point at
a middle endpoint can leave the **entire** charged niche unchanged.
`CapReflection` and `TopFacetEndpoints` place the high endpoint of a canonical
affine middle at height one. The exact tent integrals and scalar inequalities
in `PositiveTent`, `DiagonalTent` and `LowHeight*` then show that both middle
endpoint roofs of a canonical full maximum exceed one half.

`RoofGain`, `InactiveNormals` and `FacetPinning` prove an actual local
insertion and pin the maximal tilted supporting facet's horizontal
projection exactly to the middle interval. Strict one-sided corner laws
and their subsequent curvature applications are separate remaining steps.

`InverseCanonicalization` now reverses the concrete chord and height
operations at the reference, including horizontal translation. A positive
extrusion would strictly increase score because the final reference niche
vanishes at a middle endpoint. Once the extrusion is zero, the unit strip
forces recovery of the original middle roof. This does not infer that
arbitrary equal-score chord clipping is injective.

`QuarterFunctions`, `DirichletEnergy`, `QuadraticEnergy`, `AdaptiveFunctional`
and `EulerFlux` provide a concrete two-support variational calculus and
strict comparison for fixed traces. `Reference/Stationarity` proves the
reference Euler equations. The `AdaptiveGlobal*` family supplies explicit
stationary profiles, width coverage, sign phases and fixed-width comparisons.
`AdaptiveGlobalComparison` now proves the global sharp value `M/2` and
identifies exact equality with the reference support functions up to
horizontal translation. The actual family integrals and scalar maximum are
proved in `AdaptiveGlobalValue` and `AdaptiveGlobalScalar`.

## Remaining critical path

### F4 — weak source curvature and the full sharp bound

1. The full open nonexceptional normal domain and actual support/tangent
   and corner-velocity integral identities are now implemented in
   `RegularCurvatureDomain` and `SupportDensityCalculus`. The central facet
   and top normal remain explicit. Endpoint face convergence,
   complementarity, positivity and the central niche-height estimate are
   complete source results.
2. `SourceOccupation` now identifies literal finite inner-source interval
   limits with actual curvature on compact regular sets.
   `NegativeCornerCurvature` proves actual zero curvature below the floor.
   `FiniteGraphGreen`, `FiniteSourceBalance`, `SupportHeightControl` and
   `SelectedGreenLimit` give the exact stationary finite Green limit.
   `FiniteGraphLength` and `CanonicalWingChord` derive actual wing chord
   inequalities. `NonpositiveCornerCurvature` combines negative and floor
   laws; `ShadowCurvature` gives the actual same-sign density bounds. Complete
   fractional positive-corner occupation and geometric calibration.
3. Complete strict corner laws, horizontal unit curvature and geometric
   comparison to the analytic functional. Complete all tilted-width/height
   exclusions from the written full-cap proof. `TiltedInitialEnergy` and
   its exact rational parameter bounds are implemented. The first-unit
   energy, convolution, explicit fold payment and raw-momentum contradiction
   are now written in the `Tilted*` family.
   Their source-occupation hypotheses still need to be derived from actual
   cap geometry. The late-excess and remaining tilted exclusions are open.
   `DiagonalRelaxation` now gives the literal tilted diagonal integral with
   both clipped tails. `DiagonalScalar` proves its global supporting-plane
   bounds and exact short-width stability. `ShortWidthExclusion` now
   combines actual exterior support cuts with both extra niche tails and
   their exact clipped areas, proving the exclusion through a=1001/1000.
   The wider tilted and intermediate width/height exclusions remain.
4. Apply the completed analytic global comparison and strict equality
   classification to the actual geometric domain after these reductions.

The actual one-turn geometry needed for the tilted exclusion is now written:
`CornerTrigonometry` and `CornerConfinement` place all attached corners in
the middle interval throughout the required parameter range. `NicheWings`
and `NicheBoxBounds` give convexity and endpoint control. `SelectedNicheHeight`
supplies central fit, and `CanonicalOneTurn` proves the entire niche lies
below the actual roof. `Topology/VerticalRegion`, `OneTurnSurvivor` and
`OneTurnArea` establish compactness, connectedness, a genuine continuous
passage, actual Cavalieri area and the ordinary-area necessary inequality
`M/2 + C(3-E-3h/2) ≤ 22199/10000`. `CanonicalWingChord` now also gives
`sqrt(C²+(1-h/2-E/2)²) + C(3-E-3h/2) ≤ 22199/10000` from the actual
Green limit. These applications assume neither an auxiliary body's
feasibility nor a central height certificate.

The 51 files under `Imported` are the complete project-source import closure
of the earlier ordinary one-turn theorem. Their actual support/curvature
definitions are bridged in `SupportCurvature`; `OrdinarySofaBound` bridges
the physical movement predicate and rational value bound. The exact source
map and namespace/import transformations are documented in
`Imported/README.md`; attribution and the Apache-2.0 license are retained.

### F5 — proper terminal angles

`PartialCapContinuity` and `JointCapMaximum` now prove joint compact
maximization and select the largest attaining angle. `PartialTopInsertion`
preserves the full proper barrier. `UsedSupportSaturation` identifies the
actual cap after its middle chord cut; `UnusedCurvature` eliminates precisely
the unused open normal intervals while retaining their endpoints and the
middle-facet normal. `TerminalWallBound` and `TerminalScalar` exclude
`α ≤ arctan(5/4)`. `TerminalThreeSupports` derives the actual three-support
clipped integral relaxation. `InitialAngleScalar` proves the exact stationary
value, strict rational margins and subsequent variation budgets.

`InitialAngleRelaxation` and `InitialAngleCritical` now give the actual
relaxation and its exact critical clipping/value. `TerminalAngleIntegral`
proves the integrated one-sided angle variation, retaining all historical
ties. `PartialInactiveNormals` and `PartialFacetPinning` prove literal
fixed-angle facet pinning. `TerminalSupportTails` derives the actual missing
support tails; `NegativeCompletion` completes the specified negative-tilt
branches on the same cap and excludes them for a largest-angle maximum.

`InitialAngleExclusion` discharges the actual relaxation assumptions and
proves α>arctan(8/3); `InitialAngleWidth` gives width>49/25.
`TerminalCorner` derives the actual terminal facet reserve from same-cap
extension, and `TerminalExposure` derives strict terminal occupation by an
inward supporting-line cut. `TerminalCircleMargin` proves the exact scalar
MP.24 comparison with actual-parameter inputs. Complete the top-projection
horizontal source moment, remaining reflected impulse, weighted companion
bounds and final terminal comparison. The entire first
terminal wall remains in the objective. The two original motion angles must
stay independent, all angular endpoints must be covered, and `π/2` must be
handled by the full-cap theorem.

### F6 — equality of actual bodies

Classify every prescribed canonical equality cap, including horizontal
translation, then apply the completed actual reference inverse. Prove strict
inequality for every proper terminal angle; use the four-term
physical deficit to recover both original cap scores and the actual common
hull. Apply the proved regular-closed recovery only after containment and
finite equal area have been established. Equality must be literal equality
of compact sets up to congruence. Reference feasibility and exact area supply
the converse.

### F7 — final source assembly and review

Assemble the unconditional theorem from the unchanged original two-motion
predicate. Check declaration names/import closure, review the theorem's full
hypothesis list for circular or target-shaped assumptions, regenerate the
prepared axiom inventory, and publish the concrete source through the GitHub
API. Keep the pull request a draft, omit CI, and explicitly retain the
uncompiled status. No Lean/Lake command or axiom-query execution belongs to
this source-only completion.

## Trust discipline

The intended foundational allowlist is `propext`, `Classical.choice`, and
`Quot.sound`. Each declared source theorem must have an actual proof body.
Natural local hypotheses in reusable analysis lemmas are explicit; they
must be discharged at the global application. A scalar certificate that
assumes the sharp bound or equality classification is not source closure.

The [source review](SOURCE-REVIEW.md) records actual inspections and the
Python-only policy check. That check cannot establish elaboration, theorem
correctness or actual transitive axiom dependencies. Kernel verification
requires a separate future instruction permitting compilation.

[research]: https://github.com/vltanh/lean4-moving-sofa/commit/20489723dc8777a82ee70ae60510115dc6f21085
[manuscript]: https://github.com/vltanh/lean4-moving-sofa/blob/20489723dc8777a82ee70ae60510115dc6f21085/docs/ambidextrous/GATE3-MANUSCRIPT.md
