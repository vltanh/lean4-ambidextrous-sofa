# Roadmap to F7 source closure

## Current uncompiled-draft publication

The source draft is being published in dependency stages; the detailed roadmap records the completed work and the next publication step. Full source auditing and kernel verification are deferred.

The current, detailed execution plan is [F7-DRAFT-ROADMAP.md](F7-DRAFT-ROADMAP.md). The longer sections below retain the earlier implementation history.

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
| F4 | Universal full-angle cap score at most `M/2`, including nonsmooth, asymmetric and subunit caps | Horizontal rigidity complete; all tilted first-unit selection, overhang, geometric moments, actual phases and bad-entry lower laws written; common occupation and final actual GF assembly remain |
| F5 | Universal cap value reduction retaining the whole outgoing wall and independent motion angles | Actual proper reflected excess and strict contradiction complete for a largest-angle joint maximizer; full-cap maxima now also maximize jointly; sharp numerical value awaits F4 |
| F6 | Every equality cap, inverse canonicalization, individual proper-angle strictness and literal original compact-body recovery | Canonical inverse and original-body recovery written; individual proper equality requires the separate fixed-cap extension/atom argument, and full equality awaits tilted exclusion |
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

### F4 — complete the actual tilted-cap exclusion

The horizontal branch is now source-complete through literal rigidity.
`HorizontalLeakageBound`, `HorizontalWidthReduction` and
`HorizontalUnitCurvature` apply the rational leakage rows to actual caps.
`ClosedSupportPair`, `SupportAreaAC`, `HorizontalSignedArea` and
`HorizontalCalibration` identify the actual geometric score with the
analytic functional. `HorizontalClassification`, `CapNormalization` and
`HorizontalRigidity` apply its sharp equality case; the reference reflection
is reduced to a literal horizontal translation by `HorizontalSymmetry`.

The positively tilted branch already has the actual full-width ceiling,
sharp density and ODE, endpoint pressure, actual one-turn survivor, outside
niche convexity and global chord bounds. The following newer source chains
are completed:

1. `TiltedSupportPair` and `TiltedSupportControls` construct the literal
   first/low-left pair, including its initial zero-density interval.
   `TiltedInitialCircle` constructs the actual stopping point.
   `TiltedEnergyBarrier` and `TiltedInitialUnitRegions` turn the scalar
   initial-floor conditions into an actual first-unit density.
2. `TiltedCrossingExcess` and `TiltedLateExcess` derive actual early
   excess bounds and select a density unit after `11/15`, with weighted
   excess less than `1/40`. `TiltedEndpointLeakage` and
   `TiltedLeakageMoment` turn these into actual endpoint and outside-area
   estimates.
3. `CompanionZero`, `TiltedZeroGeometry`, `DrySourceProjection`,
   `DryTopBalance` and `TiltedTopProjection` prove the literal low-wing
   zero, actual positive middle interval and exact top projection.
4. `SplitWingChord`, `SmallTiltConstants`, `SmallTiltScalar` and
   `SmallTiltArea` prove the small-height initial-energy tests from the
   actual ordinary-area comparison. `TiltedTriangleArea` excludes the
   remaining high-width middle-height region once its actual dry-left
   conclusion is supplied by the reflected projection step.
5. `FirstUnitTangency` constructs the actual middle tangency crossing,
   closed traces and source-box momentum sign under a first-unit density.

The reflected full-cap unit-prefix application is now written in
`TiltedReflectedControls`, `TiltedReflectedLateUnit` and `TiltedTopOverhang`.
`TiltedUnitSelection` closes all first-unit parameter regions. The
generalized `FirstUnitTangency` works for every `C>1/2`.
`FirstUnitProjection`, `FirstUnitTopOverhang` and
`FirstUnitGeometricMoments` prove the exact projection, dry left middle,
positive overhang, four FTC moments and the first-floor abscissa bounds.

`CoreContactGeometry` constructs literal positive core and tangent pieces,
including angular and tangent plateaus. `FirstSourceFlux`,
`FirstSourceDensity` and `CoreSourceLowerBounds` supply the actual density
lower laws. `FirstUnitCrossings`, `FirstUnitPhases`,
`FirstUnitPrefixEnergy` and `FirstUnitBadEntry` construct the sign phases
and show that the first possible excess follows the middle crossing with
second momentum at most one quarter. `FirstUnitLateWindowClosure` handles
the additional companion-unit event order. `FirstFloorVisibility` and
`FirstFloorTrapping` close the analytic zero-height boundary case.

`JointSourceMeasure`, `JointSourceLimit` and `JointSourceMarginal` now
construct a single common source limit with its actual angular marginal.
`PositiveWallContacts` supplies strict tangent/core contact classification.
Finish its spatial flux and common fractional occupation; instantiate every
actual phase/floor/fold input of the two first-unit contradictions; then
classify every prescribed full maximum and use actual maximum existence.

The 51 imported ordinary-theorem files remain a complete retained source
dependency, with attribution and the original license. No build or full
independent review of that imported chain has occurred.

### F5 — largest-angle value reduction completed in source

`TerminalReflectedParameters`, `ProperExcessScalar`, `ProperReflectedEntry`
and `ProperExcessEnvelope` derive the actual reflected early-excess bounds,
including the terminal atom and the complete outgoing wall.
`ProperTerminalExclusion` constructs the actual density, applies the
strict required-excess comparison, and rules out a proper largest-angle
joint maximizer. Its endpoints are
`exists_jointCapMaximizer_full_angle` and
`IsFullCapMaximizer.isJointCapMaximizer`. Once F4 supplies the sharp full
value, this proves the universal non-strict cap/angle value bound.

### F6 — individual equality and actual recovery

A largest-angle selection alone does not exclude an individual proper
equality cap: the full reference already belongs to the joint equality
set. The manuscript's TB1 argument must be applied to that individual
cap. `TerminalExtension` already constructs a single same-cap angle
increase for an overlong terminal facet. Use actual regular curvature at
the enlarged angle to contradict the unchanged positive charged facet,
derive its terminal mass bound without a largest-angle premise, and then
apply the completed quantitative proper comparison. Negative completed
branches must use the actual full-cap rigidity, once F4 is closed.

`FullCapRecovery` constructs the actual height-saturated middle-chord cap,
preserves its full-maximizer status, and recovers the original cap from
reference equality of that concrete canonical cap.
`Measure/ActualReferenceRecovery` aligns both actual cap translates,
reconstructs the literal hull and body, and applies finite equal-area
regular-closed recovery. Apply these after the full and individual proper
classifications. Exact compact-set equality up to a rigid motion remains
the final target, with reference feasibility and exact area as converse.

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
