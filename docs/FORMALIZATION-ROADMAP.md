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
| F4 | Universal full-angle cap score at most `M/2`, including nonsmooth, asymmetric and subunit caps | Global maximizer/canonicalization, prescribed polygon selection, first variations, endpoint cuts, top insertion, low-height exclusion and analytic comparison implemented; remaining curvature/exposure and global sharpness arguments below |
| F5 | Universal proper-angle cap bound retaining the whole outgoing wall, independently for the two motions | Actual terminal wall and original-motion reduction implemented; sharp terminal analysis remains |
| F6 | Every equality cap, inverse canonicalization, strict proper-angle inequality and literal original compact-body recovery | Exact deficit and reference regularity/recovery infrastructure implemented; sharp equality classification and assembly remain |
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
source masses and the total translation balance.

`CapInsertion` and `TopInsertion` prove that inserting a height-one point at
a middle endpoint can leave the **entire** charged niche unchanged.
`CapReflection` and `TopFacetEndpoints` place the high endpoint of a canonical
affine middle at height one. The exact tent integrals and scalar inequalities
in `PositiveTent`, `DiagonalTent` and `LowHeight*` then show that both middle
endpoint roofs of a canonical full maximum exceed one half.

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

1. Complete the neighboring-wall exposure estimates. `FacetCurvature` and
   `SelectedCurvature` identify literal polygon source lengths with actual
   supporting-facet atoms, retain the uncharged middle facet, and bound the
   total selection defect by a quantity tending to zero.
2. Pass the selected finite estimates to weak limits at the prescribed
   maximizer. Separate the central facet/top normal and preserve disappearing
   zero-height niche source mass. Derive the actual support-curvature density
   bounds and necessary endpoint face convergence.
3. Complete endpoint complementarity and the exact exposure moments/Green
   identity. Use the low-height result to obtain both positive pressures.
4. Complete the support-inactivity/facet-pinning argument, horizontal unit
   curvature and geometric comparison to the analytic functional. Complete
   all tilted-width/height exclusions from the written full-cap proof.
5. Apply the completed analytic global comparison and strict equality
   classification to the actual geometric domain after these reductions.
6. Discharge the ordinary one-turn area bound and rational Gerver enclosure
   used by strict exclusion branches, through an appropriate complete source
   dependency and a bridge from the actual constructed moving body.

The four files under `Imported` are objective-independent planar convex-body,
Lebesgue–Stieltjes and surface-area calculus adapted from the pinned earlier
repository. Their actual support/curvature definitions are bridged in
`SupportCurvature`; they do not supply the ordinary one-turn optimality input.
Source attribution and the original Apache-2.0 license are retained.

### F5 — proper terminal angles

Prove the actual terminal-facet and reflected-impulse laws, angle-domain
compactness, all-sign width cuts, weighted companion bounds and the sharp
terminal comparison. The entire terminal first wall must be retained.
The two angular ranges must cover all endpoints and the two original motion
angles must remain independent. At `π/2`, use the full-cap theorem.

### F6 — equality of actual bodies

Classify every prescribed canonical equality cap, including horizontal
translation. Reverse the actual chord and height operations at the reference;
prove strict inequality for every proper terminal angle; use the four-term
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
