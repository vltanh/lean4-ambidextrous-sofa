# Uncompiled source: review record

**Review date:** October 10, 2026.

**Mode:** source inspection, pinned-source API lookup and Python-only lexical
checks. No project Lean source has been compiled; no CI or axiom queries have
been run. Successful elaboration and actual transitive axioms remain unchecked.
This record is not a kernel proof log or an external referee report.

## Current source inventory

The entry point covers **104 implementation modules**, containing
**1816 named theorems** and **2176 explicitly named declarations**.
Every declared theorem has an explicit proof body. `AxiomAudit.lean` prepares
one unexecuted `#print axioms` query per explicitly named declaration.
Generated constructors, projections, recursors and equation lemmas are not
separate source commands in this inventory.

The four adapted objective-independent modules under `Imported` are counted
in these totals. They retain their source revision, path, modification notice
and Apache-2.0 license. The original ordinary one-turn optimality theorem is
not among those four modules.

## Substantive source reviews

Independent collaborating reviewers inspected the actual geometric and
measure-theoretic reductions, significant proof bodies, and pinned Mathlib
interfaces. The following completed reviews cover the principal new chains:

- Original rigid normalization, exact area invariance, strip exclusions and
  independent angular reach from genuine passages. The original
  `IsAmbidextrous` predicate was retained.
- Actual reference support realization, exact faces and niche, physical body
  feasibility, regular closedness, and the complete actual-area computation.
  In particular the identity `volumeReal_referenceSofa = M` is derived from
  actual cap and niche integrals, without an area certificate.
- Hausdorff compactness of actual caps, convex frontier nullity, indicator
  and roof convergence, continuity of the whole-angle niche at singular
  endpoint angles, and score continuity with moving integration domains.
- Finite min/max source derivatives, repeated source handling, actual
  floating-wall variations and the conversion to finite spatial scores.
- Actual cuts and erosions, exact shortened projections, min-roof identities,
  support changes and the product-metric Hausdorff estimate. The finite
  erosion halfplanes are identified as sets before retightening to actual
  supports. Inward endpoint pressures use genuine contained cap variations.
- Point insertion's actual max-support identity; whole-angle niche invariance
  on the charged middle; strict exterior roof gain; horizontal reflection;
  high-endpoint localization; and the translation/reflection application of
  the low-height estimate.
- The half-angle energy identity, two-endpoint Dirichlet coercivity,
  fixed-trace strictness, clipped-functional first variation, reference Euler
  stationarity, natural width boundary formula and the explicit large-width
  analytic branch.

The explicit analytic family now has a complete global comparison and exact
equality classification. Source reviews checked the C1 joins, including the
degenerate switches; all clipped signs and Euler identities; actual integral
values; the strict scalar maximum; width coverage and the translation of the
reference equality data. The translation and integral-value modules received
independent review. A pinned multiplication-inequality rewrite was corrected.

The dense-grid/persistent-penalty selection, actual polygon-curvature atoms,
vanishing selection defects, moving-envelope derivatives and source moments
are included with complete proof bodies. Their authors performed focused
static review; the final independent cross-module review and remaining
geometric applications are continuing.

The integration scan found two duplicate helper declarations:
`convex_verticalFiber` and `IsDownwardCap.intervalIntegrable_capRoof`.
Their duplicate copies were removed and the existing proved helpers are
imported. Review also made the affine translation's scalar identity explicit
and replaced several variable-index rewrite shortcuts by local quantified
lemmas. These are source corrections; no elaborator was invoked to test them.

## Source-policy guard

The source-only command is:

```sh
python3 scripts/check_source_policy.py
```

Its `--write-axiom-audit` option generates Lean query text without executing
it. `--inventory-json` emits the namespace-qualified source inventory.
The guard strips comments and strings, rejects admissions, custom axioms,
unsafe/native/metaprogramming proof shortcuts, checks names and audit-query
coverage, detects import cycles, checks entry-point coverage and pins, and
rejects CI configuration. Only Mathlib (including its submodules) and
project-local modules are permitted imports.

The intended axiom allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
The lexical guard cannot compute actual transitive axiom dependencies or
establish that any theorem elaborates. The prepared queries have not been
run and the actual axiom sets are unverified.

The checked snapshot has **106 Lean files**, including entry point and
audit, **104 implementation modules**, **1816 named theorems**,
and **2176 prepared queries**. The source-policy guard passed.
Whitespace and local documentation links are checked before publication.
Publication uses GitHub's Git Data API with exact tree/blob comparisons;
no workflow is added and commits use `[skip ci]`.

## Pinned source and scope of verification

Lean is pinned to `leanprover/lean4:v4.35.0-rc3`; Mathlib is pinned to
[`c55e6e786f49471c72fbddbec5415808896aec1e`][mathlib]. Relevant Mathlib
source declarations are inspected locally from that exact revision and
through the GitHub API. The lockfile preserves the exact upstream package
revisions. No build compatibility or transitive kernel audit is claimed.

The adapted planar convex-body/Stieltjes source is from
[`20489723dc8777a82ee70ae60510115dc6f21085`][research]. Its project-local
namespace and import transformations preserve the mathematical definitions;
private helpers received stable public names for the prepared audit. The
bridge in `Analysis/SupportCurvature.lean` identifies the actual support
functions and transfers product-metric Hausdorff convergence to uniform
angular-support convergence. That import supplies no assumed sharp bound.

## Remaining mathematics

F7 source closure is **not yet achieved**. The current project has actual
reference attainment and an original-domain reduction, but still lacks the
universal full and proper-angle sharp cap theorems and their complete
equality classification. Weak source-curvature and exposure balances,
tilted/full/terminal exclusions, the retained ordinary one-turn input,
inverse canonicalization and final original-body assembly remain on the
[critical path](FORMALIZATION-ROADMAP.md).

No unproved global result is installed as an axiom, placeholder or a
certificate field equivalent to the desired conclusion. Kernel verification
is a separate future task and is excluded by the current no-compilation
instruction.

## Per-module inventory

| Implementation module | Theorems | Named declarations |
| --- | ---: | ---: |
| `AmbidextrousSofa/Algebra/Deficit.lean` | 22 | 26 |
| `AmbidextrousSofa/Analysis/AdaptiveFunctional.lean` | 13 | 24 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalBoundary.lean` | 12 | 19 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalBranches.lean` | 39 | 44 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalComparison.lean` | 9 | 10 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalFamily.lean` | 43 | 61 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalMomenta.lean` | 39 | 55 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalParameters.lean` | 21 | 28 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalScalar.lean` | 18 | 18 |
| `AmbidextrousSofa/Analysis/AdaptiveGlobalValue.lean` | 17 | 20 |
| `AmbidextrousSofa/Analysis/AdaptiveTranslation.lean` | 11 | 14 |
| `AmbidextrousSofa/Analysis/AxisVariation.lean` | 8 | 9 |
| `AmbidextrousSofa/Analysis/CapCompactness.lean` | 14 | 15 |
| `AmbidextrousSofa/Analysis/CapInsertion.lean` | 10 | 11 |
| `AmbidextrousSofa/Analysis/CapMaximum.lean` | 5 | 6 |
| `AmbidextrousSofa/Analysis/CapNicheContinuity.lean` | 16 | 20 |
| `AmbidextrousSofa/Analysis/CapOrder.lean` | 7 | 7 |
| `AmbidextrousSofa/Analysis/CapReflection.lean` | 22 | 24 |
| `AmbidextrousSofa/Analysis/CapRoofConvergence.lean` | 6 | 6 |
| `AmbidextrousSofa/Analysis/CapScoreContinuity.lean` | 6 | 6 |
| `AmbidextrousSofa/Analysis/CapTranslation.lean` | 21 | 23 |
| `AmbidextrousSofa/Analysis/CapVolumeContinuity.lean` | 7 | 8 |
| `AmbidextrousSofa/Analysis/Chord.lean` | 24 | 28 |
| `AmbidextrousSofa/Analysis/Circumscription.lean` | 9 | 10 |
| `AmbidextrousSofa/Analysis/DiagonalTent.lean` | 10 | 12 |
| `AmbidextrousSofa/Analysis/DirichletEnergy.lean` | 7 | 7 |
| `AmbidextrousSofa/Analysis/DyadicGrid.lean` | 7 | 10 |
| `AmbidextrousSofa/Analysis/EndpointPolygons.lean` | 8 | 8 |
| `AmbidextrousSofa/Analysis/EndpointPressure.lean` | 25 | 29 |
| `AmbidextrousSofa/Analysis/EndpointTrimming.lean` | 66 | 71 |
| `AmbidextrousSofa/Analysis/ErosionVariation.lean` | 6 | 7 |
| `AmbidextrousSofa/Analysis/EulerFlux.lean` | 7 | 11 |
| `AmbidextrousSofa/Analysis/ExactEstimates.lean` | 3 | 3 |
| `AmbidextrousSofa/Analysis/ExposureMoments.lean` | 12 | 14 |
| `AmbidextrousSofa/Analysis/Extrusion.lean` | 22 | 25 |
| `AmbidextrousSofa/Analysis/FacetCurvature.lean` | 9 | 9 |
| `AmbidextrousSofa/Analysis/FiniteEnvelope.lean` | 14 | 20 |
| `AmbidextrousSofa/Analysis/FiniteScore.lean` | 11 | 11 |
| `AmbidextrousSofa/Analysis/FiniteVariation.lean` | 9 | 10 |
| `AmbidextrousSofa/Analysis/GlobalCapMaximum.lean` | 7 | 8 |
| `AmbidextrousSofa/Analysis/GridNiche.lean` | 15 | 20 |
| `AmbidextrousSofa/Analysis/GridPolygon.lean` | 14 | 20 |
| `AmbidextrousSofa/Analysis/GridScore.lean` | 6 | 7 |
| `AmbidextrousSofa/Analysis/GridSeparation.lean` | 2 | 2 |
| `AmbidextrousSofa/Analysis/LowHeightAlgebra.lean` | 9 | 11 |
| `AmbidextrousSofa/Analysis/LowHeightGeometry.lean` | 7 | 8 |
| `AmbidextrousSofa/Analysis/LowHeightMaximizer.lean` | 4 | 4 |
| `AmbidextrousSofa/Analysis/LowHeightScore.lean` | 9 | 9 |
| `AmbidextrousSofa/Analysis/PersistentPenalty.lean` | 18 | 28 |
| `AmbidextrousSofa/Analysis/PolygonEnvelope.lean` | 23 | 37 |
| `AmbidextrousSofa/Analysis/PolygonExposure.lean` | 6 | 8 |
| `AmbidextrousSofa/Analysis/PolygonVariation.lean` | 12 | 13 |
| `AmbidextrousSofa/Analysis/PositiveTent.lean` | 6 | 6 |
| `AmbidextrousSofa/Analysis/QuadraticEnergy.lean` | 11 | 14 |
| `AmbidextrousSofa/Analysis/QuarterFunctions.lean` | 4 | 9 |
| `AmbidextrousSofa/Analysis/RoofContinuity.lean` | 3 | 3 |
| `AmbidextrousSofa/Analysis/SelectedCurvature.lean` | 10 | 13 |
| `AmbidextrousSofa/Analysis/SelectedSequence.lean` | 9 | 10 |
| `AmbidextrousSofa/Analysis/SupportCurvature.lean` | 9 | 11 |
| `AmbidextrousSofa/Analysis/TopFacetEndpoints.lean` | 3 | 3 |
| `AmbidextrousSofa/Analysis/TopInsertion.lean` | 6 | 6 |
| `AmbidextrousSofa/Analysis/WideCap.lean` | 10 | 10 |
| `AmbidextrousSofa/ExactConstant.lean` | 22 | 26 |
| `AmbidextrousSofa/Geometry/AngularDomain.lean` | 9 | 11 |
| `AmbidextrousSofa/Geometry/BarrierAnalysis.lean` | 23 | 23 |
| `AmbidextrousSofa/Geometry/Barriers.lean` | 15 | 21 |
| `AmbidextrousSofa/Geometry/CapGeometry.lean` | 34 | 38 |
| `AmbidextrousSofa/Geometry/Caps.lean` | 9 | 13 |
| `AmbidextrousSofa/Geometry/Hallway.lean` | 15 | 19 |
| `AmbidextrousSofa/Geometry/HullCompact.lean` | 8 | 9 |
| `AmbidextrousSofa/Geometry/MotionReduction.lean` | 10 | 10 |
| `AmbidextrousSofa/Geometry/Motions.lean` | 2 | 8 |
| `AmbidextrousSofa/Geometry/Plane.lean` | 9 | 20 |
| `AmbidextrousSofa/Geometry/Reflection.lean` | 37 | 40 |
| `AmbidextrousSofa/Geometry/RigidMotion.lean` | 18 | 22 |
| `AmbidextrousSofa/Geometry/Support.lean` | 40 | 45 |
| `AmbidextrousSofa/Geometry/UpwardSupport.lean` | 5 | 5 |
| `AmbidextrousSofa/Imported/ConvexBody.lean` | 67 | 78 |
| `AmbidextrousSofa/Imported/LebesgueStieltjes.lean` | 40 | 42 |
| `AmbidextrousSofa/Imported/Plane.lean` | 116 | 133 |
| `AmbidextrousSofa/Imported/SurfaceArea.lean` | 35 | 41 |
| `AmbidextrousSofa/Measure/CapAssembly.lean` | 9 | 13 |
| `AmbidextrousSofa/Measure/CapScore.lean` | 14 | 17 |
| `AmbidextrousSofa/Measure/Fibers.lean` | 31 | 34 |
| `AmbidextrousSofa/Measure/GraphIntegral.lean` | 7 | 8 |
| `AmbidextrousSofa/Measure/Partition.lean` | 23 | 26 |
| `AmbidextrousSofa/Measure/RigidInvariance.lean` | 11 | 12 |
| `AmbidextrousSofa/Measure/SignedRoof.lean` | 23 | 23 |
| `AmbidextrousSofa/Measure/SignedRoofIntegral.lean` | 16 | 23 |
| `AmbidextrousSofa/Measure/StripBounds.lean` | 11 | 13 |
| `AmbidextrousSofa/Measure/SupportArea.lean` | 11 | 20 |
| `AmbidextrousSofa/Measure/SymmetricBody.lean` | 8 | 9 |
| `AmbidextrousSofa/Reference/Body.lean` | 29 | 32 |
| `AmbidextrousSofa/Reference/Faces.lean` | 21 | 24 |
| `AmbidextrousSofa/Reference/Hull.lean` | 31 | 36 |
| `AmbidextrousSofa/Reference/Momenta.lean` | 16 | 18 |
| `AmbidextrousSofa/Reference/Niche.lean` | 24 | 27 |
| `AmbidextrousSofa/Reference/Parameters.lean` | 27 | 34 |
| `AmbidextrousSofa/Reference/Realization.lean` | 38 | 45 |
| `AmbidextrousSofa/Reference/Regularity.lean` | 13 | 14 |
| `AmbidextrousSofa/Reference/Stationarity.lean` | 15 | 20 |
| `AmbidextrousSofa/Reference/Support.lean` | 58 | 74 |
| `AmbidextrousSofa/Reference/Value.lean` | 45 | 48 |
| `AmbidextrousSofa/Topology/RegularClosed.lean` | 3 | 3 |

[mathlib]: https://github.com/leanprover-community/mathlib4/tree/c55e6e786f49471c72fbddbec5415808896aec1e
[research]: https://github.com/vltanh/lean4-moving-sofa/commit/20489723dc8777a82ee70ae60510115dc6f21085
