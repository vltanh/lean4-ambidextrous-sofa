# Detailed roadmap for the uncompiled F7 draft

## Deliverable and publication policy

The current task is to supply a complete **uncompiled Lean source draft** of
optimality and exact uniqueness for the original ambidextrous sofa domain.
No Lean, Lake, toolchain, language server, build, axiom query, or CI execution
is part of this task. No admissions or additional axioms are permitted.

Following the user's instruction to commit more frequently, the work is
published in three coherent dependency stages. Basic source hygiene and
local-import completeness are checked before publication. A complete source
audit and kernel verification are deferred; this roadmap does not treat a
lexical check as proof verification.

| Publication stage | Source content | Current status |
| --- | --- | --- |
| 1. Actual source measures and individual proper-angle reduction | One joint source, four literal branches, actual RN densities, tangent bounds, graph residual, and fixed-cap terminal regime | Published |
| 2. Common occupation and tilted exclusion | Shared corner balance and budget, first/core saturation, explicit common coefficients, actual first-unit contradiction | Published in this checkpoint |
| 3. Original-domain final assembly | Full-cap rigidity, sharp cap bound, individual proper equality, area bound, exact rigid-image equality and attainment | Written; publication next |

## 1. Construct the actual source measures

1. Retain the selected finite angle/abscissa source measures and their single
   compact weak limit. Identify the angular marginal with actual curvature.
2. Prove horizontal domination of the sine-weighted spatial marginal, exact
   spatial flux on positive niche intervals, and null spatial/angle fibers.
3. Exclude dry and zero-height source mass using the first-unit geometry.
   Derive an actual niche derivative from the same measure and retain its
   horizontal and vertical graph residual identity.
4. Partition the measure into strict first tangent, first corner, strict
   companion tangent, and companion corner. Assign wall ties to the corner
   branches, and define every angular density by Radon--Nikodym differentiation
   of these literal restrictions.
5. Identify the sums with the actual first density and the translated actual
   companion density. Prove that the latter agrees almost everywhere with
   the cut-companion density, including the interval through the affine normal.

Exit condition: the branch densities belong to one actual cap and one joint
source limit. No independent occupation certificate is assumed.

Principal files: `JointSourceSpatial`, `JointSourceFlux`, `JointSourcePositive`,
`JointNicheDerivative`, `JointSourceDensity`, `JointSourceBranches`,
`JointBranchDensity`, `JointSourceAffine`, and `JointSourceNicheCalculus`.

## 2. Derive tangent and corner occupation

1. Transport the sine-weighted graph bound to each tangent branch. Prove
   `aB <= 1-u`; prove `aD <= max(1-v,0)` and zero companion tangent mass on
   excess and below the floor. Prove zero first tangent mass outside the
   open middle window.
2. At a differentiable positive strict first contact, prove that its first
   angle is the unique possible source angle. The slope bounds and monotone
   first tangent exclude competing corner/companion sources.
3. Transfer exact horizontal length on charged first tangent images to
   `aB=1-u`. Retain monotone plateaus and their zero velocity.
4. Localize both actual corner branches to the open opposite-sign phase.
   The actual core abscissa is strictly decreasing there.
5. Cancel the signed residuals of the two corner restrictions against every
   spatial test. Pull that common cancellation back along the core graph
   to obtain `p*aZ + q*aW = 0`.
6. Bound their shared horizontal projection by the actual core speed.
   At a uniquely exposed positive core contact, replace domination by
   equality and obtain `aZ=q` and `aW=-p`.
7. Define measurable clipped ratios for `b`, `delta`, and one shared `chi`.
   Retain the value one at charged zero-speed first contacts. Derive
   `u=(1-u)*b+q*chi` and `v=(1-v)*delta-p*chi`, with the required bounds,
   first-contact flag, unique-core flag, and companion-shadow flags.

Exit condition: `exists_common_source_occupation_of_phases` constructs all
coefficients and flags from natural actual-cap and actual-density inputs.

Principal files: `JointFirstTangentDensity`, `JointCompanionTangentDensity`,
`FirstTangentExclusivity`, `JointFirstTangentExclusivity`,
`JointFirstTangentSaturation`, `JointCoreSourceGeometry`, `JointCoreFlux`,
`JointCoreProjection`, `JointCoreProjectionEquality`, `JointCoreVisibility`,
`CommonSourceCoefficients`, and `JointCommonOccupation`.

## 3. Close the actual tilted-cap contradiction

1. Derive the centered width, height-drop, positive-slope and small-parameter
   bounds from the prescribed full maximum.
2. Select its actual sharp curvature representative with the first-unit
   bound. Construct actual phase zeros and the common joint source.
3. Apply the occupation law to the already written event, first-floor,
   moment, source-sector, and fold-budget contradictions in both event orders.
4. Expose `IsFullCapMaximizer.false_of_positive_tilt` with only the centered
   height-one full maximum and its positive affine middle slope as premises.

Exit condition: the public tilted-exclusion theorem contains no occupation,
phase, visibility, fold, moment, or numerical certificate premise.

Principal files: `CanonicalTiltParameters`, `TiltedUnitSelection`,
`FirstUnitEventSelection`, `FirstUnitOccupationClosure`, and `TiltedCapExclusion`.

## 4. Classify every full and proper equality cap

1. Reflect negative slopes and use the positive-tilt contradiction to force
   zero slope. Apply the existing horizontal rigidity theorem.
2. Recover the original full maximum from its concrete height-saturated
   canonical cap. Obtain exact equality to a horizontal translate of the
   reference cap and the score `M/2`.
3. Use the completed largest-angle value reduction to prove the universal
   non-strict cap bound on every angle in `[pi/4,pi/2]`.
4. Apply the fixed-cap terminal extension and interior-atom argument to each
   individual proper equality cap. The generalized `ProperTailRegime` removes
   the largest-angle premise from that individual argument.
5. Use full-cap rigidity to exclude the negative completion case. Conclude
   that each joint equality cap has full angle and is a reference translate.

Exit condition: `capScore_eq_half_M_iff` classifies each prescribed equality
cap, rather than only one chosen largest-angle maximum.

Principal files: `TerminalFacetAtom`, `ProperTailRegime`,
`ProperAngleStrictness`, `FullCapRigidity`, `SharpCapBound`, and `SharpCapEquality`.

## 5. Assemble the original-domain theorem

1. Normalize the original two independent continuous rigid passages, retaining
   their independent effective angles, unrestricted terminal behavior, and
   any backtracking permitted by the original definition.
2. Apply the universal bound to both actual caps in the physical area deficit.
   Deal with the strict small-area alternative using `sqrt(2)<M`.
3. At equality, force both actual cap scores to equal `M/2`. Their individual
   classifications force full angles and aligned reference-cap translates.
4. Recover the literal compact body, including its boundary, from the actual
   caps. Invert the initial rigid normalization.
5. Supply the converse and attainment from the existing feasible reference
   sofa and its exact area.

Exit declarations in `AmbidextrousSofa/Theorems/Optimality.lean`:

- `IsAmbidextrous.volumeReal_le_M`;
- `IsAmbidextrous.eq_rigidImage_referenceSofa_of_volumeReal_eq`;
- `IsAmbidextrous.volumeReal_eq_M_iff`;
- `isGreatest_ambidextrous_areas`.

Their only body hypothesis is the unchanged original `IsAmbidextrous S`;
the equality implication additionally assumes its actual area is `M`.

## 6. Completion boundary and deferred work

The uncompiled F7 deliverable is the complete source chain through those
declarations, published in the draft PR. Source policy rejects admissions,
custom axioms, unsafe/native proof shortcuts, and CI configuration. Prepared
`#print axioms` commands are text only and are not executed.

Full independent mathematical/source auditing is a later pass, as requested.
Successful elaboration and a kernel-reported transitive axiom list have not
been established. The intended foundational allowlist remains `propext`,
`Classical.choice`, and `Quot.sound`. None of these deferred items is a reason
to withhold the requested uncompiled draft.
