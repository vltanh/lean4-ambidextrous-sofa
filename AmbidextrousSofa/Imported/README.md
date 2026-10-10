# Retained ordinary moving-sofa source

The ambidextrous manuscript uses the rational ordinary moving-sofa upper
bound `22199 / 10000` in auxiliary strict exclusions. This draft discharges
that input through the complete project import closure of
`MovingSofaOptimality/Main.lean` at revision
`20489723dc8777a82ee70ae60510115dc6f21085` of
[vltanh/lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa/tree/20489723dc8777a82ee70ae60510115dc6f21085).

The closure contains 51 source modules. It includes the proved existence
of Gerver's parameters, rational parameter and area enclosures, actual
motion reductions, cap maximization and the ordinary optimality argument.
Only this closure is copied: the original uniqueness, challenge and bridge
libraries are not dependencies. The original Apache-2.0 license is retained
as [LICENSE-lean4-moving-sofa](LICENSE-lean4-moving-sofa).

## Exact adaptation

The project namespace changes from `MovingSofaOptimality` to
`AmbidextrousSofa.Imported`. Project import paths change accordingly; the
four previously adapted basic convex-body/Stieltjes modules are reused at
their existing paths. The `module` declaration is omitted, imports become
ordinary imports, and the exposed public section becomes a noncomputable
section. Previously private helpers are public with their original local
names; the complete namespace inventory found no duplicate declarations.
The surface-area measure instance has the explicit name
`sigma_isLocallyFiniteMeasure` for the prepared audit.

No mathematical premise, definition or proof step is added to these
adapted modules. Each file records the original path and revision. The
source guard checks their imports, explicit declaration names, prohibited
trust tokens and prepared audit coverage together with the new source.

The separate [OrdinarySofaBound](../Analysis/OrdinarySofaBound.lean) bridge
identifies the coordinate rotations, hallway arms, ordinary area and
continuous real-angle movement predicates. It obtains the rational bound
for any actual compact connected lower passage, rebasing the initial body
orientation through an area-preserving rigid map. Both Gerver existence
conditions are discharged by the imported existence theorem.

## Verification limits

All adapted and bridge source remains uncompiled. The import closure and
textual transformation were checked, and the bridge theorem was inspected
at source level. This record does not claim a new independent review of
all 40,311 original source lines, successful elaboration or a transitive
kernel axiom audit. The permitted foundational axioms remain `propext`,
`Classical.choice` and `Quot.sound`. No CI is introduced or run.

## Source map

| Original path | Local path | Explicit declarations |
| --- | --- | ---: |
| `MovingSofaOptimality/Angle/HorizontalSide.lean` | [Angle/HorizontalSide.lean](Angle/HorizontalSide.lean) | 69 |
| `MovingSofaOptimality/Angle/RightAngle.lean` | [Angle/RightAngle.lean](Angle/RightAngle.lean) | 50 |
| `MovingSofaOptimality/Balanced/BalancedMaximumSofa.lean` | [Balanced/BalancedMaximumSofa.lean](Balanced/BalancedMaximumSofa.lean) | 25 |
| `MovingSofaOptimality/Balanced/CapGeometry.lean` | [Balanced/CapGeometry.lean](Balanced/CapGeometry.lean) | 86 |
| `MovingSofaOptimality/Balanced/MaxPolygonCapExists.lean` | [Balanced/MaxPolygonCapExists.lean](Balanced/MaxPolygonCapExists.lean) | 47 |
| `MovingSofaOptimality/Balanced/MaximumPolygonCap.lean` | [Balanced/MaximumPolygonCap.lean](Balanced/MaximumPolygonCap.lean) | 50 |
| `MovingSofaOptimality/Balanced/NefPolygon.lean` | [Balanced/NefPolygon.lean](Balanced/NefPolygon.lean) | 50 |
| `MovingSofaOptimality/Balanced/PolygonCap.lean` | [Balanced/PolygonCap.lean](Balanced/PolygonCap.lean) | 77 |
| `MovingSofaOptimality/Balanced/Polyline.lean` | [Balanced/Polyline.lean](Balanced/Polyline.lean) | 53 |
| `MovingSofaOptimality/Basic/ConvexBody.lean` | [ConvexBody.lean](ConvexBody.lean) | 78 |
| `MovingSofaOptimality/Basic/Interval.lean` | [Basic/Interval.lean](Basic/Interval.lean) | 22 |
| `MovingSofaOptimality/Basic/LebesgueStieltjes.lean` | [LebesgueStieltjes.lean](LebesgueStieltjes.lean) | 42 |
| `MovingSofaOptimality/Basic/Plane.lean` | [Plane.lean](Plane.lean) | 133 |
| `MovingSofaOptimality/Basic/SurfaceArea.lean` | [SurfaceArea.lean](SurfaceArea.lean) | 41 |
| `MovingSofaOptimality/Convex/ConvexCurve.lean` | [Convex/ConvexCurve.lean](Convex/ConvexCurve.lean) | 82 |
| `MovingSofaOptimality/Convex/ConvexDomain.lean` | [Convex/ConvexDomain.lean](Convex/ConvexDomain.lean) | 36 |
| `MovingSofaOptimality/Convex/CurveArea.lean` | [Convex/CurveArea.lean](Convex/CurveArea.lean) | 55 |
| `MovingSofaOptimality/Convex/Mamikon.lean` | [Convex/Mamikon.lean](Convex/Mamikon.lean) | 18 |
| `MovingSofaOptimality/External/AreaFormula.lean` | [External/AreaFormula.lean](External/AreaFormula.lean) | 39 |
| `MovingSofaOptimality/External/AreaFormula/Param.lean` | [External/AreaFormula/Param.lean](External/AreaFormula/Param.lean) | 44 |
| `MovingSofaOptimality/External/Romik.lean` | [External/Romik.lean](External/Romik.lean) | 38 |
| `MovingSofaOptimality/External/Romik/Calc.lean` | [External/Romik/Calc.lean](External/Romik/Calc.lean) | 15 |
| `MovingSofaOptimality/External/Romik/Fix.lean` | [External/Romik/Fix.lean](External/Romik/Fix.lean) | 19 |
| `MovingSofaOptimality/External/Romik/Num.lean` | [External/Romik/Num.lean](External/Romik/Num.lean) | 123 |
| `MovingSofaOptimality/Gerver/AreaBounds.lean` | [Gerver/AreaBounds.lean](Gerver/AreaBounds.lean) | 120 |
| `MovingSofaOptimality/Gerver/Bounds.lean` | [Gerver/Bounds.lean](Gerver/Bounds.lean) | 1 |
| `MovingSofaOptimality/Gerver/Defs.lean` | [Gerver/Defs.lean](Gerver/Defs.lean) | 15 |
| `MovingSofaOptimality/Gerver/Envelope.lean` | [Gerver/Envelope.lean](Gerver/Envelope.lean) | 52 |
| `MovingSofaOptimality/Gerver/EnvelopeArea.lean` | [Gerver/EnvelopeArea.lean](Gerver/EnvelopeArea.lean) | 30 |
| `MovingSofaOptimality/Gerver/Frame.lean` | [Gerver/Frame.lean](Gerver/Frame.lean) | 191 |
| `MovingSofaOptimality/Gerver/Niche.lean` | [Gerver/Niche.lean](Gerver/Niche.lean) | 30 |
| `MovingSofaOptimality/Gerver/NicheBounds.lean` | [Gerver/NicheBounds.lean](Gerver/NicheBounds.lean) | 43 |
| `MovingSofaOptimality/Gerver/Properties.lean` | [Gerver/Properties.lean](Gerver/Properties.lean) | 149 |
| `MovingSofaOptimality/Gerver/Structure.lean` | [Gerver/Structure.lean](Gerver/Structure.lean) | 6 |
| `MovingSofaOptimality/Gerver/StructureCap.lean` | [Gerver/StructureCap.lean](Gerver/StructureCap.lean) | 90 |
| `MovingSofaOptimality/Injectivity/ArmLengths.lean` | [Injectivity/ArmLengths.lean](Injectivity/ArmLengths.lean) | 45 |
| `MovingSofaOptimality/Injectivity/BoundingArms.lean` | [Injectivity/BoundingArms.lean](Injectivity/BoundingArms.lean) | 21 |
| `MovingSofaOptimality/Injectivity/DiscreteIneq.lean` | [Injectivity/DiscreteIneq.lean](Injectivity/DiscreteIneq.lean) | 50 |
| `MovingSofaOptimality/Injectivity/LimitIneq.lean` | [Injectivity/LimitIneq.lean](Injectivity/LimitIneq.lean) | 42 |
| `MovingSofaOptimality/Intro/RotationAngleBound.lean` | [Intro/RotationAngleBound.lean](Intro/RotationAngleBound.lean) | 12 |
| `MovingSofaOptimality/Main.lean` | [Main.lean](Main.lean) | 16 |
| `MovingSofaOptimality/Monotone/CapContainsNiche.lean` | [Monotone/CapContainsNiche.lean](Monotone/CapContainsNiche.lean) | 96 |
| `MovingSofaOptimality/Monotone/CapDefs.lean` | [Monotone/CapDefs.lean](Monotone/CapDefs.lean) | 26 |
| `MovingSofaOptimality/Monotone/CapNiche.lean` | [Monotone/CapNiche.lean](Monotone/CapNiche.lean) | 8 |
| `MovingSofaOptimality/Monotone/MonotoneSofa.lean` | [Monotone/MonotoneSofa.lean](Monotone/MonotoneSofa.lean) | 42 |
| `MovingSofaOptimality/Monotone/SupportingHallway.lean` | [Monotone/SupportingHallway.lean](Monotone/SupportingHallway.lean) | 33 |
| `MovingSofaOptimality/Optimality/Concavity.lean` | [Optimality/Concavity.lean](Optimality/Concavity.lean) | 50 |
| `MovingSofaOptimality/Optimality/Domain.lean` | [Optimality/Domain.lean](Optimality/Domain.lean) | 71 |
| `MovingSofaOptimality/Optimality/UpperBound.lean` | [Optimality/UpperBound.lean](Optimality/UpperBound.lean) | 56 |
| `MovingSofaOptimality/Optimality/Variation.lean` | [Optimality/Variation.lean](Optimality/Variation.lean) | 34 |
| `MovingSofaOptimality/Sofa/Defs.lean` | [Sofa/Defs.lean](Sofa/Defs.lean) | 41 |
