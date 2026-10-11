module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the library and of the copied `MovingSofaOptimality`, so that
-- proofs are visible to the dependency traversal and the axiom check (the module system hides them
-- from a plain `import`). Generate the lines with
--   find AmbidextrousSofa MovingSofaOptimality -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all AmbidextrousSofa.Algebra.Deficit
import all AmbidextrousSofa.Analysis.AdaptiveFunctional
import all AmbidextrousSofa.Analysis.AdaptiveGlobalBoundary
import all AmbidextrousSofa.Analysis.AdaptiveGlobalBranches
import all AmbidextrousSofa.Analysis.AdaptiveGlobalComparison
import all AmbidextrousSofa.Analysis.AdaptiveGlobalFamily
import all AmbidextrousSofa.Analysis.AdaptiveGlobalMomenta
import all AmbidextrousSofa.Analysis.AdaptiveGlobalParameters
import all AmbidextrousSofa.Analysis.AdaptiveGlobalScalar
import all AmbidextrousSofa.Analysis.AdaptiveGlobalValue
import all AmbidextrousSofa.Analysis.AdaptiveTranslation
import all AmbidextrousSofa.Analysis.AffineNormal
import all AmbidextrousSofa.Analysis.AngularFluxLimit
import all AmbidextrousSofa.Analysis.AsymmetricTent
import all AmbidextrousSofa.Analysis.AtomIntervalLimit
import all AmbidextrousSofa.Analysis.AxisFaces
import all AmbidextrousSofa.Analysis.AxisHeightLimit
import all AmbidextrousSofa.Analysis.AxisVariation
import all AmbidextrousSofa.Analysis.BoxedSecants
import all AmbidextrousSofa.Analysis.CanonicalOneTurn
import all AmbidextrousSofa.Analysis.CanonicalTiltParameters
import all AmbidextrousSofa.Analysis.CanonicalWingChord
import all AmbidextrousSofa.Analysis.CapCompactness
import all AmbidextrousSofa.Analysis.CapInsertion
import all AmbidextrousSofa.Analysis.CapInteriorRoof
import all AmbidextrousSofa.Analysis.CapMaximum
import all AmbidextrousSofa.Analysis.CapNicheContinuity
import all AmbidextrousSofa.Analysis.CapNormalization
import all AmbidextrousSofa.Analysis.CapOrder
import all AmbidextrousSofa.Analysis.CapReflection
import all AmbidextrousSofa.Analysis.CapRoofConvergence
import all AmbidextrousSofa.Analysis.CapScoreContinuity
import all AmbidextrousSofa.Analysis.CapTranslation
import all AmbidextrousSofa.Analysis.CapVolumeContinuity
import all AmbidextrousSofa.Analysis.Chord
import all AmbidextrousSofa.Analysis.CircleAverage
import all AmbidextrousSofa.Analysis.Circumscription
import all AmbidextrousSofa.Analysis.ClippedTailIntegral
import all AmbidextrousSofa.Analysis.ClosedSupportPair
import all AmbidextrousSofa.Analysis.CommonSourceCoefficients
import all AmbidextrousSofa.Analysis.CompanionBaseline
import all AmbidextrousSofa.Analysis.CompanionEndpointEnergy
import all AmbidextrousSofa.Analysis.CompanionEndpointKernel
import all AmbidextrousSofa.Analysis.CompanionFloorShadow
import all AmbidextrousSofa.Analysis.CompanionZero
import all AmbidextrousSofa.Analysis.ContactGraphSlope
import all AmbidextrousSofa.Analysis.ContactSlopeBounds
import all AmbidextrousSofa.Analysis.CoreContactGeometry
import all AmbidextrousSofa.Analysis.CoreContactPhase
import all AmbidextrousSofa.Analysis.CoreSourceLowerBounds
import all AmbidextrousSofa.Analysis.CornerArcCrossing
import all AmbidextrousSofa.Analysis.CornerArcExcess
import all AmbidextrousSofa.Analysis.CornerConfinement
import all AmbidextrousSofa.Analysis.CornerCrossing
import all AmbidextrousSofa.Analysis.CornerDynamics
import all AmbidextrousSofa.Analysis.CornerEndpointEnergy
import all AmbidextrousSofa.Analysis.CornerEnergy
import all AmbidextrousSofa.Analysis.CornerPropagation
import all AmbidextrousSofa.Analysis.CornerSignPhases
import all AmbidextrousSofa.Analysis.CornerThreshold
import all AmbidextrousSofa.Analysis.CornerTrigonometry
import all AmbidextrousSofa.Analysis.DiagonalComparisonScore
import all AmbidextrousSofa.Analysis.DiagonalCutTriangles
import all AmbidextrousSofa.Analysis.DiagonalDeficit
import all AmbidextrousSofa.Analysis.DiagonalLowHeight
import all AmbidextrousSofa.Analysis.DiagonalRelaxation
import all AmbidextrousSofa.Analysis.DiagonalScalar
import all AmbidextrousSofa.Analysis.DiagonalTent
import all AmbidextrousSofa.Analysis.DirichletEnergy
import all AmbidextrousSofa.Analysis.DiscreteCurvature
import all AmbidextrousSofa.Analysis.DrySourceProjection
import all AmbidextrousSofa.Analysis.DryTopBalance
import all AmbidextrousSofa.Analysis.DyadicCurvatureMass
import all AmbidextrousSofa.Analysis.DyadicGrid
import all AmbidextrousSofa.Analysis.DyadicNeighbors
import all AmbidextrousSofa.Analysis.EndpointComplementarity
import all AmbidextrousSofa.Analysis.EndpointPolygons
import all AmbidextrousSofa.Analysis.EndpointPositivity
import all AmbidextrousSofa.Analysis.EndpointPressure
import all AmbidextrousSofa.Analysis.EndpointTrimming
import all AmbidextrousSofa.Analysis.ErosionMoments
import all AmbidextrousSofa.Analysis.ErosionVariation
import all AmbidextrousSofa.Analysis.EulerFlux
import all AmbidextrousSofa.Analysis.ExactEstimates
import all AmbidextrousSofa.Analysis.ExposureMoments
import all AmbidextrousSofa.Analysis.Extrusion
import all AmbidextrousSofa.Analysis.FacetCurvature
import all AmbidextrousSofa.Analysis.FacetPinning
import all AmbidextrousSofa.Analysis.FiniteEnvelope
import all AmbidextrousSofa.Analysis.FiniteGraphFlux
import all AmbidextrousSofa.Analysis.FiniteGraphGreen
import all AmbidextrousSofa.Analysis.FiniteGraphLength
import all AmbidextrousSofa.Analysis.FiniteHorizontalMoment
import all AmbidextrousSofa.Analysis.FiniteNicheOscillation
import all AmbidextrousSofa.Analysis.FiniteRoofVariation
import all AmbidextrousSofa.Analysis.FiniteScore
import all AmbidextrousSofa.Analysis.FiniteSourceBalance
import all AmbidextrousSofa.Analysis.FiniteSpatialVariation
import all AmbidextrousSofa.Analysis.FiniteVariation
import all AmbidextrousSofa.Analysis.FirstFloorOrder
import all AmbidextrousSofa.Analysis.FirstFloorTrapping
import all AmbidextrousSofa.Analysis.FirstFloorVisibility
import all AmbidextrousSofa.Analysis.FirstSourceDensity
import all AmbidextrousSofa.Analysis.FirstSourceFlux
import all AmbidextrousSofa.Analysis.FirstTangentExclusivity
import all AmbidextrousSofa.Analysis.FirstUnitBadEntry
import all AmbidextrousSofa.Analysis.FirstUnitCrossings
import all AmbidextrousSofa.Analysis.FirstUnitEventSelection
import all AmbidextrousSofa.Analysis.FirstUnitFoldBudget
import all AmbidextrousSofa.Analysis.FirstUnitGeometricMoments
import all AmbidextrousSofa.Analysis.FirstUnitLateWindowClosure
import all AmbidextrousSofa.Analysis.FirstUnitNiche
import all AmbidextrousSofa.Analysis.FirstUnitOccupationClosure
import all AmbidextrousSofa.Analysis.FirstUnitOccupationGeometry
import all AmbidextrousSofa.Analysis.FirstUnitPhases
import all AmbidextrousSofa.Analysis.FirstUnitPrefixEnergy
import all AmbidextrousSofa.Analysis.FirstUnitProjection
import all AmbidextrousSofa.Analysis.FirstUnitSourceSectors
import all AmbidextrousSofa.Analysis.FirstUnitTangency
import all AmbidextrousSofa.Analysis.FirstUnitTopOverhang
import all AmbidextrousSofa.Analysis.FloorContactCurvature
import all AmbidextrousSofa.Analysis.FullCapRecovery
import all AmbidextrousSofa.Analysis.FullCapRigidity
import all AmbidextrousSofa.Analysis.FullTriangleArea
import all AmbidextrousSofa.Analysis.FullTriangleFloor
import all AmbidextrousSofa.Analysis.FullTriangleParameters
import all AmbidextrousSofa.Analysis.FullTriangleScalar
import all AmbidextrousSofa.Analysis.FullTriangleWidth
import all AmbidextrousSofa.Analysis.FullWidthCeiling
import all AmbidextrousSofa.Analysis.FullWidthGap
import all AmbidextrousSofa.Analysis.GlobalCapMaximum
import all AmbidextrousSofa.Analysis.GridCounting
import all AmbidextrousSofa.Analysis.GridNiche
import all AmbidextrousSofa.Analysis.GridPolygon
import all AmbidextrousSofa.Analysis.GridScore
import all AmbidextrousSofa.Analysis.GridSeparation
import all AmbidextrousSofa.Analysis.HorizontalCalibration
import all AmbidextrousSofa.Analysis.HorizontalClassification
import all AmbidextrousSofa.Analysis.HorizontalCutoff
import all AmbidextrousSofa.Analysis.HorizontalEndpointBounds
import all AmbidextrousSofa.Analysis.HorizontalEndpointKernel
import all AmbidextrousSofa.Analysis.HorizontalLeakageBound
import all AmbidextrousSofa.Analysis.HorizontalLeakageDynamics
import all AmbidextrousSofa.Analysis.HorizontalLeakageIntegral
import all AmbidextrousSofa.Analysis.HorizontalLeakageOccupation
import all AmbidextrousSofa.Analysis.HorizontalLeakageScalar
import all AmbidextrousSofa.Analysis.HorizontalNicheConfinement
import all AmbidextrousSofa.Analysis.HorizontalNicheGraphs
import all AmbidextrousSofa.Analysis.HorizontalOrdinaryArea
import all AmbidextrousSofa.Analysis.HorizontalRigidity
import all AmbidextrousSofa.Analysis.HorizontalSignedArea
import all AmbidextrousSofa.Analysis.HorizontalSupportArea
import all AmbidextrousSofa.Analysis.HorizontalTopFacet
import all AmbidextrousSofa.Analysis.HorizontalUnitCurvature
import all AmbidextrousSofa.Analysis.HorizontalWidthReduction
import all AmbidextrousSofa.Analysis.HorizontalWindowLimit
import all AmbidextrousSofa.Analysis.InactiveNormals
import all AmbidextrousSofa.Analysis.InitialAngleBound
import all AmbidextrousSofa.Analysis.InitialAngleCalibration
import all AmbidextrousSofa.Analysis.InitialAngleCritical
import all AmbidextrousSofa.Analysis.InitialAngleExclusion
import all AmbidextrousSofa.Analysis.InitialAngleRaise
import all AmbidextrousSofa.Analysis.InitialAngleRelaxation
import all AmbidextrousSofa.Analysis.InitialAngleScalar
import all AmbidextrousSofa.Analysis.InitialAngleWidth
import all AmbidextrousSofa.Analysis.IntermediateTilt
import all AmbidextrousSofa.Analysis.InverseCanonicalization
import all AmbidextrousSofa.Analysis.JointBranchDensity
import all AmbidextrousSofa.Analysis.JointBranchIntegrals
import all AmbidextrousSofa.Analysis.JointBranchProjection
import all AmbidextrousSofa.Analysis.JointCapMaximum
import all AmbidextrousSofa.Analysis.JointCommonOccupation
import all AmbidextrousSofa.Analysis.JointCompanionTangentDensity
import all AmbidextrousSofa.Analysis.JointCoreFlux
import all AmbidextrousSofa.Analysis.JointCoreProjection
import all AmbidextrousSofa.Analysis.JointCoreProjectionEquality
import all AmbidextrousSofa.Analysis.JointCoreSourceGeometry
import all AmbidextrousSofa.Analysis.JointCoreVisibility
import all AmbidextrousSofa.Analysis.JointFirstTangentDensity
import all AmbidextrousSofa.Analysis.JointFirstTangentExclusivity
import all AmbidextrousSofa.Analysis.JointFirstTangentSaturation
import all AmbidextrousSofa.Analysis.JointNicheDerivative
import all AmbidextrousSofa.Analysis.JointSourceAffine
import all AmbidextrousSofa.Analysis.JointSourceBranches
import all AmbidextrousSofa.Analysis.JointSourceContactLimit
import all AmbidextrousSofa.Analysis.JointSourceContacts
import all AmbidextrousSofa.Analysis.JointSourceDensity
import all AmbidextrousSofa.Analysis.JointSourceFlux
import all AmbidextrousSofa.Analysis.JointSourceLimit
import all AmbidextrousSofa.Analysis.JointSourceMarginal
import all AmbidextrousSofa.Analysis.JointSourceMeasure
import all AmbidextrousSofa.Analysis.JointSourceNicheCalculus
import all AmbidextrousSofa.Analysis.JointSourcePositive
import all AmbidextrousSofa.Analysis.JointSourceSpatial
import all AmbidextrousSofa.Analysis.LeftCompanionCap
import all AmbidextrousSofa.Analysis.LeftCompanionCurvature
import all AmbidextrousSofa.Analysis.LeftCompanionDensity
import all AmbidextrousSofa.Analysis.LevelSetDerivative
import all AmbidextrousSofa.Analysis.LocalSourceDensity
import all AmbidextrousSofa.Analysis.LowHeightAlgebra
import all AmbidextrousSofa.Analysis.LowHeightGeometry
import all AmbidextrousSofa.Analysis.LowHeightMaximizer
import all AmbidextrousSofa.Analysis.LowHeightScore
import all AmbidextrousSofa.Analysis.MiddleFacetBounds
import all AmbidextrousSofa.Analysis.MiddleMassLimit
import all AmbidextrousSofa.Analysis.MiddleNormalStability
import all AmbidextrousSofa.Analysis.MovingSupportSecants
import all AmbidextrousSofa.Analysis.NearDiagonalGeometry
import all AmbidextrousSofa.Analysis.NearDiagonalTail
import all AmbidextrousSofa.Analysis.NearDiagonalWalls
import all AmbidextrousSofa.Analysis.NegativeCompletion
import all AmbidextrousSofa.Analysis.NegativeCornerCurvature
import all AmbidextrousSofa.Analysis.NeighborCompanion
import all AmbidextrousSofa.Analysis.NeighborLength
import all AmbidextrousSofa.Analysis.NeighborShadowing
import all AmbidextrousSofa.Analysis.NeighborWalls
import all AmbidextrousSofa.Analysis.NicheBoxBounds
import all AmbidextrousSofa.Analysis.NicheFit
import all AmbidextrousSofa.Analysis.NichePositiveMiddle
import all AmbidextrousSofa.Analysis.NicheWings
import all AmbidextrousSofa.Analysis.NonpositiveCornerCurvature
import all AmbidextrousSofa.Analysis.NormalTrimming
import all AmbidextrousSofa.Analysis.OneTurnArea
import all AmbidextrousSofa.Analysis.OneTurnSurvivor
import all AmbidextrousSofa.Analysis.OpenGraphFlux
import all AmbidextrousSofa.Analysis.OpenWingCurvature
import all AmbidextrousSofa.Analysis.OrdinarySofaBound
import all AmbidextrousSofa.Analysis.PartialAtomIntervalLimit
import all AmbidextrousSofa.Analysis.PartialAxisCurvature
import all AmbidextrousSofa.Analysis.PartialAxisHeightLimit
import all AmbidextrousSofa.Analysis.PartialCapContinuity
import all AmbidextrousSofa.Analysis.PartialCurvatureDensity
import all AmbidextrousSofa.Analysis.PartialCurvatureIntervals
import all AmbidextrousSofa.Analysis.PartialEndpointComplementarity
import all AmbidextrousSofa.Analysis.PartialEndpointMoments
import all AmbidextrousSofa.Analysis.PartialEndpointPositivity
import all AmbidextrousSofa.Analysis.PartialErosionMoments
import all AmbidextrousSofa.Analysis.PartialFacetPinning
import all AmbidextrousSofa.Analysis.PartialGridNiche
import all AmbidextrousSofa.Analysis.PartialGridPolygon
import all AmbidextrousSofa.Analysis.PartialGridScore
import all AmbidextrousSofa.Analysis.PartialHorizontalCutoff
import all AmbidextrousSofa.Analysis.PartialHorizontalMoment
import all AmbidextrousSofa.Analysis.PartialInactiveNormals
import all AmbidextrousSofa.Analysis.PartialLowHeight
import all AmbidextrousSofa.Analysis.PartialNegativeCornerCurvature
import all AmbidextrousSofa.Analysis.PartialNeighborLength
import all AmbidextrousSofa.Analysis.PartialNeighborShadowing
import all AmbidextrousSofa.Analysis.PartialNeighborWalls
import all AmbidextrousSofa.Analysis.PartialPressureLimit
import all AmbidextrousSofa.Analysis.PartialReflectedControls
import all AmbidextrousSofa.Analysis.PartialReflectedDynamics
import all AmbidextrousSofa.Analysis.PartialReflectedSupport
import all AmbidextrousSofa.Analysis.PartialRegularDomain
import all AmbidextrousSofa.Analysis.PartialSelectedCurvature
import all AmbidextrousSofa.Analysis.PartialSelectedSequence
import all AmbidextrousSofa.Analysis.PartialShadowCurvature
import all AmbidextrousSofa.Analysis.PartialShadowSecants
import all AmbidextrousSofa.Analysis.PartialSharpCurvatureDensity
import all AmbidextrousSofa.Analysis.PartialSharpSourceDensity
import all AmbidextrousSofa.Analysis.PartialSourceBalance
import all AmbidextrousSofa.Analysis.PartialSourceCounting
import all AmbidextrousSofa.Analysis.PartialSourceMass
import all AmbidextrousSofa.Analysis.PartialSourceVelocity
import all AmbidextrousSofa.Analysis.PartialTopInsertion
import all AmbidextrousSofa.Analysis.PartialTriangleScalar
import all AmbidextrousSofa.Analysis.PartialWidthBounds
import all AmbidextrousSofa.Analysis.PartialWingSupport
import all AmbidextrousSofa.Analysis.PersistentPenalty
import all AmbidextrousSofa.Analysis.PolygonEnvelope
import all AmbidextrousSofa.Analysis.PolygonExposure
import all AmbidextrousSofa.Analysis.PolygonVariation
import all AmbidextrousSofa.Analysis.PositiveNicheLimit
import all AmbidextrousSofa.Analysis.PositivePartCalculus
import all AmbidextrousSofa.Analysis.PositivePartialBarrierLimit
import all AmbidextrousSofa.Analysis.PositiveTent
import all AmbidextrousSofa.Analysis.PositiveWallContacts
import all AmbidextrousSofa.Analysis.ProperAngleStrictness
import all AmbidextrousSofa.Analysis.ProperExcessEnvelope
import all AmbidextrousSofa.Analysis.ProperExcessScalar
import all AmbidextrousSofa.Analysis.ProperReflectedEntry
import all AmbidextrousSofa.Analysis.ProperTailRegime
import all AmbidextrousSofa.Analysis.ProperTerminalExclusion
import all AmbidextrousSofa.Analysis.QuadraticEnergy
import all AmbidextrousSofa.Analysis.QuarterFunctions
import all AmbidextrousSofa.Analysis.RampCutIntegral
import all AmbidextrousSofa.Analysis.ReflectedExcessScalar
import all AmbidextrousSofa.Analysis.RegularCorner
import all AmbidextrousSofa.Analysis.RegularCurvatureDomain
import all AmbidextrousSofa.Analysis.RegularTangency
import all AmbidextrousSofa.Analysis.RoofContinuity
import all AmbidextrousSofa.Analysis.RoofGain
import all AmbidextrousSofa.Analysis.SelectedCurvature
import all AmbidextrousSofa.Analysis.SelectedEndpointMoments
import all AmbidextrousSofa.Analysis.SelectedErosionMoments
import all AmbidextrousSofa.Analysis.SelectedGreenLimit
import all AmbidextrousSofa.Analysis.SelectedHorizontalMoment
import all AmbidextrousSofa.Analysis.SelectedNicheHeight
import all AmbidextrousSofa.Analysis.SelectedPressureLimit
import all AmbidextrousSofa.Analysis.SelectedSequence
import all AmbidextrousSofa.Analysis.ShadowCurvature
import all AmbidextrousSofa.Analysis.ShadowSecants
import all AmbidextrousSofa.Analysis.SharpCapBound
import all AmbidextrousSofa.Analysis.SharpCapEquality
import all AmbidextrousSofa.Analysis.SharpCurvatureDensity
import all AmbidextrousSofa.Analysis.ShortTailGeometry
import all AmbidextrousSofa.Analysis.ShortWidthExclusion
import all AmbidextrousSofa.Analysis.ShortWidthPayment
import all AmbidextrousSofa.Analysis.SmallTiltArea
import all AmbidextrousSofa.Analysis.SmallTiltConstants
import all AmbidextrousSofa.Analysis.SmallTiltScalar
import all AmbidextrousSofa.Analysis.SourceLocalization
import all AmbidextrousSofa.Analysis.SourceOccupation
import all AmbidextrousSofa.Analysis.SourceVelocity
import all AmbidextrousSofa.Analysis.SplitWingChord
import all AmbidextrousSofa.Analysis.SupportCurvature
import all AmbidextrousSofa.Analysis.SupportDensityCalculus
import all AmbidextrousSofa.Analysis.SupportHeightControl
import all AmbidextrousSofa.Analysis.SurfaceAreaFacts
import all AmbidextrousSofa.Analysis.TangencyEndpoints
import all AmbidextrousSofa.Analysis.TangencyLoci
import all AmbidextrousSofa.Analysis.TangencyMeasurable
import all AmbidextrousSofa.Analysis.TangencyOrder
import all AmbidextrousSofa.Analysis.TerminalActualComparison
import all AmbidextrousSofa.Analysis.TerminalAngleDerivative
import all AmbidextrousSofa.Analysis.TerminalAngleIntegral
import all AmbidextrousSofa.Analysis.TerminalCircleEndpoints
import all AmbidextrousSofa.Analysis.TerminalCircleMargin
import all AmbidextrousSofa.Analysis.TerminalCompanionComparison
import all AmbidextrousSofa.Analysis.TerminalCompanionCurvature
import all AmbidextrousSofa.Analysis.TerminalCompanionLocalization
import all AmbidextrousSofa.Analysis.TerminalCompanionMoment
import all AmbidextrousSofa.Analysis.TerminalCorner
import all AmbidextrousSofa.Analysis.TerminalCubicPayment
import all AmbidextrousSofa.Analysis.TerminalExposure
import all AmbidextrousSofa.Analysis.TerminalExtension
import all AmbidextrousSofa.Analysis.TerminalFacet
import all AmbidextrousSofa.Analysis.TerminalFacetAtom
import all AmbidextrousSofa.Analysis.TerminalHistory
import all AmbidextrousSofa.Analysis.TerminalImpulseEnergy
import all AmbidextrousSofa.Analysis.TerminalLeftComparison
import all AmbidextrousSofa.Analysis.TerminalReflectedParameters
import all AmbidextrousSofa.Analysis.TerminalScalar
import all AmbidextrousSofa.Analysis.TerminalStrictComparison
import all AmbidextrousSofa.Analysis.TerminalSupportTails
import all AmbidextrousSofa.Analysis.TerminalThreeSupports
import all AmbidextrousSofa.Analysis.TerminalTopProjection
import all AmbidextrousSofa.Analysis.TerminalWallBound
import all AmbidextrousSofa.Analysis.ThreeAngleComparison
import all AmbidextrousSofa.Analysis.ThreeAngleDeficit
import all AmbidextrousSofa.Analysis.ThreeAngleNiche
import all AmbidextrousSofa.Analysis.ThreeAngleShortTail
import all AmbidextrousSofa.Analysis.ThreeAngleShortWidth
import all AmbidextrousSofa.Analysis.ThreeAngleTriangleWidth
import all AmbidextrousSofa.Analysis.ThreeAngleWideWidth
import all AmbidextrousSofa.Analysis.ThreeAngleWidth
import all AmbidextrousSofa.Analysis.TiltedCapExclusion
import all AmbidextrousSofa.Analysis.TiltedCrossingExcess
import all AmbidextrousSofa.Analysis.TiltedDiagonalRoof
import all AmbidextrousSofa.Analysis.TiltedEndpointBounds
import all AmbidextrousSofa.Analysis.TiltedEndpointLeakage
import all AmbidextrousSofa.Analysis.TiltedFirstUnitClosure
import all AmbidextrousSofa.Analysis.TiltedFirstUnitEnergy
import all AmbidextrousSofa.Analysis.TiltedFirstUnitMoments
import all AmbidextrousSofa.Analysis.TiltedFoldPayment
import all AmbidextrousSofa.Analysis.TiltedHarmonicMoments
import all AmbidextrousSofa.Analysis.TiltedInitialCircle
import all AmbidextrousSofa.Analysis.TiltedInitialEnergy
import all AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
import all AmbidextrousSofa.Analysis.TiltedInitialUnitRegions
import all AmbidextrousSofa.Analysis.TiltedLateExcess
import all AmbidextrousSofa.Analysis.TiltedLateExcessScalar
import all AmbidextrousSofa.Analysis.TiltedLeakageMoment
import all AmbidextrousSofa.Analysis.TiltedMomentumConvolution
import all AmbidextrousSofa.Analysis.TiltedReflectedControls
import all AmbidextrousSofa.Analysis.TiltedReflectedLateUnit
import all AmbidextrousSofa.Analysis.TiltedSupportControls
import all AmbidextrousSofa.Analysis.TiltedSupportPair
import all AmbidextrousSofa.Analysis.TiltedTopOverhang
import all AmbidextrousSofa.Analysis.TiltedTopProjection
import all AmbidextrousSofa.Analysis.TiltedTriangleArea
import all AmbidextrousSofa.Analysis.TiltedTriangleScalar
import all AmbidextrousSofa.Analysis.TiltedUnitSelection
import all AmbidextrousSofa.Analysis.TiltedWingSupport
import all AmbidextrousSofa.Analysis.TiltedZeroGeometry
import all AmbidextrousSofa.Analysis.TopFacetEndpoints
import all AmbidextrousSofa.Analysis.TopInsertion
import all AmbidextrousSofa.Analysis.UniqueWallContact
import all AmbidextrousSofa.Analysis.UnusedCurvature
import all AmbidextrousSofa.Analysis.UsedSupportSaturation
import all AmbidextrousSofa.Analysis.VisibleFluxDensity
import all AmbidextrousSofa.Analysis.VisibleGraphFlux
import all AmbidextrousSofa.Analysis.WallVisibility
import all AmbidextrousSofa.Analysis.WideCap
import all AmbidextrousSofa.Analysis.WideDiagonalGeometry
import all AmbidextrousSofa.Analysis.WideDiagonalScalar
import all AmbidextrousSofa.Analysis.WideGainScalar
import all AmbidextrousSofa.Analysis.WideNicheGeometry
import all AmbidextrousSofa.Analysis.WideNichePieces
import all AmbidextrousSofa.Analysis.WideSupportCuts
import all AmbidextrousSofa.Analysis.WideWidthExclusion
import all AmbidextrousSofa.Analysis.WingCurvatureDensity
import all AmbidextrousSofa.Analysis.WingCurvatureIntervals
import all AmbidextrousSofa.ChallengeDefs
import all AmbidextrousSofa.ExactConstant
import all AmbidextrousSofa.Geometry.AngularDomain
import all AmbidextrousSofa.Geometry.BarrierAnalysis
import all AmbidextrousSofa.Geometry.Barriers
import all AmbidextrousSofa.Geometry.CapGeometry
import all AmbidextrousSofa.Geometry.Caps
import all AmbidextrousSofa.Geometry.Hallway
import all AmbidextrousSofa.Geometry.HullCompact
import all AmbidextrousSofa.Geometry.MotionReduction
import all AmbidextrousSofa.Geometry.Motions
import all AmbidextrousSofa.Geometry.Plane
import all AmbidextrousSofa.Geometry.Reflection
import all AmbidextrousSofa.Geometry.RigidImage
import all AmbidextrousSofa.Geometry.RigidMotion
import all AmbidextrousSofa.Geometry.Support
import all AmbidextrousSofa.Geometry.UpwardSupport
import all AmbidextrousSofa.Main
import all AmbidextrousSofa.Measure.ActualReferenceRecovery
import all AmbidextrousSofa.Measure.CapAssembly
import all AmbidextrousSofa.Measure.CapScore
import all AmbidextrousSofa.Measure.ContactVariation
import all AmbidextrousSofa.Measure.Fibers
import all AmbidextrousSofa.Measure.FiniteMeasurePortmanteau
import all AmbidextrousSofa.Measure.GraphDensityDomination
import all AmbidextrousSofa.Measure.GraphDensitySaturation
import all AmbidextrousSofa.Measure.GraphIntegral
import all AmbidextrousSofa.Measure.GraphMeasureTransfer
import all AmbidextrousSofa.Measure.MonotoneGraphSaturation
import all AmbidextrousSofa.Measure.Partition
import all AmbidextrousSofa.Measure.RealRadonNikodym
import all AmbidextrousSofa.Measure.ReferenceOrbit
import all AmbidextrousSofa.Measure.RigidInvariance
import all AmbidextrousSofa.Measure.SignedRoof
import all AmbidextrousSofa.Measure.SignedRoofIntegral
import all AmbidextrousSofa.Measure.SignedRoofIntegralAC
import all AmbidextrousSofa.Measure.StripBounds
import all AmbidextrousSofa.Measure.SupportArea
import all AmbidextrousSofa.Measure.SupportAreaAC
import all AmbidextrousSofa.Measure.SymmetricBody
import all AmbidextrousSofa.Measure.WeightedFiniteMeasure
import all AmbidextrousSofa.Reference.Body
import all AmbidextrousSofa.Reference.Faces
import all AmbidextrousSofa.Reference.HorizontalSymmetry
import all AmbidextrousSofa.Reference.Hull
import all AmbidextrousSofa.Reference.Momenta
import all AmbidextrousSofa.Reference.Niche
import all AmbidextrousSofa.Reference.Parameters
import all AmbidextrousSofa.Reference.Realization
import all AmbidextrousSofa.Reference.Regularity
import all AmbidextrousSofa.Reference.Stationarity
import all AmbidextrousSofa.Reference.Support
import all AmbidextrousSofa.Reference.Value
import all AmbidextrousSofa.Theorems.Optimality
import all AmbidextrousSofa.Topology.RegularClosed
import all AmbidextrousSofa.Topology.VerticalRegion
import all MovingSofaOptimality.Angle.HorizontalSide
import all MovingSofaOptimality.Angle.RightAngle
import all MovingSofaOptimality.Balanced.BalancedMaximumSofa
import all MovingSofaOptimality.Balanced.CapGeometry
import all MovingSofaOptimality.Balanced.MaxPolygonCapExists
import all MovingSofaOptimality.Balanced.MaximumPolygonCap
import all MovingSofaOptimality.Balanced.NefPolygon
import all MovingSofaOptimality.Balanced.PolygonCap
import all MovingSofaOptimality.Balanced.Polyline
import all MovingSofaOptimality.Basic.ConvexBody
import all MovingSofaOptimality.Basic.Interval
import all MovingSofaOptimality.Basic.LebesgueStieltjes
import all MovingSofaOptimality.Basic.Plane
import all MovingSofaOptimality.Basic.SurfaceArea
import all MovingSofaOptimality.Convex.ConvexCurve
import all MovingSofaOptimality.Convex.ConvexDomain
import all MovingSofaOptimality.Convex.CurveArea
import all MovingSofaOptimality.Convex.Mamikon
import all MovingSofaOptimality.External.AreaFormula
import all MovingSofaOptimality.External.AreaFormula.Param
import all MovingSofaOptimality.External.Romik
import all MovingSofaOptimality.External.Romik.Calc
import all MovingSofaOptimality.External.Romik.Fix
import all MovingSofaOptimality.External.Romik.Num
import all MovingSofaOptimality.Gerver.AreaBounds
import all MovingSofaOptimality.Gerver.Bounds
import all MovingSofaOptimality.Gerver.Defs
import all MovingSofaOptimality.Gerver.Envelope
import all MovingSofaOptimality.Gerver.EnvelopeArea
import all MovingSofaOptimality.Gerver.Frame
import all MovingSofaOptimality.Gerver.Niche
import all MovingSofaOptimality.Gerver.NicheBounds
import all MovingSofaOptimality.Gerver.Properties
import all MovingSofaOptimality.Gerver.Structure
import all MovingSofaOptimality.Gerver.StructureCap
import all MovingSofaOptimality.Injectivity.ArmLengths
import all MovingSofaOptimality.Injectivity.BoundingArms
import all MovingSofaOptimality.Injectivity.DiscreteIneq
import all MovingSofaOptimality.Injectivity.LimitIneq
import all MovingSofaOptimality.Intro.RotationAngleBound
import all MovingSofaOptimality.Main
import all MovingSofaOptimality.Monotone.CapContainsNiche
import all MovingSofaOptimality.Monotone.CapDefs
import all MovingSofaOptimality.Monotone.CapNiche
import all MovingSofaOptimality.Monotone.MonotoneSofa
import all MovingSofaOptimality.Monotone.SupportingHallway
import all MovingSofaOptimality.Optimality.Concavity
import all MovingSofaOptimality.Optimality.Domain
import all MovingSofaOptimality.Optimality.UpperBound
import all MovingSofaOptimality.Optimality.Variation
import all MovingSofaOptimality.Sofa.Defs
import all Solution

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For each main result and each principal step of the proof, this prints the axioms it depends on
and the results from prior work (Baek's theorem, from `MovingSofaOptimality`) that it uses, whether
proved there or, in a conditional formalization, assumed as hypotheses of its statement. It then
checks every declaration of the library and the theorems that Palomar's comparator checks. The run fails if any of them
depends on an axiom other than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a
`sorry` shows up as the axiom `sorryAx`). Its table of results is the source of the report's
dependency table.

It also writes the *route* of each of these results to `.lake/route_deps.tsv`: the other results
of the list that its proof uses, found by following the proof through the library's helper lemmas
and stopping at the results of the list.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

To adapt: generate the `import all` lines, fill in the three lists, and set the library's root
name in `isLibraryModule`. Keep one `import all` line per module of the library, each on its own
line: a module that is missing is still imported through the others, but without its proofs, and
the audit then misses the axioms and the routes inside them. The CI template checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved
there and, in a conditional formalization, the propositions assumed as hypotheses. The traversal
stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Baek, Theorem 1.1.1 (optimality of Gerver's sofa)", ``MovingSofaOptimality.gm_area_le),
   ("Gerver's sofa has area at most 2.2199", ``MovingSofaOptimality.gerverSofa_area_mem)]

/-- The main results and the principal steps of their proof. -/
meta def paperResults : List (String × Name) :=
  [("Optimality: the area is at most M", ``AmbidextrousSofa.IsAmbidextrous.volumeReal_le_M),
   ("Uniqueness: the sofas of area M", ``AmbidextrousSofa.IsAmbidextrous.eq_rigidImage_referenceSofa_of_volumeReal_eq),
   ("The quarter turns at area M", ``AmbidextrousSofa.quarter_turns_of_volumeReal_eq_M),
   ("M is the greatest area", ``AmbidextrousSofa.isGreatest_ambidextrous_areas),
   ("The score of a cap is at most M/2", ``AmbidextrousSofa.IsDownwardCap.capScore_le_half_M),
   ("The caps of score M/2", ``AmbidextrousSofa.IsDownwardCap.capScore_eq_half_M_iff),
   ("The reduction to two caps", ``AmbidextrousSofa.IsAmbidextrous.original_domain_score_reduction),
   ("The area of Romik's sofa", ``AmbidextrousSofa.Reference.volumeReal_referenceSofa),
   ("M > sqrt 2", ``AmbidextrousSofa.sqrt_two_lt_M),
   ("The ordinary bound 2.2199", ``AmbidextrousSofa.volumeReal_le_ordinaryBound_of_lowerPassage)]

/-- The theorems that Palomar's comparator checks (`theorem_names` of `comparator.json`). -/
meta def solutionResults : List Name :=
  [``Ambidextrous.existsUnique_root, ``Ambidextrous.value_eq_romik, ``Ambidextrous.volume_le,
   ``Ambidextrous.isAmbidextrous_referenceSofa, ``Ambidextrous.volume_referenceSofa,
   ``Ambidextrous.isAmbidextrous_image_referenceSofa, ``Ambidextrous.convexHull_referenceSofa,
   ``Ambidextrous.volume_eq_iff, ``Ambidextrous.quarter_turns]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`AmbidextrousSofa).isPrefixOf m

/-- Whether `m` is a module of the copy of lean4-moving-sofa's `MovingSofaOptimality`. -/
meta def isCopiedModule (m : Name) : Bool := (`MovingSofaOptimality).isPrefixOf m

/-- The constants declared in the modules that `p` selects. -/
meta def moduleConstants (env : Environment) (p : Name → Bool) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if p m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := moduleConstants env isLibraryModule

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter (fun d => library.contains d || externals.contains d)
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library and of the copied `MovingSofaOptimality`, including private
  -- and auxiliary ones.
  let copied := moduleConstants env isCopiedModule
  for c in library.toList ++ copied.toList do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library and {copied.size} of the copied " ++
    s!"MovingSofaOptimality: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
