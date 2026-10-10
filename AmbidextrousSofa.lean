import AmbidextrousSofa.ExactConstant
import AmbidextrousSofa.Geometry.Plane
import AmbidextrousSofa.Geometry.Motions
import AmbidextrousSofa.Geometry.Caps
import AmbidextrousSofa.Geometry.CapGeometry
import AmbidextrousSofa.Geometry.HullCompact
import AmbidextrousSofa.Geometry.Support
import AmbidextrousSofa.Geometry.Reflection
import AmbidextrousSofa.Geometry.Hallway
import AmbidextrousSofa.Geometry.Barriers
import AmbidextrousSofa.Geometry.BarrierAnalysis
import AmbidextrousSofa.Geometry.AngularDomain
import AmbidextrousSofa.Algebra.Deficit
import AmbidextrousSofa.Topology.RegularClosed
import AmbidextrousSofa.Measure.Fibers
import AmbidextrousSofa.Measure.Partition
import AmbidextrousSofa.Measure.CapScore
import AmbidextrousSofa.Measure.CapAssembly
import AmbidextrousSofa.Reference.Parameters
import AmbidextrousSofa.Reference.Support
import AmbidextrousSofa.Reference.Hull

/-!
# Ambidextrous sofa: an uncompiled geometric and analytic draft

This entry point imports every implementation module in the draft: the actual
hull and cap constructions, complete angular barriers, integrated physical
area and deficit assembly, and the explicit reference formulas and hull.
Every declared theorem has a complete source proof body. The full sharp cap
bounds, reference attainment, and original-domain optimality and uniqueness
remain listed in `docs/FORMALIZATION-ROADMAP.md`. This project has not been compiled.
-/
