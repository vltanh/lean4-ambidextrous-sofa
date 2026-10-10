import AmbidextrousSofa

/-!
# Prepared axiom queries — not executed

This file is deliberately outside the main library entry point.
Every explicitly named declaration in the six project modules is listed.
The allowed resulting dependency set is a subset of:
`propext`, `Classical.choice`, `Quot.sound`.

These queries do not enforce that policy by themselves and have not been run.
A later Lean verification pass must inspect their actual transitive output.
-/

-- AmbidextrousSofa/Algebra/Deficit.lean
#print axioms AmbidextrousSofa.signedFiberLength
#print axioms AmbidextrousSofa.fourWallFiber
#print axioms AmbidextrousSofa.mem_fourWallFiber
#print axioms AmbidextrousSofa.fourWallFiber_eq_Icc
#print axioms AmbidextrousSofa.fourWallFiber_nonempty_iff
#print axioms AmbidextrousSofa.signedFiberLength_nonneg_of_mem
#print axioms AmbidextrousSofa.max_sub_left_eq_max_sub_zero
#print axioms AmbidextrousSofa.max_sub_right_eq_max_sub_zero
#print axioms AmbidextrousSofa.middlePartitionDefect
#print axioms AmbidextrousSofa.exteriorPartitionDefect
#print axioms AmbidextrousSofa.middle_partition_defect_identity
#print axioms AmbidextrousSofa.exterior_partition_defect_identity
#print axioms AmbidextrousSofa.middlePartitionDefect_nonneg
#print axioms AmbidextrousSofa.exteriorPartitionDefect_nonneg
#print axioms AmbidextrousSofa.middlePartitionDefect_eq_zero_iff
#print axioms AmbidextrousSofa.exteriorPartitionDefect_eq_zero_iff
#print axioms AmbidextrousSofa.signedFiberLength_le_middle
#print axioms AmbidextrousSofa.signedFiberLength_le_exterior
#print axioms AmbidextrousSofa.four_term_deficit_identity
#print axioms AmbidextrousSofa.four_term_deficit_of_eq
#print axioms AmbidextrousSofa.area_le_of_deficit_bounds
#print axioms AmbidextrousSofa.area_eq_iff_deficits_vanish
#print axioms AmbidextrousSofa.extrusion_truncation_identity
#print axioms AmbidextrousSofa.extrusion_truncation_nonneg
#print axioms AmbidextrousSofa.extrusion_truncation_eq_zero_iff
#print axioms AmbidextrousSofa.extrusion_truncation_pos_iff

-- AmbidextrousSofa/ExactConstant.lean
#print axioms AmbidextrousSofa.cubic
#print axioms AmbidextrousSofa.cubic_sub_cubic
#print axioms AmbidextrousSofa.cubic_strictMono
#print axioms AmbidextrousSofa.continuous_cubic
#print axioms AmbidextrousSofa.exists_positive_root
#print axioms AmbidextrousSofa.cubic_root_unique
#print axioms AmbidextrousSofa.existsUnique_positive_root
#print axioms AmbidextrousSofa.Y
#print axioms AmbidextrousSofa.Y_pos
#print axioms AmbidextrousSofa.Y_cubic
#print axioms AmbidextrousSofa.Y_equation
#print axioms AmbidextrousSofa.eq_Y_of_cubic_eq_zero
#print axioms AmbidextrousSofa.cubic_eq_zero_iff_eq_Y
#print axioms AmbidextrousSofa.two_sevenths_lt_Y
#print axioms AmbidextrousSofa.Y_lt_three_tenths
#print axioms AmbidextrousSofa.Y_ne_zero
#print axioms AmbidextrousSofa.Y_lt_one
#print axioms AmbidextrousSofa.beta
#print axioms AmbidextrousSofa.beta_pos
#print axioms AmbidextrousSofa.beta_lt_pi_div_two
#print axioms AmbidextrousSofa.beta_lt_pi_div_four
#print axioms AmbidextrousSofa.tan_beta
#print axioms AmbidextrousSofa.M
#print axioms AmbidextrousSofa.one_lt_M
#print axioms AmbidextrousSofa.M_pos
#print axioms AmbidextrousSofa.M_sub_beta_add_two_mul_Y

-- AmbidextrousSofa/Geometry/Caps.lean
#print axioms AmbidextrousSofa.actualHull
#print axioms AmbidextrousSofa.horizontalProjection
#print axioms AmbidextrousSofa.upperCap
#print axioms AmbidextrousSofa.IsDownwardCap
#print axioms AmbidextrousSofa.subset_actualHull
#print axioms AmbidextrousSofa.convex_actualHull
#print axioms AmbidextrousSofa.actualHull_mono
#print axioms AmbidextrousSofa.upperCap_mono
#print axioms AmbidextrousSofa.upperCap_downward
#print axioms AmbidextrousSofa.subset_upperCap
#print axioms AmbidextrousSofa.horizontalProjection_upperCap
#print axioms AmbidextrousSofa.IsDownwardCap.upperCap_eq
#print axioms AmbidextrousSofa.IsDownwardCap.baseline_mem

-- AmbidextrousSofa/Geometry/Motions.lean
#print axioms AmbidextrousSofa.motionInterval
#print axioms AmbidextrousSofa.RigidMotionPath
#print axioms AmbidextrousSofa.RigidMotionPath.placement
#print axioms AmbidextrousSofa.Passage
#print axioms AmbidextrousSofa.SameInitialOrientation
#print axioms AmbidextrousSofa.IsAmbidextrous
#print axioms AmbidextrousSofa.Passage.mono
#print axioms AmbidextrousSofa.IsAmbidextrous.of_subset

-- AmbidextrousSofa/Geometry/Plane.lean
#print axioms AmbidextrousSofa.Plane
#print axioms AmbidextrousSofa.rotate
#print axioms AmbidextrousSofa.rigidMap
#print axioms AmbidextrousSofa.squaredLength
#print axioms AmbidextrousSofa.rotate_zero
#print axioms AmbidextrousSofa.rigidMap_zero_zero
#print axioms AmbidextrousSofa.squaredLength_rotate
#print axioms AmbidextrousSofa.reflect
#print axioms AmbidextrousSofa.reflect_reflect
#print axioms AmbidextrousSofa.unitStrip
#print axioms AmbidextrousSofa.incomingArm
#print axioms AmbidextrousSofa.lowerOutgoingArm
#print axioms AmbidextrousSofa.upperOutgoingArm
#print axioms AmbidextrousSofa.lowerHall
#print axioms AmbidextrousSofa.upperHall
#print axioms AmbidextrousSofa.reflect_mem_unitStrip
#print axioms AmbidextrousSofa.reflect_mem_incomingArm
#print axioms AmbidextrousSofa.reflect_mem_lowerOutgoingArm
#print axioms AmbidextrousSofa.reflect_mem_lowerHall
#print axioms AmbidextrousSofa.upperHall_eq_preimage_lowerHall

-- AmbidextrousSofa/Topology/RegularClosed.lean
#print axioms AmbidextrousSofa.closure_interior_subset_of_measure_sdiff_eq_zero
#print axioms AmbidextrousSofa.eq_of_subset_of_measure_eq_of_regularClosed
#print axioms AmbidextrousSofa.eq_of_subset_of_measure_eq_of_isCompact_regularClosed
