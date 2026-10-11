module

public import AmbidextrousSofa.Analysis.LeftCompanionDensity
public import AmbidextrousSofa.Analysis.ShadowCurvature

@[expose] public section

/-!
# Actual full-maximizer wing densities with the middle atom removed

The full maximizer has its own selected sequence and middle-facet pinning.
These give the literal endpoints of its middle face and zero initial
curvature for the left cut, including the joining normal. Splicing the
original regular density onto this actual cut produces bounded measurable
wing densities suitable for the tilted support equations.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.middle_support_vertices
    {U : Set Plane} {m c : ℝ} (hU : IsFullCapMaximizer U) (hm : m ≠ 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    MovingSofaOptimality.vplus U (affineNormalAngle m) =
      (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)) ∧
    MovingSofaOptimality.vminus U (affineNormalAngle m) =
      (horizontalRight U - capWidth U / 4, capRoof U (horizontalRight U - capWidth U / 4)) := by
  have hs : 0 < Real.sin (affineNormalAngle m) :=
    Real.sin_pos_of_pos_of_lt_pi (affineNormalAngle_mem m).1 (affineNormalAngle_mem m).2
  have hends := (Icc_eq_Icc_iff (hU.isCap.face_fst_order hs.le)).mp
    (show _ = middleHalfInterval (horizontalLeft U) (horizontalRight U) by
      rw [← hU.isCap.horizontalProjection_edge hs.le,
        hU.isCap.edge_affineNormalAngle_eq_supportFace]
      exact hU.horizontalProjection_middle_supportFace hm haffine)
  have hK := hU.isCap.imported_isConvexBody
  refine ⟨Prod.ext hends.1 ?_, Prod.ext hends.2 ?_⟩
  · simpa only [hends.1, capWidth] using
      hU.isCap.capRoof_eq_of_mem_upper_edge hs (MovingSofaOptimality.vplus_mem_edge hK _)
  · simpa only [hends.2, capWidth] using
      hU.isCap.capRoof_eq_of_mem_upper_edge hs (MovingSofaOptimality.vminus_mem_edge hK _)

theorem IsFullCapMaximizer.leftCompanion_initial_curvature_zero
    {U : Set Plane} {m c : ℝ} (hU : IsFullCapMaximizer U) (hm : 0 < m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) (affineNormalAngle m)) = 0 := by
  obtain ⟨ha, hb, hab⟩ :=
    hU.isCap.middleChord_endpoints (by linarith [hU.width_bounds.1, one_lt_M])
  have hθ := affineNormalAngle_mem m
  refine MovingSofaOptimality.sigma_Ioc_eq_zero_of_vplus_const
    (hU.isCap.leftCompanionCap ha).imported_isConvexBody
    (le_add_of_nonneg_left (Real.arctan_pos.mpr hm).le)
    (p := (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)))
    fun t ht => ?_
  have hs : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, Real.pi_pos]) (ht.2.trans_lt hθ.2)
  rcases ht.2.eq_or_lt with rfl | htm
  · rw [hU.isCap.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine hs
      (affineNormal_coefficient_nonpos_after le_rfl hθ.2.le)]
    exact (hU.middle_support_vertices hm.ne' haffine).1
  · exact hU.isCap.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient ha hb hab
      haffine hs (affineNormal_coefficient_pos_before (by linarith [ht.1, Real.pi_pos]) htm)

theorem IsFullCapMaximizer.leftCompanion_density_of_regular_companion
    {U : Set Plane} {m c : ℝ} {ρ : ℝ → ℝ}
    (hU : IsFullCapMaximizer U)
    (haffine : ∀ z ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U z = m * z + c)
    (heq : (upperCurvature U).restrict (regularCompanionDomain m) =
      (volume.restrict (regularCompanionDomain m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
        (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) := by
  set b := max (Real.pi / 2) (affineNormalAngle m)
  have hLb : Real.pi / 2 ≤ b := le_max_left _ _
  have hθb : affineNormalAngle m ≤ b := le_max_right _ _
  obtain ⟨ha, hb, hab⟩ :=
    hU.isCap.middleChord_endpoints (by linarith [hU.width_bounds.1, one_lt_M])
  have hzero : upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) b) = 0 := by
    rcases le_or_gt (affineNormalAngle m) (Real.pi / 2) with hθ | hθ
    · rw [show b = _ from max_eq_left hθ, Ioc_self, measure_empty]
    · rw [show b = _ from max_eq_right hθ.le]
      exact hU.leftCompanion_initial_curvature_zero
        (Real.arctan_pos.mp (by unfold affineNormalAngle at hθ; linarith)) haffine
  have hinter : Ioi b ∩ Ioo (Real.pi / 2) Real.pi = Ioo b Real.pi := by
    ext t
    exact ⟨fun ht => ⟨ht.1, ht.2.2⟩, fun ht => ⟨ht.1, hLb.trans_lt ht.1, ht.2⟩⟩
  conv_lhs => rw [← Ioc_union_Ioo_eq_Ioo hLb
    (max_lt (by linarith [Real.pi_pos]) (affineNormalAngle_mem m).2), Measure.restrict_union
      (Ioc_disjoint_Ioi_same.mono_right Ioo_subset_Ioi_self) measurableSet_Ioo]
  rw [Measure.restrict_eq_zero.mpr hzero, zero_add,
    hU.isCap.leftCompanion_curvature_restrict_open_after_affine ha hb hab haffine hθb,
    restrict_withDensity_of_subset heq measurableSet_Ioo
      fun t ht => ⟨⟨hLb.trans_lt ht.1, ht.2⟩, (hθb.trans_lt ht.1).ne'⟩,
    ← hinter, ← Measure.restrict_restrict measurableSet_Ioi,
    ← withDensity_indicator measurableSet_Ioi]
  exact congrArg _ (indicator_comp_of_zero ENNReal.ofReal_zero)

theorem regularCompanionDomain_subset_regularCurvatureDomain (m : ℝ) :
    regularCompanionDomain m ⊆ regularCurvatureDomain m :=
  fun t ht => ⟨⟨by linarith [ht.1.1, Real.pi_pos], ht.1.2⟩, by
    rintro (h | h)
    exacts [ht.1.1.ne' h, ht.2 h]⟩

theorem firstQuarter_subset_regularCurvatureDomain_of_nonneg {m : ℝ} (hm : 0 ≤ m) :
    Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCurvatureDomain m := by
  intro t ht
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  exact mem_regularCurvatureDomain_iff.mpr ⟨ht.1, by linarith [ht.2, Real.pi_pos], ht.2.ne,
    (add_pos_of_pos_of_nonneg hc (mul_nonneg hm hs.le)).ne'⟩

end AmbidextrousSofa
