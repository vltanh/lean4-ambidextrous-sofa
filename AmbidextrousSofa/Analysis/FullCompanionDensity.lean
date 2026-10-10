import AmbidextrousSofa.Analysis.LeftCompanionDensity
import AmbidextrousSofa.Analysis.ShadowCurvature

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
    Imported.vplus U (affineNormalAngle m) =
      (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)) ∧
    Imported.vminus U (affineNormalAngle m) =
      (horizontalRight U - capWidth U / 4, capRoof U (horizontalRight U - capWidth U / 4)) := by
  have hs : 0 < Real.sin (affineNormalAngle m) :=
    Real.sin_pos_of_pos_of_lt_pi (affineNormalAngle_mem m).1 (affineNormalAngle_mem m).2
  have hproj : Icc (Imported.vplus U (affineNormalAngle m)).1
      (Imported.vminus U (affineNormalAngle m)).1 =
      middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
    rw [← hU.isCap.horizontalProjection_edge hs.le,
      hU.isCap.edge_affineNormalAngle_eq_supportFace]
    exact hU.horizontalProjection_middle_supportFace hm haffine
  have hends := (Icc_eq_Icc_iff (hU.isCap.face_fst_order hs.le)).mp hproj
  constructor
  · apply Prod.ext hends.1
    have h := hU.isCap.capRoof_eq_of_mem_upper_edge hs
      (Imported.vplus_mem_edge hU.isCap.imported_isConvexBody (affineNormalAngle m))
    simpa only [hends.1] using h
  · apply Prod.ext hends.2
    have h := hU.isCap.capRoof_eq_of_mem_upper_edge hs
      (Imported.vminus_mem_edge hU.isCap.imported_isConvexBody (affineNormalAngle m))
    simpa only [hends.2] using h

theorem IsFullCapMaximizer.leftCompanion_initial_curvature_zero
    {U : Set Plane} {m c : ℝ} (hU : IsFullCapMaximizer U) (hm : 0 < m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) (affineNormalAngle m)) = 0 := by
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hV := hU.isCap.leftCompanionCap ha
  have hm0 : 0 < Real.arctan m := Real.arctan_pos.mpr hm
  have hLm : Real.pi / 2 ≤ affineNormalAngle m := by
    unfold affineNormalAngle
    linarith only [hm0]
  apply Imported.sigma_Ioc_eq_zero_of_vplus_const hV.imported_isConvexBody hLm
    (p := (horizontalLeft U + capWidth U / 4, capRoof U (horizontalLeft U + capWidth U / 4)))
  intro t ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (by linarith only [ht.1, Real.pi_pos]) (ht.2.trans_lt (affineNormalAngle_mem m).2)
  rcases ht.2.eq_or_lt with htm | htm
  · rw [htm] at hs ⊢
    rw [hU.isCap.vplus_leftCompanionCap_eq_of_affine ha hb hab haffine hs
      (affineNormal_coefficient_nonpos_after le_rfl (affineNormalAngle_mem m).2.le)]
    exact (hU.middle_support_vertices hm.ne' haffine).1
  · exact hU.isCap.vplus_leftCompanionCap_eq_rightRoof_of_positive_coefficient
      ha hb hab haffine hs (affineNormal_coefficient_pos_before
        (by linarith only [ht.1, Real.pi_pos]) htm)

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
  let b := max (Real.pi / 2) (affineNormalAngle m)
  have hLb : Real.pi / 2 ≤ b := le_max_left _ _
  have hθb : affineNormalAngle m ≤ b := le_max_right _ _
  have hbπ : b < Real.pi := max_lt
    (by linarith only [Real.pi_pos]) (affineNormalAngle_mem m).2
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hzero : upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (Ioc (Real.pi / 2) b) = 0 := by
    by_cases hθ : affineNormalAngle m ≤ Real.pi / 2
    · have hb : b = Real.pi / 2 := max_eq_left hθ
      rw [hb, Ioc_self, measure_empty]
    · have hm : 0 < m := Real.arctan_pos.mp (by
        have hpos : Real.pi / 2 < affineNormalAngle m := lt_of_not_ge hθ
        unfold affineNormalAngle at hpos
        linarith only [hpos])
      have hb : b = affineNormalAngle m := max_eq_right (le_of_not_ge hθ)
      rw [hb]
      exact hU.leftCompanion_initial_curvature_zero hm haffine
  have hlast := hU.isCap.leftCompanion_curvature_restrict_open_after_affine
    ha hb hab haffine hθb
  have hsub : Ioo b Real.pi ⊆ regularCompanionDomain m := by
    intro t ht
    exact ⟨⟨hLb.trans_lt ht.1, ht.2⟩, (hθb.trans_lt ht.1).ne'⟩
  have hρlast := restrict_withDensity_of_subset heq measurableSet_Ioo hsub
  have hdecomp : Ioo (Real.pi / 2) Real.pi =
      Ioc (Real.pi / 2) b ∪ Ioo b Real.pi := by
    ext t
    constructor
    · intro ht
      by_cases htb : t ≤ b
      · exact Or.inl ⟨ht.1, htb⟩
      · exact Or.inr ⟨lt_of_not_ge htb, ht.2⟩
    · intro ht
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans_lt hbπ⟩
      · exact ⟨hLb.trans_lt ht.1, ht.2⟩
  have hd : Disjoint (Ioc (Real.pi / 2) b) (Ioo b Real.pi) := by
    apply disjoint_left.mpr
    intro t ht hs
    exact (not_lt_of_ge ht.2) hs.1
  have hinter : Ioi b ∩ Ioo (Real.pi / 2) Real.pi = Ioo b Real.pi := by
    ext t
    constructor
    · exact fun ht => ⟨ht.1, ht.2.2⟩
    · exact fun ht => ⟨ht.1, hLb.trans_lt ht.1, ht.2⟩
  have hind : (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) =
      (Ioi b).indicator (fun t => ENNReal.ofReal (ρ t)) := by
    funext t
    change ENNReal.ofReal ((Ioi b).indicator ρ t) =
      (Ioi b).indicator (fun r => ENNReal.ofReal (ρ r)) t
    by_cases ht : t ∈ Ioi b
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_not_mem ht, ENNReal.ofReal_zero]
  calc
    _ = (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioc (Real.pi / 2) b) +
        (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioo b Real.pi) := by rw [hdecomp, Measure.restrict_union hd measurableSet_Ioo]
    _ = (volume.restrict (Ioo b Real.pi)).withDensity (fun t => ENNReal.ofReal (ρ t)) := by
      rw [Measure.restrict_eq_zero.mpr hzero, zero_add, hlast, hρlast]
    _ = _ := by
      rw [hind, withDensity_indicator measurableSet_Ioi,
        Measure.restrict_restrict measurableSet_Ioi, hinter]

theorem regularCompanionDomain_subset_regularCurvatureDomain (m : ℝ) :
    regularCompanionDomain m ⊆ regularCurvatureDomain m := by
  intro t ht
  have ht0 : 0 < t := by linarith only [ht.1.1, Real.pi_pos]
  apply mem_regularCurvatureDomain_iff.mpr
  refine ⟨ht0, ht.1.2, (ne_of_gt ht.1.1), ?_⟩
  intro hz
  exact ht.2 (mem_singleton_iff.mpr
    ((cos_add_mul_sin_eq_zero_iff ⟨ht0, ht.1.2⟩).mp hz))

/-- This cut density is constructed from the full maximum itself. Its
bound is evaluated at the original corner velocity only on the retained
wing; the initial cut density is literally zero. -/
theorem IsFullCapMaximizer.leftCompanion_curvature_density_sharp
    {U : Set Plane} {m c : ℝ} (hU : IsFullCapMaximizer U)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (∀ t ≤ max (Real.pi / 2) (affineNormalAngle m), ρ t = 0) ∧
      (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) := by
  obtain ⟨ρ, hρ, hsharp, hcoarse, heq⟩ := hU.curvature_density_on_regular_domain haffine
  have hcomp := restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
    (regularCompanionDomain_subset_regularCurvatureDomain m)
  refine ⟨leftCompanionWingDensity m ρ, measurable_leftCompanionWingDensity hρ m,
    ?_, ?_, (fun t ht => leftCompanionWingDensity_eq_zero ht),
    hU.leftCompanion_density_of_regular_companion haffine hcomp⟩
  · intro t
    by_cases ht : max (Real.pi / 2) (affineNormalAngle m) < t
    · rw [leftCompanionWingDensity_eq ht]
      exact hsharp t
    · rw [leftCompanionWingDensity_eq_zero (le_of_not_gt ht)]
      exact ⟨le_rfl, sourceKappa_nonneg _⟩
  · intro t
    by_cases ht : max (Real.pi / 2) (affineNormalAngle m) < t
    · rw [leftCompanionWingDensity_eq ht]
      exact hcoarse t
    · rw [leftCompanionWingDensity_eq_zero (le_of_not_gt ht)]
      positivity

theorem firstQuarter_subset_regularCurvatureDomain_of_nonneg {m : ℝ} (hm : 0 ≤ m) :
    Ioo (0 : ℝ) (Real.pi / 2) ⊆ regularCurvatureDomain m := by
  intro t ht
  have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo
    (show t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
      exact ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩)
  apply mem_regularCurvatureDomain_iff.mpr
  refine ⟨ht.1, by linarith only [ht.2, Real.pi_pos], ht.2.ne, ?_⟩
  exact (add_pos_of_pos_of_nonneg hc (mul_nonneg hm hs.le)).ne'

/-- Both actual support arcs have a bounded density. The companion is
the literal low-wing cut, so its removed middle-face atom is not hidden
in the regularity hypothesis. The two representatives come from the
same selected original density. -/
theorem IsFullCapMaximizer.exists_full_tilted_wing_densities
    {U : Set Plane} {m c : ℝ} (hU : IsFullCapMaximizer U) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (upperCurvature U).restrict (Ioo (0 : ℝ) (Real.pi / 2)) =
        (volume.restrict (Ioo (0 : ℝ) (Real.pi / 2))).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
          (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) := by
  obtain ⟨ρ, hρ, hsharp, hcoarse, heq⟩ := hU.curvature_density_on_regular_domain haffine
  have hcomp := restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
    (regularCompanionDomain_subset_regularCurvatureDomain m)
  exact ⟨ρ, hρ, hsharp, hcoarse, heq,
    restrict_withDensity_of_subset heq measurableSet_Ioo
      (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm),
    hU.leftCompanion_density_of_regular_companion haffine hcomp⟩

end AmbidextrousSofa
