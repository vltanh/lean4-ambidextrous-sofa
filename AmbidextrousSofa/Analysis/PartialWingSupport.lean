module

public import AmbidextrousSofa.Analysis.PartialNegativeCornerCurvature
public import AmbidextrousSofa.Analysis.PartialWidthBounds
public import AmbidextrousSofa.Analysis.TiltedWingSupport

@[expose] public section

/-!
# The actual two used support arcs of a proper maximum

Same-cap completion places the negative middle normal beyond the
terminal angle. In the other middle orientations that normal is at or
beyond the top. Consequently the entire first used open arc has the
proved density, and the literal left companion cut supplies the second
arc. The positive-tilt initial surrogate interval has both actual
densities zero; its first density vanishes because its original corner
is below the floor.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.proper_terminal_lt_affineNormal_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : α < affineNormalAngle m := by
  by_cases hm : m < 0
  · exact (hU.negative_remaining_tail_geometry_of_tail_regime hregime hproper hheight hm haffine).1
  · have hm0 := Real.arctan_nonneg.mpr (le_of_not_gt hm)
    unfold affineNormalAngle
    linarith only [hm0, hproper]

theorem IsJointCapMaximizer.proper_first_arc_subset_regular_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Ioo (0 : ℝ) α ⊆ regularProperCurvatureDomain α m := by
  have hαm := hU.proper_terminal_lt_affineNormal_of_tail_regime hregime hproper hheight haffine
  intro t ht
  refine ⟨mem_regularCurvatureDomain_iff.mpr ⟨ht.1, ?_, ?_, ?_⟩, ht.2.ne⟩
  · linarith only [ht.2, hproper, Real.pi_pos]
  · exact (ht.2.trans hproper).ne
  · exact (affineNormal_coefficient_pos_before ht.1.le (ht.2.trans hαm)).ne'

theorem regularCompanionDomain_subset_regularProperCurvatureDomain
    {α m : ℝ} (hproper : α < Real.pi / 2) :
    regularCompanionDomain m ⊆ regularProperCurvatureDomain α m := by
  intro t ht
  exact ⟨regularCompanionDomain_subset_regularCurvatureDomain m ht,
    (hproper.trans ht.1.1).ne'⟩

theorem IsJointCapMaximizer.proper_first_density_of_regular_of_tail_regime
    {U : Set Plane} {α m c : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    (upperCurvature U).restrict (Ioo (0 : ℝ) α) =
      (volume.restrict (Ioo (0 : ℝ) α)).withDensity (fun t => ENNReal.ofReal (ρ t)) :=
  restrict_withDensity_of_subset heq measurableSet_Ioo
    (hU.proper_first_arc_subset_regular_of_tail_regime hregime hproper hheight haffine)

theorem IsJointCapMaximizer.proper_leftCompanion_density_of_regular
    {U : Set Plane} {α m c : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    (upperCurvature (leftCompanionCap U (horizontalLeft U + capWidth U / 4))).restrict
        (Ioo (Real.pi / 2) Real.pi) =
      (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
        (fun t => ENNReal.ofReal (leftCompanionWingDensity m ρ t)) :=
  hU.leftCompanion_density_of_regular_companion haffine
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularProperCurvatureDomain hproper))

theorem IsJointCapMaximizer.proper_first_wing_curvature_zero_before_affine
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hm : 0 ≤ m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U (Ioo (0 : ℝ) (Real.arctan m)) = 0 := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hhigh : capRoof U C = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rw [hr, show capWidth U = 4 * C by unfold capWidth; rw [hl, hr]; ring] at h
    simpa only [show 2 * C - 4 * C / 4 = C by ring] using h
  have hmα : Real.arctan m < α := by
    have h := hU.middle_normal_lt_terminal_companion haffine
    unfold affineNormalAngle at h
    linarith only [h]
  have hsub : Ioo (0 : ℝ) (Real.arctan m) ⊆
      {θ ∈ regularProperCurvatureDomain α m | sourceCornerHeight U θ < 0} := by
    intro t ht
    have htL := ht.2.trans (Real.arctan_lt_pi_div_two m)
    refine ⟨⟨firstQuarter_subset_regularCurvatureDomain_of_nonneg hm ⟨ht.1, htL⟩,
      (ht.2.trans hmα).ne⟩, ?_⟩
    rw [sourceCornerHeight, sourceQuarterAngle, if_pos htL]
    exact hU.isCap.attachedCorner_neg_before_positive_affine hl hr hC hsmall haff hhigh ht
  exact le_antisymm ((measure_mono hsub).trans_eq
    (hU.upperCurvature_proper_negative_corners_eq_zero hproper haffine)) zero_le

/-- The actual proper width and tilt bounds discharge the geometric
smallness needed for the unused positive-tilt interval. -/
theorem IsJointCapMaximizer.proper_width_add_slope_lt_one
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : C + m < 1 := by
  have hl' : horizontalLeft U = -(2 * C) := hl.trans (by ring)
  have hb := hU.centered_proper_half_width_bounds_of_affine_nonneg
    hproper hl' hr hheight hm haffine
  have hC0 : 1 / 2 ≤ C := by linarith only [hb.1]
  have hC1 : C ≤ 37 / 50 := by linarith only [hb.2.1]
  have hh : 1 - capRoof U (-C) < 17 / 50 := by
    simpa only [show -(2 * C) / 2 = -C by ring] using hb.2.2
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hleft := haff (-C) ⟨le_rfl, by linarith only [hC0]⟩
  have hright := haff C ⟨by linarith only [hC0], le_rfl⟩
  have hhigh := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
  have hw : capWidth U = 4 * C := by unfold capWidth; rw [hl, hr]; ring
  rw [hr, hw, show 2 * C - 4 * C / 4 = C by ring] at hhigh
  have hmEq : m = (1 - capRoof U (-C)) / (2 * C) := by
    apply (eq_div_iff (show 2 * C ≠ 0 by linarith only [hC0])).mpr
    nlinarith only [hleft, hright, hhigh]
  rw [hmEq]
  exact canonical_width_add_slope_lt_one hC0 hC1 hh

theorem IsJointCapMaximizer.proper_first_wing_initial_curvature_zero
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U (Ioo (0 : ℝ) (Real.arctan m)) = 0 := by
  have hl' : horizontalLeft U = -(2 * C) := hl.trans (by ring)
  have hb := hU.centered_proper_half_width_bounds_of_affine_nonneg
    hproper hl' hr hheight hm haffine
  exact hU.proper_first_wing_curvature_zero_before_affine hproper hl hr
    (by linarith only [hb.1]) hm
    (hU.proper_width_add_slope_lt_one hproper hl hr hheight hm haffine) hheight haffine

end AmbidextrousSofa
