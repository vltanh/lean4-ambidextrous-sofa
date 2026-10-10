import AmbidextrousSofa.Analysis.ProperExcessEnvelope
import AmbidextrousSofa.Analysis.TerminalProperComparison

/-!
# Exclusion of an actual largest-angle proper maximizer

The reflected excess envelope is transferred to the literal left-cut
density. For a near-full terminal angle the entire comparison prefix
has unit density. In the remaining cotangent range the exact cubic
payment is smaller than the terminal margin. The density is constructed
inside the exclusion theorem from the actual selected-source limit.

Centering, height normalization and middle-chord replacement preserve
the maximizing angle, so the exclusion applies to the genuine
largest-angle maximum. This reduces the global cap-and-angle objective
to the full-angle cap objective, without assuming its sharp value.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem leftCompanion_excess_bound_of_reflected
    {ρ : ℝ → ℝ} {m α θ B : ℝ} (hθ : θ ≤ α)
    (hbound : ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      max (properReflectedFirstDensity m ρ r - 1) 0 ≤
        (19 / 25 : ℝ) * max (B - r) 0) :
    ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1) 0 ≤
        (19 / 25 : ℝ) * max (t - (Real.pi / 2 - B)) 0 := by
  have hglobal := (ae_restrict_iff' measurableSet_Ioo).mp hbound
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae hglobal
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with t ht hs
  have h := hs (show Real.pi / 2 - t ∈ Ioo (Real.pi / 2 - α) (Real.pi / 2) from
    ⟨by linarith only [ht.2, hθ], by linarith only [ht.1]⟩)
  simpa only [properReflectedFirstDensity,
    show Real.pi / 2 - (Real.pi / 2 - t) + Real.pi / 2 = t + Real.pi / 2 by ring,
    show B - (Real.pi / 2 - t) = t - (Real.pi / 2 - B) by ring] using h

theorem IsJointCapMaximizer.proper_companion_prefix_bounds_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < C - topOverhangLeft U ∧ C - topOverhangLeft U ≤ 37 / 50 ∧
      Real.arcsin (C - topOverhangLeft U) < α ∧
      Real.arcsin (C - topOverhangLeft U) < Real.pi / 2 - 73 / 100 := by
  have hw : capWidth U / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hw] at hC
  have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper hheight haffine
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  have hinset := (hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH).2.1
  have hcos := (terminal_sin_cos_bounds_after_initialAngle
    hU.terminal_angle_gt_arctan_eight_thirds.le hproper).2
  have hCT : 0 < C - topOverhangLeft U := by
    linarith only [hC.1, hTP, hinset, hcos, topOverhangRight_nonneg U]
  have hCT1 : C - topOverhangLeft U ≤ 37 / 50 := by
    linarith only [hC.2, topOverhangLeft_nonneg U]
  have hcut := Analysis.eleven_fifteenths_lt_arccos_of_le
    (show -1 ≤ C - topOverhangLeft U by linarith only [hCT]) hCT1
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hcut
  have hgap : Real.pi / 2 - α < 3 / 8 := by
    rw [terminal_gap_eq_arctan_slope hU.angle_pos hproper]
    exact (Real.arctan_lt_self (terminalSlope_pos hU.angle_pos hproper)).trans
      (hU.proper_terminalSlope_lt_three_eighths hproper)
  exact ⟨hCT, hCT1, by linarith only [hcut, hgap], by linarith only [hcut]⟩

theorem IsJointCapMaximizer.proper_companion_prefix_bounds
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    0 < C - topOverhangLeft U ∧ C - topOverhangLeft U ≤ 37 / 50 ∧
      Real.arcsin (C - topOverhangLeft U) < α ∧
      Real.arcsin (C - topOverhangLeft U) < Real.pi / 2 - 73 / 100 := by
  exact IsJointCapMaximizer.proper_companion_prefix_bounds_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine

/-- The early weighted excess of the actual companion is strictly below
the already proved terminal margin, in both terminal-slope ranges. -/
theorem IsJointCapMaximizer.proper_leftCompanion_weighted_excess_lt_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hsharp : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    terminalWeightedExcess (fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2))
      (Real.arcsin (C - topOverhangLeft U)) < (39 / 4400 : ℝ) * Real.cos α := by
  obtain ⟨hCT, hCT1, hθα, hθcut⟩ := hU.proper_companion_prefix_bounds_of_tail_regime
    hregime hproper hl hr hheight haffine
  by_cases hκ : terminalSlope α ≤ 1 / 8
  · have hbound := leftCompanion_excess_bound_of_reflected hθα.le
      (hU.properReflected_ae_near_full_excess_bound_of_tail_regime
        hregime hproper hl hr hheight haffine hρ hρ0 hρK hsharp heq hκ)
    have hunit : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.arcsin (C - topOverhangLeft U))),
        leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 := by
      filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht hmem
      rw [max_eq_right (show t - (Real.pi / 2 - 73 / 100) ≤ 0 by
        linarith only [hmem.2, hθcut]), mul_zero] at ht
      have h := (le_max_left (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1) 0).trans ht
      linarith only [h]
    rw [terminalWeightedExcess_eq_zero_of_unit_prefix (Real.arcsin_nonneg.mpr hCT.le) hunit]
    exact mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo
      ⟨by linarith only [hU.angle_pos, Real.pi_pos], hproper⟩)
  · have hbound := leftCompanion_excess_bound_of_reflected hθα.le
      (hU.properReflected_ae_excess_bound_of_tail_regime
        hregime hproper hl hr hheight haffine hρ hρ0 hρK hsharp heq)
    have hint : IntervalIntegrable
        (fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2)) volume
        0 (Real.arcsin (C - topOverhangLeft U)) :=
      intervalIntegrable_bounded_real_density
        ((measurable_leftCompanionWingDensity hρ m).comp (measurable_id.add_const _))
        (fun t => (leftCompanionWingDensity_bounds hρ0 hρK _).1)
        (fun t => (leftCompanionWingDensity_bounds hρ0 hρK _).2) _ _
    exact terminalWeightedExcess_lt_allowance_of_late_tail hCT.le hCT1 hU.angle_pos hproper
      (le_of_not_ge hκ) (terminalWeightedExcess_intervalIntegrable hint) hbound

theorem IsJointCapMaximizer.proper_leftCompanion_weighted_excess_lt
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hsharp : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    terminalWeightedExcess (fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2))
      (Real.arcsin (C - topOverhangLeft U)) < (39 / 4400 : ℝ) * Real.cos α := by
  exact IsJointCapMaximizer.proper_leftCompanion_weighted_excess_lt_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine
    hρ hρ0 hρK hsharp heq

/-- Every density and endpoint input in the contradiction is produced
from the same actual maximizing cap. -/
theorem IsJointCapMaximizer.false_of_centered_proper_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : False := by
  obtain ⟨ρ, hρ, hsharp, hcoarse, heq⟩ :=
    hU.curvature_density_on_regular_proper_domain hproper haffine
  have hρ0 := fun t => (hsharp t).1
  have hκ := fun t => (hsharp t).2
  have hupper := hU.proper_leftCompanion_weighted_excess_lt_of_tail_regime hregime hproper hl hr hheight
    haffine hρ hρ0 hcoarse hκ heq
  have hcut := hU.proper_leftCompanion_density_of_regular hproper haffine heq
  have hwidth : capWidth U / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hleftMiddle : horizontalLeft U + capWidth U / 4 = -C := by rw [hl, hwidth]; ring
  have hrightMiddle : horizontalRight U - capWidth U / 4 = C := by rw [hr, hwidth]; ring
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hwidth] at hC
  have hinitial := (hU.leftCompanion_actual_initial_data hheight haffine).2.1
  rw [hleftMiddle, hwidth] at hinitial
  have htail := hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime
    hregime hproper hheight haffine
  rw [hrightMiddle] at htail
  rw [hleftMiddle] at hcut
  exact hU.false_of_leftCompanion_weighted_excess_of_tail_regime hregime hproper hheight haffine hl hr
    hinitial htail (by linarith only [hC.1]) hC.2.le (hU.terminal_cosine_square_cut hproper)
    (topOverhangLeft_nonneg U) (topOverhangRight_nonneg U)
    (hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper hheight haffine)
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hcoarse t).2) hcut hupper.le

theorem IsJointCapMaximizer.false_of_centered_proper_largest_angle
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : False := by
  exact IsJointCapMaximizer.false_of_centered_proper_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hl hr hheight haffine

theorem IsJointCapMaximizer.angle_eq_pi_div_two_of_largest
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α) :
    α = Real.pi / 2 := by
  apply le_antisymm hU.angle_mem.2
  by_contra hnot
  have hproper : α < Real.pi / 2 := lt_of_not_ge hnot
  have hcenter : IsJointCapMaximizer (centeredCap U) α :=
    hU.of_score_le hU.isCap.centeredCap hU.angle_mem (by rw [capScore_centeredCap hU.isCap])
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := hcenter.exists_heightOne_affine_middle
  let C := capWidth U / 4
  have hl : horizontalLeft V = -2 * C := by
    calc
      _ = horizontalLeft (centeredCap U) := by unfold horizontalLeft; rw [hproj]
      _ = _ := by rw [horizontalLeft_centeredCap hU.isCap]; dsimp only [C]; ring
  have hr : horizontalRight V = 2 * C := by
    calc
      _ = horizontalRight (centeredCap U) := by unfold horizontalRight; rw [hproj]
      _ = _ := by rw [horizontalRight_centeredCap hU.isCap]; dsimp only [C]; ring
  exact hV.false_of_centered_proper_largest_angle hLargest hproper hl hr hheight haffine

theorem exists_jointCapMaximizer_full_angle :
    ∃ U : Set Plane, IsJointCapMaximizer U (Real.pi / 2) := by
  obtain ⟨U, α, hU, _, hLargest⟩ := exists_jointCapMaximizer_largest_angle
  have hα := hU.angle_eq_pi_div_two_of_largest hLargest
  exact ⟨U, by simpa only [hα] using hU⟩

/-- A full-angle maximum now also maximizes over all allowed terminal
angles. Its sharp score is a separate full-cap theorem. -/
theorem IsFullCapMaximizer.isJointCapMaximizer
    {U : Set Plane} (hU : IsFullCapMaximizer U) : IsJointCapMaximizer U (Real.pi / 2) := by
  obtain ⟨V, hV⟩ := exists_jointCapMaximizer_full_angle
  refine ⟨hU.isCap, ⟨by linarith only [Real.pi_pos], le_rfl⟩, ?_⟩
  intro W β hW hβ
  exact (hV.score_le hW hβ).trans (hU.2 V hV.isCap)

end AmbidextrousSofa
