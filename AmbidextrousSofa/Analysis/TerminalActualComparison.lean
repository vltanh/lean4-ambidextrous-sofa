import AmbidextrousSofa.Analysis.TerminalLeftComparison
import AmbidextrousSofa.Analysis.PartialSharpCurvatureDensity
import AmbidextrousSofa.Analysis.TerminalTopProjection

/-!
# Actual initial data in the proper companion comparison

The left cut starts at the lesser of the original top abscissa and the
left middle endpoint. Thus its horizontal moment starts at the literal
quarter-width minus the actual left top overhang. The height and right
support derivative also retain the original low middle endpoint.

The terminal tail position and weighted top budget come from the actual
source-moment projection theorem. The cosine cut follows from the proved
initial-angle exclusion. Only the width range and the early weighted
curvature estimate remain analytic obligations in the final comparison.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.top_leftCompanionCap_fst_eq_min_of_affine
    {U : Set Plane} (hU : IsDownwardCap U) {a b m c : ℝ}
    (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (haffine : ∀ x ∈ Icc a b, capRoof U x = m * x + c) :
    (Imported.vplus (leftCompanionCap U a) (Real.pi / 2)).1 =
      min a (Imported.vplus U (Real.pi / 2)).1 := by
  by_cases hm : m ≤ 0
  · have htop := (hU.leftCompanion_initial_data_of_nonpos_affine ha hb hab hm haffine).1
    have hp := (Imported.vplus_mem_edge (hU.leftCompanionCap ha).imported_isConvexBody
      (Real.pi / 2)).1
    have hxa : (Imported.vplus U (Real.pi / 2)).1 ≤ a := by
      rw [← htop]
      exact hp.2.2
    rw [htop, min_eq_right hxa]
  · have hm0 : 0 < m := lt_of_not_ge hm
    have htop := (hU.top_leftCompanionCap_of_positive_affine ha hb hab hm0 haffine).2
    have hp := (Imported.vplus_mem_edge hU.imported_isConvexBody (Real.pi / 2)).1
    have hceiling := (le_capRoof hU.isCompact hp).trans
      (hU.capRoof_le_affine_of_affine_segment ha hb hab haffine
        (Imported.vplus U (Real.pi / 2)).1 ⟨Imported.vplus U (Real.pi / 2), hp, rfl⟩)
    have hfa : capRoof U a ≤ capHeight U := by
      have h := coordDot_le_support hU.isCompact (capRoof_mem hU.isCompact ha) (0, 1)
      simpa only [coordDot, capHeight, mul_zero, mul_one, zero_add] using h
    have hpy := top_vplus_snd_eq_capHeight U
    have hline := haffine a ⟨le_rfl, hab.le⟩
    have hax : a ≤ (Imported.vplus U (Real.pi / 2)).1 := by
      apply (mul_le_mul_left hm0).mp
      linarith only [hceiling, hfa, hpy, hline]
    rw [htop, min_eq_left hax]

/-- The physical left overhang is precisely the missing initial
horizontal displacement of the left charged wing. -/
theorem IsDownwardCap.leftCompanion_initialOffset_eq_quarter_sub_topOverhang
    {U : Set Plane} (hU : IsDownwardCap U) {m c : ℝ}
    (hwidth : 0 < capWidth U)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    companionInitialOffset (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) =
      capWidth U / 4 - topOverhangLeft U := by
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  have htop := hU.top_leftCompanionCap_fst_eq_min_of_affine ha hb hab haffine
  unfold companionInitialOffset topOverhangLeft
  rw [htop, horizontalLeft_leftCompanionCap hU ha]
  by_cases hx : (Imported.vplus U (Real.pi / 2)).1 ≤ horizontalLeft U + capWidth U / 4
  · rw [min_eq_right hx, max_eq_left (sub_nonneg.mpr hx)]
    ring
  · rw [min_eq_left (le_of_not_ge hx), max_eq_right (by linarith only [le_of_not_ge hx])]
    ring

/-- These are the actual support height and one-sided derivative in
every sign of the middle slope, including the low positive-tilt start. -/
theorem IsJointCapMaximizer.leftCompanion_actual_initial_data
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    let V := leftCompanionCap U (horizontalLeft U + capWidth U / 4)
    capHeight V = capRoof U (horizontalLeft U + capWidth U / 4) ∧
      companionInitialOffset V = capWidth U / 4 - topOverhangLeft U ∧
      companionInitialDeficit V = 1 - capRoof U (horizontalLeft U + capWidth U / 4) ∧
      HasDerivWithinAt (fun t => angleSupport V (t + Real.pi / 2))
        (-(horizontalLeft U + capWidth U / 4) + topOverhangLeft U) (Ici 0) 0 := by
  dsimp only
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hV := hU.isCap.leftCompanionCap ha
  have hVheight : capHeight (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) =
      capRoof U (horizontalLeft U + capWidth U / 4) := by
    by_cases hm : m ≤ 0
    · have htop := (hU.isCap.leftCompanion_initial_data_of_nonpos_affine ha hb hab hm haffine).1
      rw [← top_vplus_snd_eq_capHeight _, htop, top_vplus_snd_eq_capHeight U, hheight]
      exact (hU.middle_left_eq_one_of_affine_nonpos hheight hm haffine).symm
    · exact (hU.isCap.top_leftCompanionCap_of_positive_affine
        ha hb hab (lt_of_not_ge hm) haffine).1
  have hOffset := hU.isCap.leftCompanion_initialOffset_eq_quarter_sub_topOverhang hwidth haffine
  refine ⟨hVheight, hOffset, ?_, ?_⟩
  · unfold companionInitialDeficit
    rw [hVheight]
  · have hderiv := hV.hasDerivWithinAt_companionSupport_zero
    have hx : (Imported.vplus (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
        (Real.pi / 2)).1 = horizontalLeft U + capWidth U / 4 - topOverhangLeft U := by
      unfold companionInitialOffset at hOffset
      rw [horizontalLeft_leftCompanionCap hU.isCap ha] at hOffset
      linarith only [hOffset]
    rw [hx, show -(horizontalLeft U + capWidth U / 4 - topOverhangLeft U) =
      -(horizontalLeft U + capWidth U / 4) + topOverhangLeft U by ring] at hderiv
    exact hderiv

theorem terminal_cosine_square_cut_after_initialAngle {α : ℝ}
    (hα0 : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) :
    73 * Real.cos α ^ 2 ≤ 9 := by
  have hαpos : 0 < α :=
    (Real.arctan_pos.mpr (by norm_num : (0 : ℝ) < 8 / 3)).trans_le hα0
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos
    (by linarith only [hαL, Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hαpos, Real.pi_pos], hαL⟩
  have htan : (8 / 3 : ℝ) ≤ Real.tan α := by
    have h := Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo (8 / 3))
      (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith only [hαpos, Real.pi_pos], hαL⟩) hα0
    simpa only [Real.tan_arctan] using h
  rw [Real.tan_eq_sin_div_cos] at htan
  have hsc : 8 * Real.cos α ≤ 3 * Real.sin α := by
    have h := (le_div_iff₀ hc).mp htan
    linarith only [h]
  have hprod := mul_nonneg (sub_nonneg.mpr hsc)
    (show 0 ≤ 3 * Real.sin α + 8 * Real.cos α by positivity)
  nlinarith only [hprod, Real.sin_sq_add_cos_sq α]

theorem IsJointCapMaximizer.terminal_cosine_square_cut
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) : 73 * Real.cos α ^ 2 ≤ 9 :=
  terminal_cosine_square_cut_after_initialAngle
    hU.terminal_angle_gt_arctan_eight_thirds.le hproper

/-- The exact proper source density and every endpoint input are now
constructed from the maximizer. An excess below the displayed margin
is impossible once the actual width is in the stated comparison range. -/
theorem IsJointCapMaximizer.exists_actual_leftCompanion_density_excess_gt_of_tail_regime
    {U : Set Plane} {α m c C : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (∀ t ≤ max (Real.pi / 2) (affineNormalAngle m), ρ t = 0) ∧
      (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) ∧
      (39 / 4400 : ℝ) * Real.cos α <
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (C - topOverhangLeft U)) := by
  obtain ⟨ρ, hρ, hsharp, hcoarse, hzero, heq⟩ :=
    hU.leftCompanion_curvature_density_sharp hproper haffine
  have hwidth : capWidth U / 4 = C := by unfold capWidth; rw [hleft, hright]; ring
  have hquarter : horizontalLeft U + capWidth U / 4 = -C := by rw [hwidth, hleft]; ring
  have hrightMiddle : horizontalRight U - capWidth U / 4 = C := by rw [hwidth, hright]; ring
  have hinitial := (hU.leftCompanion_actual_initial_data hheight haffine).2.1
  rw [hquarter, hwidth] at hinitial
  have htail := hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime
    hregime hproper hheight haffine
  rw [hrightMiddle] at htail
  have htop := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime
    hregime hproper hheight haffine
  rw [hquarter] at heq
  refine ⟨ρ, hρ, hsharp, hcoarse, hzero, heq, ?_⟩
  by_contra hbad
  exact hU.false_of_leftCompanion_weighted_excess_of_tail_regime hregime hproper hheight haffine
    hleft hright hinitial htail hC0 hC1 (hU.terminal_cosine_square_cut hproper)
    (topOverhangLeft_nonneg U) (topOverhangRight_nonneg U) htop hρ
    (fun t => (hsharp t).1) hcoarse heq (le_of_not_gt hbad)

theorem IsJointCapMaximizer.exists_actual_leftCompanion_density_excess_gt
    {U : Set Plane} {α m c C : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hC0 : (1 / 2 : ℝ) ≤ C) (hC1 : C ≤ 37 / 50) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 8 * (|horizontalLeft U| + |horizontalRight U| + 1) + 24) ∧
      (∀ t ≤ max (Real.pi / 2) (affineNormalAngle m), ρ t = 0) ∧
      (upperCurvature (leftCompanionCap U (-C))).restrict (Ioo (Real.pi / 2) Real.pi) =
        (volume.restrict (Ioo (Real.pi / 2) Real.pi)).withDensity
          (fun t => ENNReal.ofReal (ρ t)) ∧
      (39 / 4400 : ℝ) * Real.cos α <
        terminalWeightedExcess (fun t => ρ (t + Real.pi / 2))
          (Real.arcsin (C - topOverhangLeft U)) := by
  exact IsJointCapMaximizer.exists_actual_leftCompanion_density_excess_gt_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine hleft
    hright hC0 hC1

end AmbidextrousSofa
