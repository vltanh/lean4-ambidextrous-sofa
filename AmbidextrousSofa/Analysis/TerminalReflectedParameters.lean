module

public import AmbidextrousSofa.Analysis.TerminalImpulseEnergy
public import AmbidextrousSofa.Analysis.TerminalTopProjection
public import AmbidextrousSofa.Analysis.PartialWidthBounds
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds

@[expose] public section

/-!
# Actual endpoint parameters for the proper reflected arc

The reflected initial span retains the literal right top overhang.
The reflected height is bounded through the actual partial endpoint
pressure, whose barrier includes the complete outgoing terminal wall.
The two middle orientations are distinguished only where their actual
terminal support points differ.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.terminalTailPoint_eq_middle_of_negative_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalTailPoint U α = (horizontalRight U - capWidth U / 4,
      capRoof U (horizontalRight U - capWidth U / 4)) := by
  have hαm := (hU.negative_remaining_tail_geometry_of_tail_regime hregime hproper hheight hm haffine).1
  have hmL : affineNormalAngle m < Real.pi / 2 := by
    have h := Real.arctan_lt_zero.mpr hm
    unfold affineNormalAngle
    linarith only [h]
  exact (hU.support_vertices_first_unused_gap haffine le_rfl hmL.le hαm
    (show affineNormalAngle m ∉ Ioo α (affineNormalAngle m) by simp)).1.trans
      (hU.middle_support_vertices hm.ne haffine).2

theorem IsJointCapMaximizer.terminalTailPoint_eq_middle_of_negative
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalTailPoint U α = (horizontalRight U - capWidth U / 4,
      capRoof U (horizontalRight U - capWidth U / 4)) := by
  exact IsJointCapMaximizer.terminalTailPoint_eq_middle_of_negative_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight hm haffine

theorem IsJointCapMaximizer.terminalTailPoint_snd_eq_one_of_nonneg
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (terminalTailPoint U α).2 = 1 := by
  unfold terminalTailPoint
  rw [hU.first_terminal_vplus_of_middle_nonneg hproper hm haffine,
    top_vminus_snd_eq_capHeight, hheight]

theorem IsJointCapMaximizer.terminalTailInset_eq_universal_of_nonneg
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalTailInset U α = terminalInset α := by
  unfold terminalTailInset terminalInset
  rw [hU.terminalTailPoint_snd_eq_one_of_nonneg hproper hheight hm haffine, one_mul]

theorem IsJointCapMaximizer.topOverhangRight_eq_zero_of_negative
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1) (hm : m < 0)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : topOverhangRight U = 0 := by
  have hneg : horizontalLeft U + capWidth U / 4 -
      (horizontalRight U - capWidth U / 4) ≤ 0 := by
    have hw := hU.isCap.capWidth_nonneg
    unfold capWidth at *
    linarith only [hw]
  unfold topOverhangRight
  rw [hU.top_vminus_of_negative_affine_middle hheight hm haffine]
  exact max_eq_right hneg

theorem IsJointCapMaximizer.terminalTailPoint_snd_eq_middle_right_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (terminalTailPoint U α).2 = capRoof U (horizontalRight U - capWidth U / 4) := by
  by_cases hm : m < 0
  · rw [hU.terminalTailPoint_eq_middle_of_negative_of_tail_regime hregime hproper hheight hm haffine]
  · rw [hU.terminalTailPoint_snd_eq_one_of_nonneg hproper hheight (le_of_not_gt hm) haffine,
      hU.middle_right_eq_one_of_affine_nonneg hheight (le_of_not_gt hm) haffine]

theorem IsJointCapMaximizer.terminalTailPoint_snd_eq_middle_right
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (terminalTailPoint U α).2 = capRoof U (horizontalRight U - capWidth U / 4) := by
  exact IsJointCapMaximizer.terminalTailPoint_snd_eq_middle_right_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine

theorem IsJointCapMaximizer.centered_terminalReflectedSpan_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalReflectedSpan U α = 3 * C + topOverhangRight U := by
  unfold terminalReflectedSpan
  rw [hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime hregime hproper hheight haffine]
  unfold capWidth
  rw [hl, hr]
  ring

theorem IsJointCapMaximizer.terminalReflectedHeight_nonneg_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : 0 ≤ terminalReflectedHeight U α := by
  have hroof := capRoof_nonneg hU.isCap.isCompact
    (fun p hp => (hU.isCap.inStrip hp).1) (horizontalLeft U)
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.2
  unfold terminalReflectedHeight
  linarith only [hroof, hH]

theorem IsJointCapMaximizer.terminalReflectedHeight_nonneg
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : 0 ≤ terminalReflectedHeight U α := by
  exact IsJointCapMaximizer.terminalReflectedHeight_nonneg_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hproper hheight haffine) hproper hheight haffine

/-- The endpoint pressure is the original proper pressure. In particular
the final term below contains the outgoing whole first wall. -/
theorem IsJointCapMaximizer.centered_terminalReflectedHeight_le_barrier_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalReflectedHeight U α ≤ 1 / 2 +
      5 / 4 * (1 - (terminalTailPoint U α).2) + 3 / 4 * partialBarrier U α (-C) := by
  have hEP := (hU.partial_endpoint_heights_eq_pressures_of_affine
    hproper hheight ⟨m, c, haffine⟩).2
  have hH := hU.terminalTailPoint_snd_eq_middle_right_of_tail_regime hregime hproper hheight haffine
  have hleft : horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 = -C := by
    rw [hl, hr]
    ring
  have hright : horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 = C := by
    rw [hl, hr]
    ring
  unfold partialLeftEndpointPressure leftEndpointPressure at hEP
  rw [hleft, hright] at hEP
  change (terminalTailPoint U α).2 = capRoof U
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) at hH
  rw [hright] at hH
  have hlow := capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (-C)
  have hq := partialBarrier_nonneg U α C
  unfold terminalReflectedHeight
  linarith only [hEP, hH, hlow, hq]

theorem IsJointCapMaximizer.centered_firstWall_le_terminalSlope_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    firstWall U α (-C) < 2 * C * terminalSlope α := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith only [hproper, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hU.angle_pos, Real.pi_pos], hproper⟩
  have hzero := (hU.terminal_top_projection_bound_of_tail_regime hregime hproper hheight haffine).2.2.2
  have hright : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  rw [hright] at hzero
  rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
  change terminalSlope α * (terminalTailZero U α - -C) < 2 * C * terminalSlope α
  nlinarith only [mul_pos (terminalSlope_pos hU.angle_pos hproper) (sub_pos.mpr hzero)]

theorem IsJointCapMaximizer.centered_firstWall_le_terminalSlope_of_nonneg_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    firstWall U α (-C) ≤ terminalSlope α * (2 * C - terminalInset α / 2) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith only [hproper, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hU.angle_pos, Real.pi_pos], hproper⟩
  have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper hheight haffine
  rw [hU.terminalTailInset_eq_universal_of_nonneg hproper hheight hm haffine] at hTP
  have hTR : topOverhangRight U ≤ terminalInset α / 2 := by
    linarith only [hTP, topOverhangLeft_nonneg U]
  have hright : horizontalRight U - capWidth U / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  rw [firstWall_eq_terminalTail U hs.ne' hc.ne']
  unfold terminalTailZero
  rw [hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime hregime hproper hheight haffine,
    hright, hU.terminalTailInset_eq_universal_of_nonneg hproper hheight hm haffine]
  change terminalSlope α * (C + topOverhangRight U - terminalInset α - -C) ≤ _
  exact mul_le_mul_of_nonneg_left (by linarith only [hTR])
    (terminalSlope_pos hU.angle_pos hproper).le

theorem terminalSlope_outgoing_nonneg_bound {α C : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hκ : terminalSlope α ≤ 3 / 8) (hs : 14 / 15 ≤ Real.sin α)
    (hC : C ≤ 37 / 50) :
    terminalSlope α * (2 * C - terminalInset α / 2) < 419 / 800 := by
  have hκ0 := terminalSlope_pos hα0 hαL
  have hk0 := terminalInset_pos hα0 hαL
  have hkc := terminalInset_mul_one_add_sin hα0 hαL
  have hκs : terminalSlope α * Real.sin α = Real.cos α :=
    div_mul_cancel₀ _ (show Real.sin α ≠ 0 by linarith only [hs])
  have hk : 7 / 15 * terminalSlope α ≤ terminalInset α := by
    have hsmall := mul_le_mul_of_nonneg_left (Real.sin_le_one α) hk0.le
    have hlarge := mul_le_mul_of_nonneg_left hs hκ0.le
    nlinarith only [hkc, hκs, hsmall, hlarge]
  have hfirst := mul_le_mul_of_nonneg_left hC hκ0.le
  have hsecond := mul_le_mul_of_nonneg_left hk hκ0.le
  have hmono := mul_nonneg (sub_nonneg.mpr hκ)
    (show 0 ≤ 37 / 25 - 7 / 30 * (3 / 8 + terminalSlope α) by linarith only [hκ])
  nlinarith only [hfirst, hsecond, hmono]

theorem IsJointCapMaximizer.centered_terminal_reflected_near_full_parameters_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) (hκ : terminalSlope α ≤ 1 / 8) :
    3 / 2 < terminalReflectedSpan U α ∧ terminalReflectedSpan U α < 563 / 250 ∧
      0 ≤ terminalReflectedHeight U α ∧ terminalReflectedHeight U α < 19 / 25 := by
  have hw : capWidth U / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hw] at hC
  obtain ⟨hs, _, _, hk⟩ := terminal_near_full_bounds hU.angle_pos hproper hκ
  have hbox := (hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
    (by linarith only [hC.1]) (by linarith only [hC.2])).1
  have hHbox := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths
    (by linarith only [hC.1]) hC.2.le
  have hn := (sweptNiche_mono_terminalAngle hU.isCap.isCompact hU.angle_pos hproper.le
    le_rfl (-C)).trans hbox
  change sweptNiche U α (-C) ≤ Analysis.tiltedBoxHeight C at hn
  have hwall := hU.centered_firstWall_le_terminalSlope_of_tail_regime hregime hproper hl hr hheight haffine
  have hwallsmall : firstWall U α (-C) < 1 / 3 := by
    have hprod := mul_le_mul_of_nonneg_left hκ (show 0 ≤ 2 * C by linarith only [hC.1])
    nlinarith only [hwall, hprod, hC.2]
  have hq : partialBarrier U α (-C) < 1 / 3 :=
    max_lt (by linarith only [hn, hHbox]) hwallsmall
  have he := hU.centered_terminalReflectedHeight_le_barrier_of_tail_regime
    hregime hproper hl hr hheight haffine
  have htail := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  have he1 : terminalReflectedHeight U α < 19 / 25 := by
    linarith only [he, hq, htail, hs]
  have hd := hU.centered_terminalReflectedSpan_of_tail_regime hregime hproper hl hr hheight haffine
  have hTR : topOverhangRight U < 1 / 32 := by
    by_cases hm : m < 0
    · rw [hU.topOverhangRight_eq_zero_of_negative hheight hm haffine]
      norm_num
    · have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime
        hregime hproper hheight haffine
      rw [hU.terminalTailInset_eq_universal_of_nonneg
        hproper hheight (le_of_not_gt hm) haffine] at hTP
      linarith only [hTP, hk, topOverhangLeft_nonneg U]
  exact ⟨by linarith only [hd, hC.1, topOverhangRight_nonneg U],
    by linarith only [hd, hC.2, hTR],
    hU.terminalReflectedHeight_nonneg_of_tail_regime hregime hproper hheight haffine, he1⟩

theorem IsJointCapMaximizer.centered_terminal_reflected_parameters_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    3 / 2 < terminalReflectedSpan U α ∧ 0 ≤ terminalReflectedHeight U α ∧
      ((m < 0 ∧ terminalReflectedSpan U α < 111 / 50 ∧ terminalReflectedHeight U α < 1) ∨
       (0 ≤ m ∧ terminalReflectedSpan U α < 2311 / 1000 ∧
         terminalReflectedHeight U α < 179 / 200)) := by
  have hw : capWidth U / 4 = C := by unfold capWidth; rw [hl, hr]; ring
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hw] at hC
  have hκ := hU.proper_terminalSlope_lt_three_eighths hproper
  have hκ0 := terminalSlope_pos hU.angle_pos hproper
  have hs : 14 / 15 < Real.sin α := by
    have h := (terminal_sin_cos_bounds_after_initialAngle
      hU.terminal_angle_gt_arctan_eight_thirds.le hproper).1
    linarith only [h]
  have hn := (sweptNiche_mono_terminalAngle hU.isCap.isCompact hU.angle_pos hproper.le
    le_rfl (-C)).trans (hU.isCap.middle_niche_le_box_height_of_endpoints hl hr
      (by linarith only [hC.1]) (by linarith only [hC.2])).1
  have hHbox := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths
    (by linarith only [hC.1]) hC.2.le
  change sweptNiche U α (-C) ≤ Analysis.tiltedBoxHeight C at hn
  have hd := hU.centered_terminalReflectedSpan_of_tail_regime hregime hproper hl hr hheight haffine
  have he := hU.centered_terminalReflectedHeight_le_barrier_of_tail_regime
    hregime hproper hl hr hheight haffine
  have htail := (hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine).2.1
  refine ⟨by linarith only [hd, hC.1, topOverhangRight_nonneg U],
    hU.terminalReflectedHeight_nonneg_of_tail_regime hregime hproper hheight haffine, ?_⟩
  by_cases hm : m < 0
  · have hTR := hU.topOverhangRight_eq_zero_of_negative hheight hm haffine
    have hwall := hU.centered_firstWall_le_terminalSlope_of_tail_regime hregime hproper hl hr hheight haffine
    have hwallsmall : firstWall U α (-C) < 111 / 200 := by
      have hp := mul_le_mul_of_nonneg_left hκ.le (show 0 ≤ 2 * C by linarith only [hC.1])
      nlinarith only [hwall, hp, hC.2]
    have hq : partialBarrier U α (-C) < 111 / 200 :=
      max_lt (by linarith only [hn, hHbox]) hwallsmall
    exact Or.inl ⟨hm, by linarith only [hd, hTR, hC.2],
      by linarith only [he, hq, htail, hs]⟩
  · have hwall := (hU.centered_firstWall_le_terminalSlope_of_nonneg_of_tail_regime hregime hproper
      hl hr hheight (le_of_not_gt hm) haffine).trans_lt
      (terminalSlope_outgoing_nonneg_bound hU.angle_pos hproper hκ.le hs.le hC.2.le)
    have hq : partialBarrier U α (-C) < 419 / 800 :=
      max_lt (by linarith only [hn, hHbox]) hwall
    have hH := hU.terminalTailPoint_snd_eq_one_of_nonneg
      hproper hheight (le_of_not_gt hm) haffine
    have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper hheight haffine
    rw [hU.terminalTailInset_eq_universal_of_nonneg
      hproper hheight (le_of_not_gt hm) haffine] at hTP
    have hk := terminalInset_lt_two_elevenths_of_slope_le hU.angle_pos hproper hκ.le
    exact Or.inr ⟨le_of_not_gt hm,
      by linarith only [hd, hC.2, hTP, hk, topOverhangLeft_nonneg U],
      by linarith only [he, hq, hH]⟩

end AmbidextrousSofa
