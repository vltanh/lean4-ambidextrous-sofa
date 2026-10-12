module

public import AmbidextrousSofa.Analysis.TerminalImpulseEnergy
public import AmbidextrousSofa.Analysis.TerminalTopProjection
public import AmbidextrousSofa.Analysis.PartialWidthBounds
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.ProperExcessBudget

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

open Analysis

theorem IsJointCapMaximizer.terminalTailInset_eq_universal_of_nonneg
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalTailInset U α = terminalInset α := by
  rw [terminalTailInset, terminalInset,
    hU.terminalTailPoint_eq_of_nonneg hproper hheight hm haffine, one_mul]

/-- The data shared by both parameter bounds. The endpoint pressure is the
original proper pressure, so the height bound contains the outgoing whole
first wall at the left middle endpoint, whose historical part is below the
box height. -/
theorem IsJointCapMaximizer.centered_terminal_reflected_data_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < C ∧ C < 37 / 50 ∧ terminalReflectedSpan U α = 3 * C + topOverhangRight U ∧
      0 ≤ terminalReflectedHeight U α ∧
      terminalReflectedHeight U α ≤ 1 / 2 + 5 / 4 * (1 - (terminalTailPoint U α).2) +
        3 / 4 * max (1 / 3) (firstWall U α (-C)) ∧
      Real.sin α < (terminalTailPoint U α).2 ∧
      firstWall U α (-C) = terminalSlope α * (2 * C + topOverhangRight U - terminalTailInset U α) ∧
      topOverhangLeft U + 2 * topOverhangRight U ≤ terminalTailInset U α ∧
      topOverhangRight U < terminalTailInset U α := by
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hU.angle_pos, hproper⟩
  have hw : capWidth U / 4 = C := by rw [capWidth, hl, hr]; ring
  have hRC : horizontalRight U - capWidth U / 4 = C := (centered_quarter_points hl hr).2.1
  have hC := hU.proper_quarter_width_bounds hproper
  rw [hw] at hC
  obtain ⟨-, hH, hH1⟩ := hU.terminalTailPoint_bounds_of_tail_regime hregime hproper hheight haffine
  have hfst := hU.terminalTailPoint_fst_eq_middle_add_topOverhangRight_of_tail_regime hregime
    hproper hheight haffine
  rw [hRC] at hfst
  have hHC : (terminalTailPoint U α).2 = capRoof U C := by
    rw [← hRC]
    rcases lt_or_ge m 0 with hm | hm
    · rw [hU.terminalTailPoint_eq_of_negative hregime hm haffine]
    · rw [hU.terminalTailPoint_eq_of_nonneg hproper hheight hm haffine,
        hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine]
  have hEP := (hU.partial_endpoint_heights_eq_pressures_of_affine hproper hheight
    ⟨m, c, haffine⟩).2
  rw [partialLeftEndpointPressure, leftEndpointPressure, (centered_quarter_points hl hr).1,
    (centered_quarter_points hl hr).2.1] at hEP
  have hnbox := (sweptNiche_mono_terminalAngle hU.isCap.isCompact hU.angle_pos hproper.le le_rfl (-C)).trans
    (hU.isCap.middle_niche_le_box_height_of_endpoints hl hr (by linarith only [hC.1])
      (by linarith only [hC.2])).1
  have hroot : (2 / 3 : ℝ) < Real.sqrt (1 - C ^ 2) :=
    (Real.lt_sqrt (by norm_num)).2 (by nlinarith only [hC.1, hC.2])
  have hn : sweptNiche U α (-C) < 1 / 3 := by linarith only [hnbox, hroot]
  have hroof := capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1)
    (horizontalLeft U)
  have hTP := hU.topOverhangLeft_add_twice_right_le_terminalInset_of_tail_regime hregime hproper
    hheight haffine
  refine ⟨hC.1, hC.2, by rw [terminalReflectedSpan, hfst, hl]; ring,
    by rw [terminalReflectedHeight]; linarith only [hroof, hH1], ?_, hH, ?_, hTP,
    by linarith only [hTP, topOverhangLeft_nonneg U, topOverhangRight_nonneg U,
      (hU.isCap.terminalTailInset_bounds hU.angle_pos hproper hH).1]⟩
  · rw [terminalReflectedHeight]
    linarith only [hEP, hHC, capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip (-C),
      partialBarrier_nonneg U α C,
      show partialBarrier U α (-C) ≤ max (1 / 3) (firstWall U α (-C)) from
        max_le_max hn.le le_rfl]
  · rw [firstWall_eq_terminalTail U hs.ne' hc.ne', terminalTailZero, hfst]
    change terminalSlope α * _ = _
    ring

/-- Top overhang and descending height spend the same angular stopping budget. -/
theorem IsJointCapMaximizer.centered_terminal_reflected_angular_budget_of_tail_regime
    {U : Set Plane} {α C m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m) (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = m * x + c) :
    3 / 2 < terminalReflectedSpan U α ∧
    terminalReflectedSpan U α ≤ properBaselineSpan + terminalSlope α / 4 ∧
    0 ≤ terminalReflectedHeight U α ∧ terminalReflectedHeight U α ≤ 1 ∧
    (3 / 2) * max (terminalReflectedSpan U α - properBaselineSpan) 0 +
      (9 / 10) * max (terminalReflectedHeight U α - 3 / 4 -
        (3 / 4) * properPressureExcess (terminalSlope α)) 0 ≤ (3 / 8) * terminalSlope α := by
  obtain ⟨hC0, hC1, hd, he0, he, hH, hwall, hTP, hTR⟩ :=
    hU.centered_terminal_reflected_data_of_tail_regime hregime hproper hl hr hheight haffine
  have hk := hU.proper_terminalSlope_lt_three_eighths hproper
  have hk0 := terminalSlope_pos hU.angle_pos hproper
  have hsin := (sin_cos_pos_of_mem_quarter ⟨hU.angle_pos, hproper⟩).1
  have hg : 0 ≤ properPressureExcess (terminalSlope α) := le_max_right _ _
  have hwall1 : firstWall U α (-C) ≤ (37 / 25) * terminalSlope α := by
    linarith only [hwall, mul_le_mul_of_nonneg_left hC1.le hk0.le,
      mul_nonneg hk0.le (sub_nonneg.2 hTR.le)]
  have hmax : max (1 / 3) (firstWall U α (-C)) ≤
      1 / 3 + properPressureExcess (terminalSlope α) :=
    max_le (by linarith only [hg]) (by
      linarith only [hwall1, le_max_left ((37 / 25) * terminalSlope α - 1 / 3) 0])
  have heBudget : terminalReflectedHeight U α ≤ 3 / 4 +
      (5 / 4) * (1 - (terminalTailPoint U α).2) + (3 / 4) * properPressureExcess (terminalSlope α) := by
    linarith only [he, hmax]
  have hbase : 3 / 2 < terminalReflectedSpan U α := by
    linarith only [hd, hC0, topOverhangRight_nonneg U]
  rcases lt_or_ge m 0 with hm | hm
  · have hzero := hU.topOverhangRight_eq_zero_of_negative hheight hm haffine
    rw [hzero] at hd hwall
    have hdLimit : terminalReflectedSpan U α ≤ properBaselineSpan + terminalSlope α / 4 := by
      unfold properBaselineSpan; linarith only [hd, hC1, hk0]
    have hloss : 1 - (terminalTailPoint U α).2 ≤ terminalSlope α ^ 2 / 2 :=
      (by linarith only [hH] : 1 - (terminalTailPoint U α).2 ≤ 1 - Real.sin α).trans
        (terminal_height_loss_le_half_slope_sq hU.angle_pos hproper)
    have hwallLoss : firstWall U α (-C) + (1 - (terminalTailPoint U α).2) ≤
        (37 / 25) * terminalSlope α := by
      linarith only [hwall, terminalSlope_mul_tailInset U hU.angle_pos hproper,
        mul_le_mul_of_nonneg_left hC1.le hk0.le,
        mul_nonneg hk0.le (terminalInset_pos hU.angle_pos hproper).le]
    have hmaxOne : max (1 / 3) (firstWall U α (-C)) ≤
        2 / 3 - (5 / 3) * (1 - (terminalTailPoint U α).2) := by
      apply max_le
      · nlinarith only [hloss, hk0, hk]
      · nlinarith only [hloss, hwallLoss, hk0, hk]
    have heOne : terminalReflectedHeight U α ≤ 1 := by linarith only [he, hmaxOne]
    have hdmax : max (terminalReflectedSpan U α - properBaselineSpan) 0 = 0 := by
      rw [max_eq_right]; unfold properBaselineSpan; linarith only [hd, hC1]
    have hheight : max (terminalReflectedHeight U α - 3 / 4 -
        (3 / 4) * properPressureExcess (terminalSlope α)) 0 ≤ (5 / 8) * terminalSlope α ^ 2 :=
      max_le (by linarith only [heBudget, hloss]) (by positivity)
    refine ⟨hbase, hdLimit, he0, heOne, ?_⟩
    rw [hdmax, mul_zero, zero_add]
    nlinarith only [hheight, hk0, hk]
  · rw [hU.terminalTailInset_eq_universal_of_nonneg hproper hheight hm haffine] at hTP
    have hHone := congrArg Prod.snd (hU.terminalTailPoint_eq_of_nonneg hproper hheight hm haffine)
    dsimp only at hHone
    rw [hHone] at heBudget
    have hdLimit : terminalReflectedSpan U α ≤ properBaselineSpan + terminalSlope α / 4 := by
      unfold properBaselineSpan
      linarith only [hd, hC1, hTP, topOverhangLeft_nonneg U,
        terminalInset_le_half_slope hU.angle_pos hproper]
    have hg1 : properPressureExcess (terminalSlope α) ≤ 1 / 3 := by
      apply max_le <;> linarith only [hk]
    have heOne : terminalReflectedHeight U α ≤ 1 := by linarith only [heBudget, hg1]
    have hem : max (terminalReflectedHeight U α - 3 / 4 -
        (3 / 4) * properPressureExcess (terminalSlope α)) 0 = 0 := by
      rw [max_eq_right]; linarith only [heBudget]
    have hright : terminalReflectedSpan U α - properBaselineSpan ≤ terminalSlope α / 4 := by
      unfold properBaselineSpan
      linarith only [hd, hC1, hTP, topOverhangLeft_nonneg U,
        terminalInset_le_half_slope hU.angle_pos hproper]
    have hmaxRight : max (terminalReflectedSpan U α - properBaselineSpan) 0 ≤ terminalSlope α / 4 :=
      max_le hright (by linarith only [hk0])
    have hmul := mul_le_mul_of_nonneg_left hmaxRight (by norm_num : (0 : ℝ) ≤ 3 / 2)
    refine ⟨hbase, hdLimit, he0, heOne, ?_⟩
    rw [hem, mul_zero, add_zero]
    linarith only [hmul]

end AmbidextrousSofa
