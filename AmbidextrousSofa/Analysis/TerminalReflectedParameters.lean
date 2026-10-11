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
    1001 / 2000 < C ∧ C < 37 / 50 ∧ terminalReflectedSpan U α = 3 * C + topOverhangRight U ∧
      0 ≤ terminalReflectedHeight U α ∧
      terminalReflectedHeight U α ≤ 1 / 2 + 5 / 4 * (1 - (terminalTailPoint U α).2) +
        3 / 4 * max (33 / 100) (firstWall U α (-C)) ∧
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
  have hn : sweptNiche U α (-C) < 33 / 100 :=
    ((sweptNiche_mono_terminalAngle hU.isCap.isCompact hU.angle_pos hproper.le le_rfl (-C)).trans
      (hU.isCap.middle_niche_le_box_height_of_endpoints hl hr (by linarith only [hC.1])
        (by linarith only [hC.2])).1).trans_lt
      (Analysis.tiltedBoxHeight_lt_thirty_three_hundredths (by linarith only [hC.1]) hC.2.le)
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
      show partialBarrier U α (-C) ≤ max (33 / 100) (firstWall U α (-C)) from
        max_le_max hn.le le_rfl]
  · rw [firstWall_eq_terminalTail U hs.ne' hc.ne', terminalTailZero, hfst]
    change terminalSlope α * _ = _
    ring

theorem terminalSlope_outgoing_nonneg_bound {α C : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hκ : terminalSlope α ≤ 3 / 8) (hs : 14 / 15 ≤ Real.sin α)
    (hC : C ≤ 37 / 50) :
    terminalSlope α * (2 * C - terminalInset α / 2) < 419 / 800 := by
  have hκ0 := terminalSlope_pos hα0 hαL
  have hk : 7 / 15 * terminalSlope α ≤ terminalInset α := by
    linarith only [terminalInset_mul_one_add_sin hα0 hαL,
      show terminalSlope α * Real.sin α = Real.cos α from
        div_mul_cancel₀ _ (by linarith only [hs]),
      mul_le_mul_of_nonneg_left (Real.sin_le_one α) (terminalInset_pos hα0 hαL).le,
      mul_le_mul_of_nonneg_left hs hκ0.le]
  linarith only [mul_le_mul_of_nonneg_left hC hκ0.le, mul_le_mul_of_nonneg_left hk hκ0.le,
    mul_nonneg (sub_nonneg.mpr hκ)
      (show 0 ≤ 37 / 25 - 7 / 30 * (3 / 8 + terminalSlope α) by linarith only [hκ])]

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
  obtain ⟨hC0, hC1, hd, hh0, he, hH, hwall, hTP, hTR⟩ :=
    hU.centered_terminal_reflected_data_of_tail_regime hregime hproper hl hr hheight haffine
  obtain ⟨hs, -, -, hk⟩ := terminal_near_full_bounds hU.angle_pos hproper hκ
  have hq : max (33 / 100) (firstWall U α (-C)) < 1 / 3 := max_lt (by norm_num) (by
    linarith only [hwall, hC1, mul_lt_mul_of_pos_left hTR (terminalSlope_pos hU.angle_pos hproper),
      mul_le_mul_of_nonneg_left hκ (show 0 ≤ 2 * C by linarith only [hC0])])
  have hTR' : topOverhangRight U < 1 / 32 := by
    rcases lt_or_ge m 0 with hm | hm
    · rw [hU.topOverhangRight_eq_zero_of_negative hheight hm haffine]
      norm_num
    · rw [hU.terminalTailInset_eq_universal_of_nonneg hproper hheight hm haffine] at hTP
      linarith only [hTP, hk, topOverhangLeft_nonneg U]
  exact ⟨by linarith only [hd, hC0, topOverhangRight_nonneg U], by linarith only [hd, hC1, hTR'],
    hh0, by linarith only [he, hq, hH, hs]⟩

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
  obtain ⟨hC0, hC1, hd, hh0, he, hH, hwall, hTP, hTR⟩ :=
    hU.centered_terminal_reflected_data_of_tail_regime hregime hproper hl hr hheight haffine
  have hκ := hU.proper_terminalSlope_lt_three_eighths hproper
  have hκ0 := terminalSlope_pos hU.angle_pos hproper
  have hs : 14 / 15 < Real.sin α := by
    linarith only [(terminal_sin_cos_bounds_after_initialAngle
      hU.terminal_angle_gt_arctan_eight_thirds.le hproper).1]
  refine ⟨by linarith only [hd, hC0, topOverhangRight_nonneg U], hh0, ?_⟩
  rcases lt_or_ge m 0 with hm | hm
  · have hq : max (33 / 100) (firstWall U α (-C)) < 111 / 200 := max_lt (by norm_num) (by
      linarith only [hwall, hC1, mul_lt_mul_of_pos_left hTR hκ0,
        mul_lt_mul_of_pos_left hκ (show 0 < 2 * C by linarith only [hC0])])
    exact Or.inl ⟨hm, by linarith only [hd, hC1,
      hU.topOverhangRight_eq_zero_of_negative hheight hm haffine],
      by linarith only [he, hq, hH, hs]⟩
  · rw [hU.terminalTailInset_eq_universal_of_nonneg hproper hheight hm haffine] at hwall hTP
    have hH1 := congrArg Prod.snd (hU.terminalTailPoint_eq_of_nonneg hproper hheight hm haffine)
    have hq : max (33 / 100) (firstWall U α (-C)) < 419 / 800 := max_lt (by norm_num) (by
      linarith only [hwall, terminalSlope_outgoing_nonneg_bound hU.angle_pos hproper hκ.le hs.le
        hC1.le, mul_le_mul_of_nonneg_left (show topOverhangRight U ≤ terminalInset α / 2 by
          linarith only [hTP, topOverhangLeft_nonneg U]) hκ0.le])
    exact Or.inr ⟨hm, by linarith only [hd, hC1, hTP, topOverhangLeft_nonneg U,
      terminalInset_lt_two_elevenths_of_slope_le hU.angle_pos hproper hκ.le],
      by linarith only [he, hq, hH1]⟩

end AmbidextrousSofa
