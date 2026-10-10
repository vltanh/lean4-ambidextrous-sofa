module

public import AmbidextrousSofa.Analysis.TerminalFacetAtom
public import AmbidextrousSofa.Analysis.InitialAngleExclusion
public import AmbidextrousSofa.Analysis.InitialAngleWidth

@[expose] public section

/-!
# Actual terminal corner separation and the terminal face bound

The initial-angle and preliminary-width exclusions are inequalities for
the literal partial cap score. Their exact rational consequences already
separate the actual terminal corner from the shifted upper face endpoint;
no later source-moment width cut is needed.

Combining that separation with the literal fixed-cap angle extension
bounds the complete terminal curvature atom at every largest-angle
canonical joint maximizer. The proof preserves the original orientation
and works for all signs of the affine middle roof.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem terminal_sin_cos_bounds_after_initialAngle {α : ℝ}
    (hα0 : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) :
    (187 / 200 : ℝ) < Real.sin α ∧ Real.cos α < (9 / 25 : ℝ) := by
  have hαpos : 0 < α :=
    (Real.arctan_pos.mpr (by norm_num : (0 : ℝ) < 8 / 3)).trans_le hα0
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have htan : (8 / 3 : ℝ) ≤ Real.tan α := by
    have h := Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo (8 / 3))
      (show α ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], hαL⟩) hα0
    simpa only [Real.tan_arctan] using h
  rw [Real.tan_eq_sin_div_cos] at htan
  have hsc : 8 * Real.cos α ≤ 3 * Real.sin α := by
    have h := (le_div_iff₀ hc).mp htan
    linarith only [h]
  have hprod := mul_nonneg (sub_nonneg.mpr hsc)
    (show 0 ≤ 3 * Real.sin α + 8 * Real.cos α by positivity)
  have hcircle := Real.sin_sq_add_cos_sq α
  constructor
  · by_contra hbad
    have hle : Real.sin α ≤ (187 / 200 : ℝ) := le_of_not_gt hbad
    have hsq := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ 187 / 200 + Real.sin α by positivity)
    nlinarith only [hcircle, hprod, hsq]
  · by_contra hbad
    have hle : (9 / 25 : ℝ) ≤ Real.cos α := le_of_not_gt hbad
    have hsq := mul_nonneg (sub_nonneg.mpr hle)
      (show 0 ≤ Real.cos α + 9 / 25 by positivity)
    nlinarith only [hcircle, hprod, hsq]

theorem terminalTailZero_sub_rightAbscissa (U : Set Plane) (α : ℝ) :
    terminalTailZero U α - terminalFirstRightAbscissa U α = terminalTailReserve U α := by
  unfold terminalTailZero terminalFirstRightAbscissa terminalTailReserve terminalTailPoint
  ring

/-- The terminal companion support is the actual upper left projection
point. The first support is the actual upper terminal-face endpoint. -/
theorem IsJointCapMaximizer.terminal_corner_difference
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (attachedCorner U α).1 - terminalFirstRightAbscissa U α =
      Real.sin α * (1 - ((terminalTailPoint U α).1 - horizontalLeft U) * Real.sin α +
        ((terminalTailPoint U α).2 - capRoof U (horizontalLeft U)) * Real.cos α) := by
  have hf : support U (unitNormal α) = (terminalTailPoint U α).1 * Real.cos α +
      (terminalTailPoint U α).2 * Real.sin α := (MovingSofaOptimality.dot_vplus_uvec U α).symm
  have hg := hU.companion_tail_support hαL haffine
    (show α ∈ Icc α (Real.pi / 2) from ⟨le_rfl, hαL.le⟩)
  have hcircle := congrArg (fun v : ℝ => (terminalTailPoint U α).1 * v)
    (Real.sin_sq_add_cos_sq α)
  unfold attachedCorner terminalFirstRightAbscissa
  rw [hf, hg]
  dsimp only [terminalTailPoint] at *
  nlinarith only [hcircle]

/-- The preliminary width `49/25` is already sufficient. Its exact
margin is `3*(49/100)*(187/200)-9/25 = 20289/20000 > 1`. -/
theorem IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_width_angle_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hwidth : (49 / 25 : ℝ) ≤ capWidth U) (hangle : Real.arctan (8 / 3) ≤ α) :
    (attachedCorner U α).1 < terminalFirstRightAbscissa U α := by
  have htail := hU.terminalTailPoint_bounds_of_tail_regime hregime hαL hheight haffine
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hU.angle_pos, Real.pi_pos], hαL⟩
  have htrig := terminal_sin_cos_bounds_after_initialAngle hangle hαL
  have hdisp : (147 / 100 : ℝ) ≤ (terminalTailPoint U α).1 - horizontalLeft U := by
    have hmiddle : 3 * capWidth U / 4 ≤
        (terminalTailPoint U α).1 - horizontalLeft U := by
      have hb := htail.1
      unfold capWidth at hb ⊢
      linarith
    linarith only [hmiddle, hwidth]
  have hprod : (147 / 100 : ℝ) * (187 / 200) <
      ((terminalTailPoint U α).1 - horizontalLeft U) * Real.sin α :=
    (mul_lt_mul_of_pos_left htrig.1 (by norm_num : (0 : ℝ) < 147 / 100)).trans_le
      (mul_le_mul_of_nonneg_right hdisp hs.le)
  have he0 : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _
  have hheightDiff : (terminalTailPoint U α).2 - capRoof U (horizontalLeft U) ≤ 1 := by
    linarith [htail.2.2]
  have hheightProd : ((terminalTailPoint U α).2 - capRoof U (horizontalLeft U)) * Real.cos α ≤
      Real.cos α := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hheightDiff hc.le
  have hgap : 1 - ((terminalTailPoint U α).1 - horizontalLeft U) * Real.sin α +
      ((terminalTailPoint U α).2 - capRoof U (horizontalLeft U)) * Real.cos α < 0 := by
    nlinarith only [hprod, hheightProd, htrig.2]
  have hnegative := mul_neg_of_pos_of_neg hs hgap
  rw [← hU.terminal_corner_difference hαL haffine] at hnegative
  exact sub_neg.mp hnegative

theorem IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_width_angle
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hwidth : (49 / 25 : ℝ) ≤ capWidth U) (hangle : Real.arctan (8 / 3) ≤ α) :
    (attachedCorner U α).1 < terminalFirstRightAbscissa U α := by
  exact IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_width_angle_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine hwidth hangle

/-- The angle and width assumptions above are supplied by actual scalar
score exclusions for this same maximizer. -/
theorem IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (attachedCorner U α).1 < terminalFirstRightAbscissa U α :=
  hU.terminal_corner_lt_rightAbscissa_of_width_angle_of_tail_regime hregime hαL hheight haffine
    (hU.width_gt_forty_nine_twenty_fifths hαL).le
    hU.terminal_angle_gt_arctan_eight_thirds.le

theorem IsJointCapMaximizer.terminal_corner_lt_rightAbscissa
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (attachedCorner U α).1 < terminalFirstRightAbscissa U α := by
  exact IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

/-- The complete horizontal width of the actual first terminal facet is
bounded at the canonical maximizer selected with largest terminal angle. -/
theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalFaceWidth U α ≤ terminalTailReserve U α :=
  hU.terminalFaceWidth_le_reserve_of_corner_lt_of_tail_regime hregime hαL hheight haffine
    (hU.terminal_corner_lt_rightAbscissa_of_tail_regime hregime hαL hheight haffine)

theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalFaceWidth U α ≤ terminalTailReserve U α := by
  exact IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

theorem IsJointCapMaximizer.terminalFaceWidth_lt_half_cos_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalFaceWidth U α < Real.cos α / 2 := by
  have hH := (hU.terminalTailPoint_bounds_of_tail_regime hregime hαL hheight haffine).2.1
  obtain ⟨_, _, _, _, hreserve⟩ := hU.isCap.terminalTailInset_bounds hU.angle_pos hαL hH
  exact (hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine).trans_lt hreserve

theorem IsJointCapMaximizer.terminalFaceWidth_lt_half_cos
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalFaceWidth U α < Real.cos α / 2 := by
  exact IsJointCapMaximizer.terminalFaceWidth_lt_half_cos_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

theorem IsJointCapMaximizer.terminal_curvature_atom_le_reserve_div_sin_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (upperCurvature U {α}).toReal ≤ terminalTailReserve U α / Real.sin α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos
    (by linarith [Real.pi_pos])
  apply (le_div_iff₀ hs).mpr
  rw [← hU.isCap.terminalFaceWidth_eq_curvature_atom α]
  exact hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine

theorem IsJointCapMaximizer.terminal_curvature_atom_le_reserve_div_sin
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (upperCurvature U {α}).toReal ≤ terminalTailReserve U α / Real.sin α := by
  exact IsJointCapMaximizer.terminal_curvature_atom_le_reserve_div_sin_of_tail_regime hU
    (hU.properTailRegime_of_largest hLargest hαL hheight haffine) hαL hheight haffine

end AmbidextrousSofa
