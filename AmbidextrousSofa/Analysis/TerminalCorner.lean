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
bounds the complete terminal curvature atom in the proper tail regime,
which every largest-angle canonical joint maximizer satisfies. The proof
preserves the original orientation and works for all signs of the affine
middle roof.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem terminal_sin_cos_bounds_after_initialAngle {α : ℝ}
    (hα0 : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) :
    (187 / 200 : ℝ) < Real.sin α ∧ Real.cos α < (9 / 25 : ℝ) := by
  have hαpos : 0 < α := (Real.arctan_pos.2 (by norm_num)).trans_le hα0
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hαpos (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hαL⟩
  have htan : 8 / 3 ≤ Real.tan α := by
    simpa using Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo _)
      ⟨by linarith [Real.pi_pos], hαL⟩ hα0
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at htan
  constructor <;> nlinarith [Real.sin_sq_add_cos_sq α]

/-- The preliminary width `49/25` and the initial angle `arctan (8/3)`, both supplied by actual
scalar score exclusions for this same maximizer, already separate the terminal corner from the
upper face endpoint. The exact margin is `3*(49/100)*(187/200)-9/25 = 20289/20000 > 1`. -/
theorem IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (attachedCorner U α).1 < terminalFirstRightAbscissa U α := by
  set P := terminalTailPoint U α
  have htail := hU.terminalTailPoint_bounds_of_tail_regime hregime hαL hheight haffine
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hU.angle_pos, Real.pi_pos], hαL⟩
  have htrig := terminal_sin_cos_bounds_after_initialAngle
    hU.terminal_angle_gt_arctan_eight_thirds.le hαL
  have hwidth := hU.width_gt_forty_nine_twenty_fifths hαL
  have he0 : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _
  have hdisp : (147 / 100 : ℝ) ≤ P.1 - horizontalLeft U := by
    have := htail.1
    unfold capWidth at *
    linarith
  -- The corner lies left of the abscissa by `sin α` times a negative bracket.
  have hdiff : (attachedCorner U α).1 - terminalFirstRightAbscissa U α = Real.sin α *
      (1 - (P.1 - horizontalLeft U) * Real.sin α + (P.2 - capRoof U (horizontalLeft U)) *
        Real.cos α) := by
    have hf : support U (unitNormal α) = P.1 * Real.cos α + P.2 * Real.sin α :=
      (MovingSofaOptimality.dot_vplus_uvec U α).symm
    rw [show terminalFirstRightAbscissa U α = P.1 - Real.cos α from rfl, attachedCorner, hf,
      hU.companion_tail_support hαL haffine ⟨le_rfl, hαL.le⟩]
    linear_combination P.1 * Real.sin_sq_add_cos_sq α
  have hgap : 1 - (P.1 - horizontalLeft U) * Real.sin α +
      (P.2 - capRoof U (horizontalLeft U)) * Real.cos α < 0 := by
    nlinarith [mul_le_mul_of_nonneg_right hdisp hs.le,
      mul_le_mul_of_nonneg_right (show P.2 - capRoof U (horizontalLeft U) ≤ 1 by linarith)
        hc.le]
  linarith [mul_neg_of_pos_of_neg hs hgap]

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

theorem IsJointCapMaximizer.terminal_curvature_atom_le_reserve_div_sin_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (upperCurvature U {α}).toReal ≤ terminalTailReserve U α / Real.sin α := by
  rw [le_div_iff₀ (Real.sin_pos_of_pos_of_lt_pi hU.angle_pos (by linarith [Real.pi_pos])),
    ← hU.isCap.terminalFaceWidth_eq_curvature_atom α]
  exact hU.terminalFaceWidth_le_reserve_of_tail_regime hregime hαL hheight haffine

end AmbidextrousSofa
