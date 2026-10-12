module

public import AmbidextrousSofa.Analysis.TerminalFacetAtom
public import AmbidextrousSofa.Analysis.InitialAngleExclusion
public import AmbidextrousSofa.Analysis.InitialAngleWidth

@[expose] public section

/-!
# Actual terminal corner separation and the terminal face bound

Above the initial angle `arctan (8/3)` the terminal cosine satisfies
`73 cos² α ≤ 9`. The initial-angle and preliminary-width exclusions are
inequalities for the literal partial cap score. The width threshold is the one
that separates the actual terminal corner at the angular endpoint.

Combining that separation with the literal fixed-cap angle extension
bounds the terminal face width by the reserve in the proper tail regime,
which every largest-angle canonical joint maximizer satisfies. The proof
works for all signs of the affine middle roof.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- Above the initial angle the tangent is at least `8/3`, so `73 cos² α ≤ 9`. -/
theorem terminal_cos_sq_le_of_initialAngle {α : ℝ}
    (hα0 : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) : 73 * Real.cos α ^ 2 ≤ 9 := by
  have hαpos : 0 < α := (Real.arctan_pos.2 (by norm_num)).trans_le hα0
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hαpos, hαL⟩
  have htan : 8 / 3 ≤ Real.tan α := by
    simpa using Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo _)
      ⟨by linarith [Real.pi_pos], hαL⟩ hα0
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at htan
  nlinarith [Real.sin_sq_add_cos_sq α]

theorem terminal_sin_cos_bounds_after_initialAngle {α : ℝ}
    (hα0 : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) :
    (14 / 15 : ℝ) < Real.sin α ∧ Real.cos α < (9 / 25 : ℝ) := by
  obtain ⟨hs, hc⟩ :=
    sin_cos_pos_of_mem_quarter ⟨(Real.arctan_pos.2 (by norm_num)).trans_le hα0, hαL⟩
  have := terminal_cos_sq_le_of_initialAngle hα0 hαL
  constructor <;> nlinarith [Real.sin_sq_add_cos_sq α]

/-- The geometric corner width solves the separation equality at the
angular endpoint. Increasing the angle only improves the separation. -/
theorem terminal_corner_width_scale {α : ℝ}
    (hα0 : Real.arctan (8 / 3) ≤ α) (hαL : α < Real.pi / 2) :
    1 + Real.cos α ≤ 3 * initialAngleCornerWidth * Real.sin α := by
  have hαpos : 0 < α := (Real.arctan_pos.2 (by norm_num)).trans_le hα0
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hαpos, hαL⟩
  have hcos := terminal_cos_sq_le_of_initialAngle hα0 hαL
  have htan : 8 / 3 ≤ Real.tan α := by
    simpa using Real.strictMonoOn_tan.monotoneOn (Real.arctan_mem_Ioo _)
      ⟨by linarith [Real.pi_pos], hαL⟩ hα0
  rw [Real.tan_eq_sin_div_cos, le_div_iff₀ hc] at htan
  have hsq : (8 : ℝ) ^ 2 ≤ (Real.sqrt 73 * Real.sin α) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 73)]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hsin : (8 : ℝ) ≤ Real.sqrt 73 * Real.sin α :=
    (sq_le_sq₀ (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) hs.le)).mp hsq
  unfold initialAngleCornerWidth
  nlinarith

/-- The required terminal-corner displacement follows from the actual
score exclusion at its geometric width, with no separate width tolerance. -/
theorem IsJointCapMaximizer.terminal_corner_lt_rightAbscissa_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (attachedCorner U α).1 < terminalFirstRightAbscissa U α := by
  set P := terminalTailPoint U α
  have htail := hU.terminalTailPoint_bounds_of_tail_regime hregime hαL hheight haffine
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hU.angle_pos, hαL⟩
  have hscale := terminal_corner_width_scale
    hU.terminal_angle_gt_arctan_eight_thirds.le hαL
  have hwidth := hU.width_gt_initialAngleCornerWidth hαL
  have he0 : 0 ≤ capRoof U (horizontalLeft U) :=
    capRoof_nonneg hU.isCap.isCompact (fun p hp => (hU.isCap.inStrip hp).1) _
  have hdisp : 3 * initialAngleCornerWidth < P.1 - horizontalLeft U := by
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
    nlinarith [mul_lt_mul_of_pos_right hdisp hs,
      mul_le_mul_of_nonneg_right (show P.2 - capRoof U (horizontalLeft U) ≤ 1 by linarith)
        hc.le]
  linarith [mul_neg_of_pos_of_neg hs hgap]

/-- In the proper tail regime the horizontal width of the terminal face is at most the
reserve. -/
theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_tail_regime
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    terminalFaceWidth U α ≤ terminalTailReserve U α :=
  hU.terminalFaceWidth_le_reserve_of_corner_lt_of_tail_regime hregime hαL hheight haffine
    (hU.terminal_corner_lt_rightAbscissa_of_tail_regime hregime hαL hheight haffine)

end AmbidextrousSofa
