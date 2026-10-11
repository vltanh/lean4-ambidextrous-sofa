module

public import AmbidextrousSofa.Analysis.TerminalWallBound
public import AmbidextrousSofa.Analysis.PartialTopInsertion

@[expose] public section

/-!
# Three actual supports at a proper terminal angle

The two diagonal supports and the first terminal support give simultaneous
upper bounds for the actual cap roof and lower bounds for its actual
partial barrier. The latter retains the whole outgoing first wall.

The terminal position is obtained from the support maximum of the cap.
Its compatibility with the diagonal position is proved at actual support
points. The top-endpoint alternatives likewise come from actual points of
a height-one affine-middle joint maximum.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def terminalSlope (α : ℝ) : ℝ := Real.cos α / Real.sin α

def terminalSupportPosition (U : Set Plane) (α : ℝ) : ℝ :=
  (support U (unitNormal α) - Real.sin α) / Real.cos α

def terminalInset (α : ℝ) : ℝ := (1 - Real.sin α) / Real.cos α

theorem terminalSlope_pos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    0 < terminalSlope α :=
  div_pos (terminal_sin_cos_pos hα0 hαL).2 (terminal_sin_cos_pos hα0 hαL).1

theorem terminalInset_pos {α : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    0 < terminalInset α := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα0 hαL
  exact div_pos (sub_pos.2 (by nlinarith [Real.sin_sq_add_cos_sq α])) hc

theorem terminalSlope_mul_inset {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) :
    terminalSlope α * terminalInset α =
      Real.sqrt (1 + terminalSlope α ^ 2) - 1 := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα0 hαL
  rw [show 1 + terminalSlope α ^ 2 = (1 / Real.sin α) ^ 2 by
      rw [terminalSlope]; field_simp; linear_combination Real.sin_sq_add_cos_sq α,
    Real.sqrt_sq (by positivity), terminalSlope, terminalInset]
  field_simp

theorem IsDownwardCap.capRoof_le_terminal_support {U : Set Plane}
    (hU : IsDownwardCap U) {α x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hx : x ∈ horizontalProjection U) :
    capRoof U x ≤ 1 - terminalSlope α * (x - terminalSupportPosition U α) := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα0 hαL
  convert hU.capRoof_le_first_support_line hs hx using 1
  rw [terminalSlope, terminalSupportPosition]
  field_simp
  ring

/-- The visited diagonal corner and the entire terminal first wall are
both actual lower bounds for the partial barrier. -/
theorem IsDownwardCap.three_supports_le_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα0 : Real.pi / 4 ≤ α)
    (hαL : α < Real.pi / 2) (x : ℝ) :
    max (max 0 (min ((diagonalRight U - 1) - (Real.sqrt 2 - 1) - x)
      ((diagonalLeft U - 1) - (Real.sqrt 2 - 1) + x)))
      (terminalSlope α * (terminalSupportPosition U α - terminalInset α - x)) ≤
        partialBarrier U α x := by
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos (by linarith [Real.pi_pos]) hαL
  refine max_le (max_le (partialBarrier_nonneg U α x) ?_)
    (le_trans (le_of_eq ?_) (le_max_right _ _))
  · simpa only [cornerWall, firstWall_pi_div_four_eq_diagonal hU,
      secondWall_pi_div_four_eq_diagonal hU, sub_sub_sub_cancel_right] using
      cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL.le x
  · rw [firstWall, terminalSlope, terminalSupportPosition, terminalInset]
    field_simp
    ring

theorem IsDownwardCap.three_support_compatibility_centered {U : Set Plane}
    (hU : IsDownwardCap U) {C α : ℝ}
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2) :
    terminalSupportPosition U α ≤ diagonalRight U - 1 ∧
    diagonalRight U - 1 ≤ 2 * (1 - terminalSlope α) * C +
      terminalSlope α * terminalSupportPosition U α ∧
    diagonalRight U - 1 ≤ 2 * C ∧ diagonalLeft U - 1 ≤ 2 * C ∧
    terminalSupportPosition U α ≤ 2 * C := by
  have hα : 0 < α := by linarith [Real.pi_pos]
  obtain ⟨hs, hc⟩ := terminal_sin_cos_pos hα hαL
  have hsc : Real.cos α ≤ Real.sin α := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hαL.le (by linarith)
  have hR (p : Plane) (hp : p ∈ U) : p.1 ≤ 2 * C :=
    hright ▸ le_csSup (isCompact_horizontalProjection hU.isCompact).bddAbove ⟨p, hp, rfl⟩
  refine ⟨?_, ?_, by linarith [hU.diagonalRight_le], by linarith [hU.diagonalLeft_le], ?_⟩
  · obtain ⟨p, hp, hpmax⟩ := exists_coordDot_eq_support hU.isCompact hU.nonempty (unitNormal α)
    rw [terminalSupportPosition, ← hpmax, div_le_iff₀ hc]
    simp only [coordDot, unitNormal]
    linarith [mul_le_mul_of_nonneg_right (hU.diagonalRight_ge hp) hc.le,
      mul_nonneg (sub_nonneg.2 (hU.inStrip hp).2) (sub_nonneg.2 hsc)]
  · obtain ⟨p, hp, hpmax : p.1 * 1 + p.2 * 1 = diagonalRight U⟩ :=
      exists_coordDot_eq_support hU.isCompact hU.nonempty (1, 1)
    have hk : terminalSlope α ≤ 1 := div_le_one_of_le₀ hsc hs.le
    linarith [hU.capRoof_le_terminal_support hα hαL ⟨p, hp, rfl⟩, le_capRoof hU.isCompact hp,
      mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 (hR p hp))]
  · rw [terminalSupportPosition, div_le_iff₀ hc, sub_le_iff_le_add]
    refine support_le_of_forall hU.nonempty fun p hp => ?_
    simp only [coordDot, unitNormal]
    linarith [mul_le_mul_of_nonneg_right (hR p hp) hc.le,
      mul_le_mul_of_nonneg_right (hU.inStrip hp).2 hs.le]

theorem IsDownwardCap.three_support_lower_of_top {U : Set Plane}
    (hU : IsDownwardCap U) {α t : ℝ} (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (ht : (t, 1) ∈ U) :
    -t ≤ diagonalLeft U - 1 ∧ t ≤ diagonalRight U - 1 ∧
      t ≤ terminalSupportPosition U α := by
  refine ⟨by linarith [hU.diagonalLeft_ge ht], by linarith [hU.diagonalRight_ge ht], ?_⟩
  have := coordDot_le_support hU.isCompact ht (unitNormal α)
  rw [terminalSupportPosition, le_div_iff₀ (terminal_sin_cos_pos hα0 hαL).2]
  simp only [coordDot, unitNormal] at this ⊢
  linarith

/-- The endpoint alternatives are actual points of the cap. Both slope
signs use their own top insertion, without reflecting the partial score. -/
theorem IsJointCapMaximizer.top_endpoint_of_affine {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hheight : capHeight U = 1) {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    (horizontalLeft U + capWidth U / 4, 1) ∈ U ∨
      (horizontalRight U - capWidth U / 4, 1) ∈ U := by
  obtain ⟨ha, hb, -⟩ := hU.isCap.middleChord_endpoints (by linarith [hU.width_bounds.1, one_lt_M])
  rcases le_or_gt 0 m with hm | hm
  · exact .inr (hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine ▸
      capRoof_mem hU.isCap.isCompact hb)
  · exact .inl (hU.middle_left_eq_one_of_affine_nonpos hheight hm.le haffine ▸
      capRoof_mem hU.isCap.isCompact ha)

/-- Integrating the genuine three-support bounds gives the finite scalar
relaxation. The left reward uses only a change of integration variable;
the actual cap and its partial barrier are never reflected. -/
theorem IsDownwardCap.capScore_le_three_support_integrals_centered
    {U : Set Plane} (hU : IsDownwardCap U) {C α : ℝ} (hC : 0 ≤ C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α < Real.pi / 2) :
    capScore U α ≤ 2 * C -
      (∫ x in C..(2 * C), max (x - (diagonalLeft U - 1)) 0) -
      (∫ x in C..(2 * C), max (max 0 (x - (diagonalRight U - 1)))
        (terminalSlope α * (x - terminalSupportPosition U α))) -
      ∫ x in (-C)..C,
        max (max 0 (min ((diagonalRight U - 1) - (Real.sqrt 2 - 1) - x)
          ((diagonalLeft U - 1) - (Real.sqrt 2 - 1) + x)))
          (terminalSlope α * (terminalSupportPosition U α - terminalInset α - x)) := by
  have hα : 0 < α := by linarith [Real.pi_pos]
  have hproj : horizontalProjection U = Icc (-2 * C) (2 * C) := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hleft, hright]
  have hint {a b : ℝ} {g : ℝ → ℝ} (hg : Continuous g) (ha : -2 * C ≤ a) (hab : a ≤ b)
      (hb : b ≤ 2 * C) (h : ∀ x ∈ horizontalProjection U, g x ≤ 1 - capRoof U x) :
      ∫ x in a..b, capRoof U x ≤ (b - a) - ∫ x in a..b, g x := by
    have := intervalIntegral.integral_mono_on (g := fun x => 1 - g x) hab
      (hU.intervalIntegrable_capRoof a b) ((continuous_const.sub hg).intervalIntegrable a b)
      fun x hx => le_sub_comm.1 (h x (hproj ▸ ⟨ha.trans hx.1, hx.2.trans hb⟩))
    rwa [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (hg.intervalIntegrable a b), intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
  have hL := hint (a := -2 * C) (b := -C) (g := fun x => max (-x - (diagonalLeft U - 1)) 0)
    (by fun_prop) le_rfl (by linarith) (by linarith) fun x hx => max_le
      (by linarith [hU.capRoof_le_diagonalLeft hx])
      (by linarith [capRoof_le_one hU.isCompact hU.inStrip x])
  have hR := hint (a := C) (b := 2 * C) (g := fun x => max (max 0 (x - (diagonalRight U - 1)))
      (terminalSlope α * (x - terminalSupportPosition U α))) (by fun_prop) (by linarith)
    (by linarith) le_rfl fun x hx => max_le (max_le
      (by linarith [capRoof_le_one hU.isCompact hU.inStrip x])
      (by linarith [hU.capRoof_le_diagonalRight hx]))
      (by linarith [hU.capRoof_le_terminal_support hα hαL hx])
  have hN := intervalIntegral.integral_mono_on (by linarith : -C ≤ C)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (hU.intervalIntegrable_partialBarrier hα hαL.le _ _)
    fun x _ => hU.three_supports_le_partialBarrier hα0 hαL x
  have hrefl := intervalIntegral.integral_comp_neg (a := -2 * C) (b := -C)
    fun x => max (x - (diagonalLeft U - 1)) 0
  rw [neg_neg, show -(-2 * C) = 2 * C by ring] at hrefl
  linarith [capScore_centered_quarters hU hleft hright α]

end AmbidextrousSofa
