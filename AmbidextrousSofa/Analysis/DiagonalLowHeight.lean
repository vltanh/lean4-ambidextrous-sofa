module

public import AmbidextrousSofa.Analysis.DiagonalComparisonScore

@[expose] public section

/-!
# Low middle endpoints are excluded by one actual symmetric tent

The low-height exterior reward bounds and scalar bounds apply to the
actual diagonal comparison objective. Every proper score is bounded
above by this objective. Its symmetry lets
both physical tilt orientations be treated without altering the outgoing
wall in the actual objective.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.lowHeight_diagonal_integral_lower {U : Set Plane}
    (hU : IsDownwardCap U) {C u v : ℝ} (hC : 1 / 2 ≤ C) (hCmax : C ≤ 23 / 20)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 4)
    (hR : diagonalRight U = 2 * C + u) (hL : diagonalLeft U = 2 * C + v) :
    (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 -
      (max (C + u - Real.sqrt 2) 0) ^ 2 / 2 ≤ ∫ x in (-C)..C, diagonalBarrier U x := by
  have hc : Continuous fun x : ℝ =>
      max (2 * C + (u + v) / 2 - Real.sqrt 2 - |x - (u - v) / 2|) 0 := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -C ≤ C)
    (hc.intervalIntegrable _ _) ((continuous_diagonalBarrier U).intervalIntegrable _ _)
    fun x _ => le_of_eq (by rw [hU.diagonalBarrier_eq_tent, hR, hL]; ring_nf)
  rw [integral_positive_tent_centered (⟨by linarith, by linarith⟩ : (u - v) / 2 ∈ Icc (-C) C),
    max_eq_right (by linarith [lowHeight_sqrt_bounds.1] :
      2 * C + (u + v) / 2 - Real.sqrt 2 - C - (u - v) / 2 ≤ 0),
    show 2 * C + (u + v) / 2 - Real.sqrt 2 - C + (u - v) / 2 = C + u - Real.sqrt 2 by ring]
    at hmono
  linarith

theorem IsDownwardCap.baseline_positive_tent_integral_le_diagonal {U : Set Plane}
    (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) :
    (max (2 * C - Real.sqrt 2) 0) ^ 2 - (max (C - Real.sqrt 2) 0) ^ 2 ≤
      ∫ x in (-C)..C, diagonalBarrier U x := by
  have hc : Continuous fun x : ℝ => max (2 * C - Real.sqrt 2 - |x - 0|) 0 := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -C ≤ C)
    (hc.intervalIntegrable _ _) ((continuous_diagonalBarrier U).intervalIntegrable _ _)
    fun x _ => max_le_max (by
      rw [← min_symmetric_lines]
      exact (le_of_eq (by rw [hleft, hright]; ring_nf)).trans
        (min_le_min (hU.firstWall_pi_div_four_lower x) (hU.secondWall_pi_div_four_lower x)))
      le_rfl
  rw [integral_positive_tent_centered (⟨by linarith, by linarith⟩ : (0 : ℝ) ∈ Icc (-C) C),
    show 2 * C - Real.sqrt 2 - C - 0 = C - Real.sqrt 2 by ring,
    show 2 * C - Real.sqrt 2 - C + 0 = C - Real.sqrt 2 by ring] at hmono
  linarith

/-- The strict exclusion already holds when only the actual diagonal
two-wall tent is charged. -/
theorem IsDownwardCap.diagonalComparisonScore_lt_lowHeightBound_of_affine_middle
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hlow : capRoof U (-C) ≤ 1 / 2) (hhigh : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c) :
    diagonalComparisonScore U < lowHeightBound := by
  have hceiling := hU.capRoof_le_lowCeiling_of_affine_middle hC hleft hright hlow hhigh haffine
  have hscore := diagonalComparisonScore_centered_quarters hleft hright
  have hreward := hU.lowHeight_reward_le hC hceiling
  rcases le_or_gt C (1 / 2) with hsmall | hCmin
  · linarith [lowHeight_small_width_bound hsmall, intervalIntegral.integral_nonneg_of_forall
      (μ := volume) (by linarith : -C ≤ C) (diagonalBarrier_nonneg U)]
  rcases le_or_gt C (23 / 20) with hmiddle | hlarge
  · obtain ⟨hu0, _, hu1, hv0, hv1⟩ := hU.lowHeight_diagonal_excess_bounds hCmin.le hleft hright
      hhigh hceiling
    have hrefined := hU.lowHeight_refined_reward_le hCmin.le hleft hright hhigh hceiling
    have hniche := hU.lowHeight_diagonal_integral_lower hCmin.le hmiddle hu0 hu1 hv0 hv1
      (by ring : diagonalRight U = 2 * C + (diagonalRight U - 2 * C))
      (by ring : diagonalLeft U = 2 * C + (diagonalLeft U - 2 * C))
    refine lt_of_le_of_lt ?_ (lowHeight_surrogate_bound hCmin.le hu1 hv0)
    unfold lowHeightSurrogate
    linarith
  have hniche := hU.baseline_positive_tent_integral_le_diagonal hC hleft hright
  rw [max_eq_left (by linarith [lowHeight_sqrt_bounds.2.2] : 0 ≤ 2 * C - Real.sqrt 2)] at hniche
  rcases le_total C (Real.sqrt 2) with hclip | hclip
  · rw [max_eq_right (sub_nonpos.mpr hclip)] at hniche
    linarith [lowHeight_large_width_unclipped_bound hlarge.le]
  · rw [max_eq_left (sub_nonneg.mpr hclip)] at hniche
    linarith [lowHeight_large_width_clipped_bound hclip]

end AmbidextrousSofa
