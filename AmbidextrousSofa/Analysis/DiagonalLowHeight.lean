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
  let h : ℝ := 2 * C + (u + v) / 2 - Real.sqrt 2
  let d : ℝ := (u - v) / 2
  have hd : d ∈ Icc (-C) C := by dsimp [d]; constructor <;> linarith
  have hheight : (diagonalRight U + diagonalLeft U) / 2 - Real.sqrt 2 = h := by
    rw [hR, hL]
    dsimp [h]
    ring
  have hcenter : (diagonalRight U - diagonalLeft U) / 2 = d := by
    rw [hR, hL]
    dsimp [d]
    ring
  have hpoint : ∀ x, max (h - |x - d|) 0 ≤ diagonalBarrier U x := by
    intro x
    rw [hU.diagonalBarrier_eq_tent, hheight, hcenter]
  have hc : Continuous (fun x : ℝ => max (h - |x - d|) 0) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -C ≤ C)
    (hc.intervalIntegrable (-C) C)
    ((continuous_diagonalBarrier U).intervalIntegrable (-C) C)
    (fun x _ => hpoint x)
  rw [integral_positive_tent_centered hd] at hmono
  have htail : h - C - d ≤ 0 := by
    dsimp [h, d]
    linarith [lowHeight_sqrt_bounds.1]
  rw [max_eq_right htail, show h - C + d = C + u - Real.sqrt 2 by dsimp [h, d]; ring] at hmono
  simpa only [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, sub_zero] using hmono

theorem IsDownwardCap.baseline_positive_tent_integral_le_diagonal {U : Set Plane}
    (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C) :
    (max (2 * C - Real.sqrt 2) 0) ^ 2 - (max (C - Real.sqrt 2) 0) ^ 2 ≤
      ∫ x in (-C)..C, diagonalBarrier U x := by
  have hpoint : ∀ x, max (2 * C - Real.sqrt 2 - |x|) 0 ≤ diagonalBarrier U x := by
    intro x
    have h : min (horizontalRight U - Real.sqrt 2 - x)
        (x - horizontalLeft U - Real.sqrt 2) ≤ cornerWall U (Real.pi / 4) x :=
      min_le_min (hU.firstWall_pi_div_four_lower x) (hU.secondWall_pi_div_four_lower x)
    rw [hleft, hright] at h
    have heq : min (2 * C - Real.sqrt 2 - x) (x - -2 * C - Real.sqrt 2) =
        2 * C - Real.sqrt 2 - |x| := by
      have ht := min_symmetric_lines (2 * C - Real.sqrt 2) 0 x
      simpa only [add_zero, sub_zero, show x - -2 * C - Real.sqrt 2 =
        (2 * C - Real.sqrt 2) + x by ring] using ht
    rw [heq] at h
    exact max_le_max h le_rfl
  have hc : Continuous (fun x : ℝ => max (2 * C - Real.sqrt 2 - |x - 0|) 0) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by linarith : -C ≤ C)
    (hc.intervalIntegrable (-C) C)
    ((continuous_diagonalBarrier U).intervalIntegrable (-C) C)
    (fun x _ => by simpa only [sub_zero] using hpoint x)
  rw [integral_positive_tent_centered (show (0 : ℝ) ∈ Icc (-C) C by constructor <;> linarith)] at hmono
  simp only [sub_zero, add_zero, show 2 * C - Real.sqrt 2 - C = C - Real.sqrt 2 by ring] at hmono
  linarith

/-- The strict exclusion already holds when only the actual diagonal
two-wall tent is charged. -/
theorem IsDownwardCap.diagonalComparisonScore_lt_lowHeightBound_of_ceiling
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hhigh : capRoof U C = 1)
    (hceiling : ∀ x ∈ Icc (-2 * C) C, capRoof U x ≤ lowCeiling C x) :
    diagonalComparisonScore U < lowHeightBound := by
  have hscore := diagonalComparisonScore_centered_quarters hleft hright
  have hreward := hU.lowHeight_reward_le hC hceiling
  by_cases hsmall : C ≤ 1 / 2
  · have hn : 0 ≤ ∫ x in (-C)..C, diagonalBarrier U x :=
      intervalIntegral.integral_nonneg_of_forall (by linarith) (diagonalBarrier_nonneg U)
    linarith [lowHeight_small_width_bound hsmall]
  have hCmin : 1 / 2 ≤ C := (le_of_not_ge hsmall)
  by_cases hmiddle : C ≤ 23 / 20
  · let u : ℝ := diagonalRight U - 2 * C
    let v : ℝ := diagonalLeft U - 2 * C
    obtain ⟨hu0, _, hu1, hv0, hv1⟩ := hU.lowHeight_diagonal_excess_bounds
      hCmin hleft hright hhigh hceiling
    have hrefined := hU.lowHeight_refined_reward_le hCmin hleft hright hhigh hceiling
    have hniche := hU.lowHeight_diagonal_integral_lower hCmin hmiddle hu0 hu1 hv0 hv1
      (by dsimp [u]; ring : diagonalRight U = 2 * C + u)
      (by dsimp [v]; ring : diagonalLeft U = 2 * C + v)
    have hbound : diagonalComparisonScore U ≤ lowHeightSurrogate C u v := by
      unfold lowHeightSurrogate
      change _ ≤ 11 * C / 8 - (1 - u) ^ 2 / 2 - (1 / 4 - v) ^ 2 / 2 -
        (max (2 * C + (u + v) / 2 - Real.sqrt 2) 0) ^ 2 +
          (max (C + u - Real.sqrt 2) 0) ^ 2 / 2
      change _ ≤ 11 * C / 8 - (1 - u) ^ 2 / 2 - (1 / 4 - v) ^ 2 / 2 at hrefined
      linarith
    exact hbound.trans_lt (lowHeight_surrogate_bound hCmin hu1 hv0)
  · have hlarge : 23 / 20 ≤ C := (le_of_not_ge hmiddle)
    have hniche := hU.baseline_positive_tent_integral_le_diagonal hC hleft hright
    have hheight : 0 ≤ 2 * C - Real.sqrt 2 := by linarith [lowHeight_sqrt_bounds.2.2]
    rw [max_eq_left hheight] at hniche
    by_cases hclip : C ≤ Real.sqrt 2
    · rw [max_eq_right (sub_nonpos.mpr hclip)] at hniche
      have hbound := lowHeight_large_width_unclipped_bound hlarge
      nlinarith
    · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hclip))] at hniche
      have hbound := lowHeight_large_width_clipped_bound (le_of_not_ge hclip)
      nlinarith

theorem IsDownwardCap.diagonalComparisonScore_lt_lowHeightBound_of_affine_middle
    {U : Set Plane} (hU : IsDownwardCap U) {C : ℝ} (hC : 0 < C)
    (hleft : horizontalLeft U = -2 * C) (hright : horizontalRight U = 2 * C)
    (hlow : capRoof U (-C) ≤ 1 / 2) (hhigh : capRoof U C = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c) :
    diagonalComparisonScore U < lowHeightBound :=
  hU.diagonalComparisonScore_lt_lowHeightBound_of_ceiling hC hleft hright hhigh
    (hU.capRoof_le_lowCeiling_of_affine_middle hC hleft hright hlow hhigh haffine)


end AmbidextrousSofa
