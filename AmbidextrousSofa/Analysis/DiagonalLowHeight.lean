module

public import AmbidextrousSofa.Analysis.DiagonalComparisonScore

@[expose] public section

/-!
# Low middle endpoints are excluded by one actual symmetric tent

The low-height exterior reward bounds and scalar bounds apply to the
actual diagonal comparison objective. Every proper score is bounded
above by this objective. Its symmetry lets both physical tilt orientations
be treated without altering the outgoing wall in the actual objective:
when the diagonal comparison score reaches the low-height bound, both
endpoints of an affine middle roof with one endpoint at height one lie
above one half.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- A tent of height `t` and apex `d ∈ [-C, C]` below the diagonal barrier bounds its middle
integral from below. -/
theorem diagonalBarrier_integral_ge_tent {U : Set Plane} {C d t : ℝ} (hd : d ∈ Icc (-C) C)
    (htent : ∀ x, t - |x - d| ≤ diagonalBarrier U x) :
    (max t 0) ^ 2 - (max (t - C - d) 0) ^ 2 / 2 - (max (t - C + d) 0) ^ 2 / 2 ≤
      ∫ x in (-C)..C, diagonalBarrier U x :=
  integral_positive_tent_centered hd t ▸ intervalIntegral.integral_mono_on (hd.1.trans hd.2)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    ((continuous_diagonalBarrier U).intervalIntegrable _ _)
    fun x _ => max_le (htent x) (diagonalBarrier_nonneg _ _)

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
  have hs := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  rcases le_or_gt C (1 / 2) with hsmall | hCmin
  · linarith [lowHeight_small_width_bound hsmall, intervalIntegral.integral_nonneg_of_forall
      (μ := volume) (by linarith : -C ≤ C) (diagonalBarrier_nonneg U)]
  -- This is precisely where the largest possible left tent tail reaches the window edge.
  rcases le_or_gt C (Real.sqrt 2 - 1 / 4) with hmiddle | hlarge
  · -- The actual diagonal tent, with the two diagonal support excesses `u` and `v`.
    obtain ⟨hu0, -, hu1, hv0, hv1⟩ :=
      hU.lowHeight_diagonal_excess_bounds hCmin.le hleft hright hhigh hceiling
    have hrefined := hU.lowHeight_refined_reward_le hCmin.le hleft hright hhigh hceiling
    have hbound := lowHeight_surrogate_bound (u := diagonalRight U - 2 * C) hCmin.le hv0
    generalize hu : diagonalRight U - 2 * C = u at hu0 hu1 hrefined hbound
    generalize hv : diagonalLeft U - 2 * C = v at hv0 hv1 hrefined hbound
    have hniche := diagonalBarrier_integral_ge_tent (U := U) (t := 2 * C + (u + v) / 2 -
      Real.sqrt 2) (d := (u - v) / 2) (C := C) ⟨by linarith, by linarith⟩ fun x =>
        (le_max_left _ 0).trans_eq (by rw [hU.diagonalBarrier_eq_tent, ← hu, ← hv]; ring_nf)
    rw [max_eq_right (a := 2 * C + (u + v) / 2 - Real.sqrt 2 - C - (u - v) / 2) (by linarith),
      show 2 * C + (u + v) / 2 - Real.sqrt 2 - C + (u - v) / 2 = C + u - Real.sqrt 2 by ring]
      at hniche
    unfold lowHeightSurrogate at hbound
    linarith
  -- At larger widths the baseline tent alone suffices.
  have hniche := diagonalBarrier_integral_ge_tent (U := U) (t := 2 * C - Real.sqrt 2) (d := 0)
    (C := C) ⟨by linarith, by linarith⟩ fun x => by
      rw [← min_symmetric_lines]
      exact (le_of_eq (by rw [hleft, hright]; ring_nf)).trans ((min_le_min
        (hU.firstWall_pi_div_four_lower x) (hU.secondWall_pi_div_four_lower x)).trans
          (le_max_left _ _))
  rw [max_eq_left (by linarith : 0 ≤ 2 * C - Real.sqrt 2), sub_zero, add_zero,
    show 2 * C - Real.sqrt 2 - C = C - Real.sqrt 2 by ring] at hniche
  rcases le_total C (Real.sqrt 2) with hclip | hclip
  · rw [max_eq_right (sub_nonpos.mpr hclip)] at hniche
    linarith [lowHeight_large_width_unclipped_bound hlarge.le]
  · rw [max_eq_left (sub_nonneg.mpr hclip)] at hniche
    linarith [lowHeight_large_width_clipped_bound hclip]

theorem IsDownwardCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_left
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 0 < capWidth U)
    (hlow : capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ≤ 1 / 2)
    (hhigh : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    diagonalComparisonScore U < lowHeightBound := by
  obtain ⟨m, c, haffine⟩ := haffine
  have key (x y : ℝ) (h : x + (horizontalLeft U + horizontalRight U) / 2 = y) :
      capRoof (AmbidextrousSofa.centeredCap U) x = capRoof U y :=
    (capRoof_horizontalTranslate U _ x).trans (congrArg _ (by rw [← h]; ring))
  unfold capWidth at hwidth
  rw [← diagonalComparisonScore_centeredCap hU]
  refine hU.centeredCap.diagonalComparisonScore_lt_lowHeightBound_of_affine_middle
    (C := (horizontalRight U - horizontalLeft U) / 4) (by linarith)
    (by rw [horizontalLeft_centeredCap hU, capWidth]; ring)
    (by rw [horizontalRight_centeredCap hU, capWidth]; ring)
    ((key _ _ (by ring)).trans_le hlow) ((key _ _ (by ring)).trans hhigh)
    ⟨m, c + m * ((horizontalLeft U + horizontalRight U) / 2), fun x hx => ?_⟩
  rw [key x _ rfl, haffine _ ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  ring

theorem IsDownwardCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_right
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 0 < capWidth U)
    (hlow : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ≤ 1 / 2)
    (hhigh : capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    diagonalComparisonScore U < lowHeightBound := by
  obtain ⟨m, c, haffine⟩ := haffine
  have hl := horizontalLeft_horizontalMirror hU
  have hr := horizontalRight_horizontalMirror hU
  have key (x y : ℝ) (h : -x = y) : capRoof (AmbidextrousSofa.horizontalMirror U) x =
      capRoof U y := h ▸ capRoof_horizontalMirror U x
  rw [← diagonalComparisonScore_horizontalMirror hU]
  refine hU.horizontalMirror.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_left
    (by rwa [capWidth_horizontalMirror hU]) ((key _ _ (by rw [hl, hr]; ring)).trans_le hlow)
    ((key _ _ (by rw [hl, hr]; ring)).trans hhigh) ⟨-m, c, fun x hx => ?_⟩
  rw [hl, hr, middleHalfInterval, mem_Icc] at hx
  rw [key x _ rfl, haffine _ ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  ring

/-- Both endpoints of an affine middle roof lie above one half when the diagonal comparison
score reaches the low-height bound and the endpoint on the rising side has height one. -/
theorem IsDownwardCap.middle_endpoints_gt_half_of_diagonal {U : Set Plane} (hU : IsDownwardCap U)
    (hwidth : 0 < capWidth U) (hscore : lowHeightBound ≤ diagonalComparisonScore U) {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hR : 0 ≤ m → capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (hL : m ≤ 0 → capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) = 1) :
    1 / 2 < capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ∧
    1 / 2 < capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  rcases le_total 0 m with hm | hm
  · exact ⟨lt_of_not_ge fun h => (hU.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_left
      hwidth h (hR hm) ⟨m, c, haffine⟩).not_ge hscore, one_half_lt_one.trans_eq (hR hm).symm⟩
  · exact ⟨one_half_lt_one.trans_eq (hL hm).symm, lt_of_not_ge fun h =>
      (hU.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_right hwidth h (hL hm)
        ⟨m, c, haffine⟩).not_ge hscore⟩

end AmbidextrousSofa
