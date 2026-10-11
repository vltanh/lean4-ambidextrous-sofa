module

public import AmbidextrousSofa.Analysis.DiagonalLowHeight
public import AmbidextrousSofa.Analysis.PartialTopInsertion

@[expose] public section

/-!
# Actual proper maxima have middle endpoints above one half

The diagonal comparison score is invariant under horizontal reflection.
It bounds the original proper score at every visited range reaching
pi/4. The low-height exclusion therefore applies to both tilt signs,
while top insertion supplies the height-one endpoint in the actual
orientation.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

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

/-- The low-height bound cannot exceed the diagonal comparison score of a joint maximizer. -/
private theorem IsJointCapMaximizer.lowHeightBound_le_diagonalComparisonScore {U : Set Plane}
    {α : ℝ} (hU : IsJointCapMaximizer U α) : lowHeightBound ≤ diagonalComparisonScore U := by
  linarith [hU.reference_le, lowHeightBound_lt_half_M,
    hU.isCap.capScore_le_diagonalComparisonScore hU.angle_mem.1 hU.angle_mem.2]

theorem IsJointCapMaximizer.middle_left_gt_half_of_right_eq_one
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hhigh : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) :=
  lt_of_not_ge fun h => hU.lowHeightBound_le_diagonalComparisonScore.not_gt
    (hU.isCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_left
      (by linarith [hU.width_bounds.1, one_lt_M]) h hhigh haffine)

/-- The two orientations compare only the actual diagonal tent. The
proper barrier and its outgoing wall stay in their original orientation. -/
theorem IsJointCapMaximizer.middle_endpoints_gt_half_of_affine
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ∧
    1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  obtain ⟨m, c, hmc⟩ := haffine
  rcases le_total 0 m with hm | hm
  · have hhigh := hU.middle_right_eq_one_of_affine_nonneg hheight hm hmc
    exact ⟨hU.middle_left_gt_half_of_right_eq_one hhigh ⟨m, c, hmc⟩,
      one_half_lt_one.trans_eq hhigh.symm⟩
  · have hhigh := hU.middle_left_eq_one_of_affine_nonpos hheight hm hmc
    refine ⟨one_half_lt_one.trans_eq hhigh.symm, lt_of_not_ge fun h =>
      hU.lowHeightBound_le_diagonalComparisonScore.not_gt ?_⟩
    exact hU.isCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_right
      (by linarith [hU.width_bounds.1, one_lt_M]) h hhigh ⟨m, c, hmc⟩

end AmbidextrousSofa
