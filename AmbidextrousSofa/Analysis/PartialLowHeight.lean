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
  let C := capWidth U / 4
  let d := -(horizontalLeft U + horizontalRight U) / 2
  have hC : 0 < C := div_pos hwidth (by norm_num)
  have hleft : horizontalLeft (AmbidextrousSofa.centeredCap U) = -2 * C := by
    rw [horizontalLeft_centeredCap hU]
    dsimp [C]
    ring
  have hright : horizontalRight (AmbidextrousSofa.centeredCap U) = 2 * C := by
    rw [horizontalRight_centeredCap hU]
    dsimp [C]
    ring
  have hleftArg : -C - d = horizontalLeft U +
      (horizontalRight U - horizontalLeft U) / 4 := by
    dsimp [C, d]
    unfold capWidth
    ring
  have hrightArg : C - d = horizontalRight U -
      (horizontalRight U - horizontalLeft U) / 4 := by
    dsimp [C, d]
    unfold capWidth
    ring
  have hlowV : capRoof (AmbidextrousSofa.centeredCap U) (-C) ≤ 1 / 2 := by
    change capRoof (AmbidextrousSofa.horizontalTranslate U d) (-C) ≤ 1 / 2
    rw [capRoof_horizontalTranslate, hleftArg]
    exact hlow
  have hhighV : capRoof (AmbidextrousSofa.centeredCap U) C = 1 := by
    change capRoof (AmbidextrousSofa.horizontalTranslate U d) C = 1
    rw [capRoof_horizontalTranslate, hrightArg]
    exact hhigh
  obtain ⟨m, c, haffine⟩ := haffine
  have haffineV : ∃ m' c' : ℝ, ∀ x ∈ Icc (-C) C,
      capRoof (AmbidextrousSofa.centeredCap U) x = m' * x + c' := by
    refine ⟨m, c - m * d, ?_⟩
    intro x hx
    have hxU : x - d ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
      change horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤ x - d ∧
        x - d ≤ horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
      rw [← hleftArg, ← hrightArg]
      constructor <;> linarith [hx.1, hx.2]
    change capRoof (AmbidextrousSofa.horizontalTranslate U d) x = _
    rw [capRoof_horizontalTranslate, haffine (x - d) hxU]
    ring
  have h := hU.centeredCap.diagonalComparisonScore_lt_lowHeightBound_of_affine_middle
    hC hleft hright hlowV hhighV haffineV
  rwa [diagonalComparisonScore_centeredCap hU] at h

theorem IsDownwardCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_right
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 0 < capWidth U)
    (hlow : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ≤ 1 / 2)
    (hhigh : capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    diagonalComparisonScore U < lowHeightBound := by
  have hwidthV : 0 < capWidth (AmbidextrousSofa.horizontalMirror U) := by
    rwa [capWidth_horizontalMirror hU]
  have hlowV : capRoof (AmbidextrousSofa.horizontalMirror U)
      (horizontalLeft (AmbidextrousSofa.horizontalMirror U) +
        (horizontalRight (AmbidextrousSofa.horizontalMirror U) - horizontalLeft (AmbidextrousSofa.horizontalMirror U)) / 4) ≤ 1 / 2 := by
    rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU,
      capRoof_horizontalMirror,
      show -(-horizontalRight U + (-horizontalLeft U - -horizontalRight U) / 4) =
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 by ring]
    exact hlow
  have hhighV : capRoof (AmbidextrousSofa.horizontalMirror U)
      (horizontalRight (AmbidextrousSofa.horizontalMirror U) -
        (horizontalRight (AmbidextrousSofa.horizontalMirror U) - horizontalLeft (AmbidextrousSofa.horizontalMirror U)) / 4) = 1 := by
    rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU,
      capRoof_horizontalMirror,
      show -(-horizontalLeft U - (-horizontalLeft U - -horizontalRight U) / 4) =
        horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 by ring]
    exact hhigh
  obtain ⟨m, c, haffine⟩ := haffine
  have haffineV : ∃ m' c' : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft (AmbidextrousSofa.horizontalMirror U)) (horizontalRight (AmbidextrousSofa.horizontalMirror U)),
      capRoof (AmbidextrousSofa.horizontalMirror U) x = m' * x + c' := by
    refine ⟨-m, c, ?_⟩
    intro x hx
    rw [horizontalLeft_horizontalMirror hU, horizontalRight_horizontalMirror hU] at hx
    have hxU : -x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
      change -horizontalRight U + (-horizontalLeft U - -horizontalRight U) / 4 ≤ x ∧
        x ≤ -horizontalLeft U - (-horizontalLeft U - -horizontalRight U) / 4 at hx
      change horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤ -x ∧
        -x ≤ horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
      constructor <;> linarith [hx.1, hx.2]
    rw [capRoof_horizontalMirror, haffine (-x) hxU]
    ring
  have h := hU.horizontalMirror.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_left
    hwidthV hlowV hhighV haffineV
  rwa [diagonalComparisonScore_horizontalMirror hU] at h

theorem IsJointCapMaximizer.middle_left_gt_half_of_right_eq_one
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hhigh : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) := by
  by_contra h
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hstrict := hU.isCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_left
    hw (le_of_not_gt h) hhigh haffine
  have hscore := hU.isCap.capScore_le_diagonalComparisonScore hU.angle_mem.1 hU.angle_mem.2
  exact (not_lt_of_ge hU.reference_le)
    ((hscore.trans_lt hstrict).trans lowHeightBound_lt_half_M)

theorem IsJointCapMaximizer.middle_right_gt_half_of_left_eq_one
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hhigh : capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  by_contra h
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hstrict := hU.isCap.diagonalComparisonScore_lt_lowHeightBound_of_low_middle_right
    hw (le_of_not_gt h) hhigh haffine
  have hscore := hU.isCap.capScore_le_diagonalComparisonScore hU.angle_mem.1 hU.angle_mem.2
  exact (not_lt_of_ge hU.reference_le)
    ((hscore.trans_lt hstrict).trans lowHeightBound_lt_half_M)

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
  obtain ⟨m, c, haffine⟩ := haffine
  by_cases hm : 0 ≤ m
  · have hhigh := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    exact ⟨hU.middle_left_gt_half_of_right_eq_one hhigh ⟨m, c, haffine⟩,
      by rw [hhigh]; norm_num⟩
  · have hhigh := hU.middle_left_eq_one_of_affine_nonpos hheight (le_of_not_ge hm) haffine
    exact ⟨by rw [hhigh]; norm_num,
      hU.middle_right_gt_half_of_left_eq_one hhigh ⟨m, c, haffine⟩⟩

end AmbidextrousSofa
