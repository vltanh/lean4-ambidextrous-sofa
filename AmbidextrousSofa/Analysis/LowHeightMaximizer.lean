import AmbidextrousSofa.Analysis.LowHeightScore
import AmbidextrousSofa.Analysis.TopFacetEndpoints

/-!
# Excluding low middle endpoints at a canonical full maximum

Horizontal translation carries the actual quarter-width geometry to the
centered low-height estimate. Top insertion locates the high endpoint at
height one. Horizontal reflection treats the other orientation. Hence
both endpoints of an affine middle roof of a height-one global maximizer
are strictly above one half.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.capScore_lt_lowHeightBound_of_low_middle_left
    {U : Set Plane} (hU : IsDownwardCap U) (hwidth : 0 < capWidth U)
    (hlow : capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ≤ 1 / 2)
    (hhigh : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    {α : ℝ} (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α < lowHeightBound := by
  let C := capWidth U / 4
  let d := -(horizontalLeft U + horizontalRight U) / 2
  have hC : 0 < C := div_pos hwidth (by norm_num)
  have hleft : horizontalLeft (centeredCap U) = -2 * C := by
    rw [horizontalLeft_centeredCap hU]
    dsimp [C]
    ring
  have hright : horizontalRight (centeredCap U) = 2 * C := by
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
  have hlowV : capRoof (centeredCap U) (-C) ≤ 1 / 2 := by
    change capRoof (horizontalTranslate U d) (-C) ≤ 1 / 2
    rw [capRoof_horizontalTranslate, hleftArg]
    exact hlow
  have hhighV : capRoof (centeredCap U) C = 1 := by
    change capRoof (horizontalTranslate U d) C = 1
    rw [capRoof_horizontalTranslate, hrightArg]
    exact hhigh
  obtain ⟨m, c, haffine⟩ := haffine
  have haffineV : ∃ m' c' : ℝ, ∀ x ∈ Icc (-C) C,
      capRoof (centeredCap U) x = m' * x + c' := by
    refine ⟨m, c - m * d, ?_⟩
    intro x hx
    have hxU : x - d ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
      change horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤ x - d ∧
        x - d ≤ horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
      rw [← hleftArg, ← hrightArg]
      constructor <;> linarith [hx.1, hx.2]
    change capRoof (horizontalTranslate U d) x = _
    rw [capRoof_horizontalTranslate, haffine (x - d) hxU]
    ring
  have h := hU.centeredCap.capScore_lt_lowHeightBound_of_affine_middle
    hC hleft hright hlowV hhighV haffineV hα0 hαL
  rwa [capScore_centeredCap hU] at h

theorem IsFullCapMaximizer.middle_left_gt_half_of_right_eq_one
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hhigh : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) := by
  by_contra h
  have hw : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  have hstrict := hU.isCap.capScore_lt_lowHeightBound_of_low_middle_left hw
    (le_of_not_gt h) hhigh haffine (by linarith [Real.pi_pos]) le_rfl
  exact (not_lt_of_ge hU.reference_le) (hstrict.trans lowHeightBound_lt_half_M)

theorem IsFullCapMaximizer.middle_endpoints_gt_half_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ∧
    1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  have hhigh := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
  exact ⟨hU.middle_left_gt_half_of_right_eq_one hhigh ⟨m, c, haffine⟩, by rw [hhigh]; norm_num⟩

theorem IsFullCapMaximizer.middle_endpoints_gt_half_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) ∧
    1 / 2 < capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) := by
  obtain ⟨m, c, haffine⟩ := haffine
  by_cases hm : 0 ≤ m
  · exact hU.middle_endpoints_gt_half_of_affine_nonneg hheight hm haffine
  · have hV := hU.horizontalMirror
    have hheightV : capHeight (horizontalMirror U) = 1 := by
      rw [capHeight_horizontalMirror, hheight]
    have haffineV : ∀ x ∈ middleHalfInterval
        (horizontalLeft (horizontalMirror U)) (horizontalRight (horizontalMirror U)),
        capRoof (horizontalMirror U) x = (-m) * x + c := by
      intro x hx
      rw [horizontalLeft_horizontalMirror hU.isCap,
        horizontalRight_horizontalMirror hU.isCap] at hx
      have hxU : -x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
        change -horizontalRight U + (-horizontalLeft U - -horizontalRight U) / 4 ≤ x ∧
          x ≤ -horizontalLeft U - (-horizontalLeft U - -horizontalRight U) / 4 at hx
        change horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤ -x ∧
          -x ≤ horizontalRight U - (horizontalRight U - horizontalLeft U) / 4
        constructor <;> linarith [hx.1, hx.2]
      rw [capRoof_horizontalMirror, haffine (-x) hxU]
      ring
    have hb := hV.middle_endpoints_gt_half_of_affine_nonneg hheightV
      (neg_nonneg.mpr (le_of_not_ge hm)) haffineV
    rw [horizontalLeft_horizontalMirror hU.isCap,
      horizontalRight_horizontalMirror hU.isCap, capRoof_horizontalMirror,
      capRoof_horizontalMirror] at hb
    have hfirst : -(-horizontalRight U + (-horizontalLeft U - -horizontalRight U) / 4) =
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 := by ring
    have hsecond : -(-horizontalLeft U - (-horizontalLeft U - -horizontalRight U) / 4) =
        horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 := by ring
    rw [hfirst, hsecond] at hb
    exact ⟨hb.2, hb.1⟩

end AmbidextrousSofa
