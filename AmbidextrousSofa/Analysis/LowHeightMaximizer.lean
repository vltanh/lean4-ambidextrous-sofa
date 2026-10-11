module

public import AmbidextrousSofa.Analysis.LowHeightScore
public import AmbidextrousSofa.Analysis.TopFacetEndpoints

@[expose] public section

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
  obtain ⟨m, c, haffine⟩ := haffine
  have hw : capWidth U = horizontalRight U - horizontalLeft U := rfl
  have hroof (x : ℝ) : capRoof (AmbidextrousSofa.centeredCap U) x =
      capRoof U (x + (horizontalLeft U + horizontalRight U) / 2) := by
    rw [AmbidextrousSofa.centeredCap, capRoof_horizontalTranslate]
    ring_nf
  -- Center the cap, so that its projection is `[-2C, 2C]` with `C = capWidth U / 4`.
  rw [← capScore_centeredCap hU]
  refine hU.centeredCap.capScore_lt_lowHeightBound_of_affine_middle (C := capWidth U / 4)
    (by linarith) (by rw [horizontalLeft_centeredCap hU]; ring)
    (by rw [horizontalRight_centeredCap hU]; ring) (by rw [hroof, hw]; convert hlow using 2; ring)
    (by rw [hroof, hw]; convert hhigh using 2; ring)
    ⟨m, c + m * ((horizontalLeft U + horizontalRight U) / 2), fun x hx => ?_⟩ hα0 hαL
  rw [hw] at hx
  rw [hroof, haffine _ ⟨by linarith [hx.1], by linarith [hx.2]⟩]
  ring

theorem IsFullCapMaximizer.middle_left_gt_half_of_right_eq_one
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    (hhigh : capRoof U
      (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    1 / 2 < capRoof U
      (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) :=
  lt_of_not_ge fun h => ((hU.isCap.capScore_lt_lowHeightBound_of_low_middle_left
    (by linarith [hU.width_bounds.1, one_lt_M]) h hhigh haffine (by linarith [Real.pi_pos])
    le_rfl).trans lowHeightBound_lt_half_M).not_ge hU.reference_le

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
  rcases le_total 0 m with hm | hm
  · exact hU.middle_endpoints_gt_half_of_affine_nonneg hheight hm haffine
  -- A negative slope becomes positive after the horizontal reflection.
  have hL := horizontalLeft_horizontalMirror hU.isCap
  have hR := horizontalRight_horizontalMirror hU.isCap
  have hb := hU.horizontalMirror.middle_endpoints_gt_half_of_affine_nonneg
    (by rw [capHeight_horizontalMirror, hheight]) (neg_nonneg.mpr hm) (c := c) fun x hx => by
      rw [hL, hR] at hx
      rw [capRoof_horizontalMirror, haffine (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩]
      ring
  simp only [hL, hR, capRoof_horizontalMirror] at hb
  exact ⟨by convert hb.2 using 2; ring, by convert hb.1 using 2; ring⟩

end AmbidextrousSofa
