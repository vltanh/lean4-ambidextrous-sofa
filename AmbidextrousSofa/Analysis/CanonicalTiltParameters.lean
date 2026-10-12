module

public import AmbidextrousSofa.Analysis.FullTriangleWidth
public import AmbidextrousSofa.Analysis.CapNormalization
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds

@[expose] public section

/-!
# Actual parameters of a canonical positive tilt

The width, height loss, and small-slope conditions used by the first-unit
contradiction are consequences of maximality and an actual affine middle.
Horizontal translation preserves that affine middle with its exact new
intercept, so the centered argument applies to a prescribed original cap.
-/

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.affine_middle_horizontalTranslate
    {U : Set Plane} (hU : IsDownwardCap U) {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) (a : ℝ) :
    ∀ x ∈ middleHalfInterval (horizontalLeft (AmbidextrousSofa.horizontalTranslate U a))
      (horizontalRight (AmbidextrousSofa.horizontalTranslate U a)),
      capRoof (AmbidextrousSofa.horizontalTranslate U a) x = m * x + (c - m * a) := by
  intro x hx
  rw [horizontalLeft_horizontalTranslate hU, horizontalRight_horizontalTranslate hU,
    middleHalfInterval_add] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [capRoof_horizontalTranslate, add_sub_cancel_right, haffine y hy]
  ring

/-- All numerical hypotheses for the actual tilted-case contradiction
are derived from this same canonical cap. -/
theorem IsFullCapMaximizer.centered_positive_tilt_parameters
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hm : 0 < m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    let h := 1 - capRoof U (-C)
    1 / 2 < C ∧ C < 37 / 50 ∧ 0 < h ∧ h < 1 / 3 ∧ C + m < 1 ∧
      capRoof U (-C) = 1 - h ∧ capRoof U C = 1 := by
  dsimp only
  have hw : capWidth U = 4 * C := by rw [capWidth, hl, hr]; ring
  have hC0 : 1 / 2 < C := by linarith only [hU.two_lt_width, hw]
  have hC1 : C < 37 / 50 := by linarith only [hU.quarter_width_lt_thirty_seven_fiftieths, hw]
  obtain ⟨-, hplus, hmid⟩ := centered_quarter_points hl hr
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := hmid ▸ haffine
  have hhigh : capRoof U C = 1 :=
    hplus ▸ hU.middle_right_eq_one_of_affine_nonneg hheight hm.le haffine
  have hrel : 1 - capRoof U (-C) = 2 * C * m := by
    linarith only [haff (-C) ⟨le_rfl, by linarith only [hC0]⟩,
      haff C ⟨by linarith only [hC0], le_rfl⟩, hhigh]
  have hh1 : 1 - capRoof U (-C) < 1 / 3 := by
    simpa only [show -(2 * C) / 2 = -C by ring] using (hU.centered_intermediate_width_tilt
      (a := 2 * C) (by rw [hl]; ring) hr hheight hm.le haffine).1
  refine ⟨hC0, hC1, hrel ▸ mul_pos (by linarith only [hC0]) hm, hh1,
    not_le.1 fun hnot => ?_, by ring, hhigh⟩
  linarith only [mul_nonneg (sub_nonneg.mpr hC0.le) (sub_nonneg.mpr hC1.le),
    mul_nonneg (by linarith only [hC0] : (0 : ℝ) ≤ 2 * C) (sub_nonneg.mpr hnot), hrel, hh1, hC1]

end AmbidextrousSofa
