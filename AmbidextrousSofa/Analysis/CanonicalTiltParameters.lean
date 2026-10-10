module

public import AmbidextrousSofa.Analysis.FullTriangleWidth
public import AmbidextrousSofa.Analysis.CapNormalization

@[expose] public section

/-!
# Actual parameters of a canonical positive tilt

The width, height loss, and small-slope conditions used by the first-unit
contradiction are consequences of maximality and an actual affine middle.
Horizontal translation preserves that affine middle with its exact new
intercept, so the centered argument applies to a prescribed original cap.
-/

noncomputable section

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
    1 / 2 < C ∧ C < 37 / 50 ∧ 0 < h ∧ h < 17 / 50 ∧ C + m < 1 ∧
      capRoof U (-C) = 1 - h ∧ capRoof U C = 1 := by
  let h := 1 - capRoof U (-C)
  change 1 / 2 < C ∧ C < 37 / 50 ∧ 0 < h ∧ h < 17 / 50 ∧ C + m < 1 ∧
    capRoof U (-C) = 1 - h ∧ capRoof U C = 1
  have hw : capWidth U = 4 * C := by
    unfold capWidth
    rw [hl, hr]
    ring
  have hC0 : 1 / 2 < C := by linarith only [hU.two_lt_width, hw]
  have hC1 : C < 37 / 50 := by
    linarith only [hU.quarter_width_lt_thirty_seven_fiftieths, hw]
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := by
    simpa only [hmid] using haffine
  have hhigh : capRoof U C = 1 := by
    have heq := hU.middle_right_eq_one_of_affine_nonneg hheight hm.le haffine
    rw [hl, hr, show 2 * C - (2 * C - -2 * C) / 4 = C by ring] at heq
    exact heq
  have hhighAff : m * C + c = 1 := by
    rw [← haff C ⟨by linarith only [hC0], le_rfl⟩, hhigh]
  have hrel : h = 2 * C * m := by
    dsimp only [h]
    rw [haff (-C) ⟨le_rfl, by linarith only [hC0]⟩]
    nlinarith only [hhighAff]
  have hh0 : 0 < h := by
    rw [hrel]
    exact mul_pos (by linarith only [hC0]) hm
  have hh1 : h < 17 / 50 := by
    have hbound := (hU.centered_intermediate_width_tilt (a := 2 * C)
      (by rw [hl]; ring) hr hheight hm.le haffine).1
    simpa only [show -(2 * C) / 2 = -C by ring] using hbound
  have hsmall : C + m < 1 := by
    have hbox := mul_nonneg (sub_nonneg.mpr hC0.le) (sub_nonneg.mpr hC1.le)
    by_contra hnot
    have hprod := mul_nonneg (show 0 ≤ 2 * C by linarith only [hC0])
      (sub_nonneg.mpr (le_of_not_gt hnot))
    nlinarith only [hbox, hprod, hrel, hh1, hC1]
  exact ⟨hC0, hC1, hh0, hh1, hsmall, by dsimp only [h]; ring, hhigh⟩

end AmbidextrousSofa
