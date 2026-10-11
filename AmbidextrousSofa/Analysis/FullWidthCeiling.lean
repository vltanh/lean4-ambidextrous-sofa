module

public import AmbidextrousSofa.Analysis.WideWidthExclusion
public import AmbidextrousSofa.Analysis.FullWidthGap
public import AmbidextrousSofa.Analysis.LowHeightMaximizer

@[expose] public section

/-!
# The actual full maximum has width less than sixteen fifths

The wide exclusion receives both endpoint laws from actual maximality.
At a centered maximizer of height one with a rising affine middle, its
half width is therefore below eight fifths. Together with the short-width
gap this bounds the middle tilt of such a maximizer.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.centered_half_projection_width_lt_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (8 / 5 : ℝ) := by
  by_contra! ha0
  obtain ⟨hright, hAff⟩ := hU.centered_middle hl hr hheight hm haffine
  have hend := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).1
  rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at hend
  have hw : capWidth U = 2 * a := by rw [capWidth, hl, hr]; ring
  have hleft := (sub_sub_cancel 1 (capRoof U (-a / 2))).symm
  have hEP := hU.centered_endpoint_laws hheight hl hr hleft hright hAff
  exact (not_lt_of_ge hU.reference_le) ((hU.isCap.capScore_lt_of_wide_width_and_endpoint_laws ha0
    (by linarith [hU.width_bounds.2])
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)) (by linarith)
    hl hr hleft hright hAff hEP.1 hEP.2).trans forty_one_fiftieths_lt_half_M)

/-- The coupled intermediate width and tilt estimate now has all its
width premises supplied by the actual full maximizer. -/
theorem IsFullCapMaximizer.centered_intermediate_width_tilt
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    let h := 1 - capRoof U (-a / 2)
    h < 17 / 50 ∧ (a - Real.sqrt 2) ^ 2 +
      (4 * a / (4 * a - h)) * (Real.sqrt 2 - 1 + h / 2) ^ 2 ≤ 9 / 25 := by
  obtain ⟨hright, hAff⟩ := hU.centered_middle hl hr hheight hm haffine
  have hleft := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).1
  rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at hleft
  exact hU.isCap.intermediate_width_tilt_bound
    (by linarith [hU.centered_half_projection_width_gt_of_affine_nonneg hl hr hheight hm haffine])
    (hU.centered_half_projection_width_lt_of_affine_nonneg hl hr hheight hm haffine).le
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _))
    (by linarith) hl hr (sub_sub_cancel 1 _).symm hright hAff
    (by linarith [Real.pi_pos]) le_rfl
    (forty_one_fiftieths_lt_half_M.le.trans hU.reference_le)

end AmbidextrousSofa
