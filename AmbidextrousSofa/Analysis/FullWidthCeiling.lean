module

public import AmbidextrousSofa.Analysis.WideWidthExclusion
public import AmbidextrousSofa.Analysis.FullWidthGap
public import AmbidextrousSofa.Analysis.LowHeightMaximizer

@[expose] public section

/-!
# The actual full maximum has width less than sixteen fifths

The wide exclusion receives both endpoint laws from actual maximality.
Height and middle canonicalization preserve projection, and reflection
puts the high endpoint on the right. The conclusion therefore bounds
the width of every original full maximizer.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- `41/50 < M/2`; the same statement and proof as `forty_one_fiftieths_lt_half_M` of
`TerminalScalar`, which this module does not import. -/
private theorem fullWidthCeiling_forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 := by
  have hY : (19 / 64 : ℝ) < Y := cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])
  unfold M beta
  linarith [Y_equation, self_sub_cube_div_three_le_arctan Y_pos.le,
    mul_pos (sub_pos.mpr hY) (show 0 < Y + 19 / 64 by linarith [Y_pos])]

theorem IsFullCapMaximizer.centered_half_projection_width_lt_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (8 / 5 : ℝ) := by
  by_contra! ha0
  have hright : capRoof U (a / 2) = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rwa [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
  have hend := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).1
  rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at hend
  have hw : capWidth U = 2 * a := by rw [capWidth, hl, hr]; ring
  have hleft := (sub_sub_cancel 1 (capRoof U (-a / 2))).symm
  have hAff : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m' * x + c' :=
    ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
  have hEP := hU.centered_endpoint_laws hheight hl hr hleft hright hAff
  have hscore := hU.isCap.capScore_lt_of_wide_width_and_endpoint_laws ha0
    (by linarith [hU.width_bounds.2])
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)) (by linarith)
    hl hr hleft hright hAff hEP.1 hEP.2
  exact (not_lt_of_ge hU.reference_le)
    (hscore.trans fullWidthCeiling_forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.centered_half_projection_width_lt_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (8 / 5 : ℝ) := by
  by_cases hm : 0 ≤ m
  · exact hU.centered_half_projection_width_lt_of_affine_nonneg hl hr hheight hm haffine
  have hVl : horizontalLeft (AmbidextrousSofa.horizontalMirror U) = -a := by
    rw [horizontalLeft_horizontalMirror hU.isCap, hr]
  have hVr : horizontalRight (AmbidextrousSofa.horizontalMirror U) = a := by
    rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg]
  refine hU.horizontalMirror.centered_half_projection_width_lt_of_affine_nonneg hVl hVr
    (by rw [capHeight_horizontalMirror, hheight]) (m := -m) (c := c) (by linarith)
    fun x hx => ?_
  rw [hVl, hVr, middleHalfInterval_centered] at hx
  rw [capRoof_horizontalMirror, haffine (-x) (by
    rw [hl, hr, middleHalfInterval_centered]
    constructor <;> linarith [hx.1, hx.2])]
  ring

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
  have hright : capRoof U (a / 2) = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rwa [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
  have hleft := (hU.middle_endpoints_gt_half_of_affine hheight ⟨m, c, haffine⟩).1
  rw [hl, hr, show -a + (a - -a) / 4 = -a / 2 by ring] at hleft
  exact hU.isCap.intermediate_width_tilt_bound
    (by linarith [hU.centered_half_projection_width_gt_of_affine hl hr hheight haffine])
    (hU.centered_half_projection_width_lt_of_affine hl hr hheight haffine).le
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _))
    (by linarith) hl hr (sub_sub_cancel 1 _).symm hright
    ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
    (by linarith [Real.pi_pos]) le_rfl
    (fullWidthCeiling_forty_one_fiftieths_lt_half_M.le.trans hU.reference_le)

end AmbidextrousSofa
