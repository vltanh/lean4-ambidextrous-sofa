module

public import AmbidextrousSofa.Analysis.ShortWidthExclusion
public import AmbidextrousSofa.Analysis.TopFacetEndpoints

@[expose] public section

/-!
# Every actual full maximizer has width strictly greater than two

The stronger rational gap follows by centering, actual height and middle
canonicalization, and reflection if its middle slope is negative. Each
operation preserves the literal projection width and maximality.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem middleHalfInterval_centered (a : ℝ) :
    middleHalfInterval (-a) a = Icc (-a / 2) (a / 2) := by
  unfold middleHalfInterval
  congr 1 <;> ring

/-- `41/50 < M/2`; the same statement and proof as `forty_one_fiftieths_lt_half_M` of
`TerminalScalar`, which this module does not import. -/
private theorem fullWidthGap_forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 := by
  have hY : (19 / 64 : ℝ) < Y := cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])
  unfold M beta
  linarith [Y_equation, self_sub_cube_div_three_le_arctan Y_pos.le,
    mul_pos (sub_pos.mpr hY) (show 0 < Y + 19 / 64 by linarith [Y_pos])]

theorem IsFullCapMaximizer.centered_half_projection_width_gt_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : (1001 / 1000 : ℝ) < a := by
  by_contra! ha1
  have hright : capRoof U (a / 2) = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rwa [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
  have hw : capWidth U = 2 * a := by rw [capWidth, hl, hr]; ring
  have hscore := hU.isCap.capScore_lt_forty_one_fiftieths_of_short_width
    (by linarith [hU.width_bounds.1, one_lt_M]) ha1
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)) hl hr
    (sub_sub_cancel 1 _).symm hright
    ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
    (sub_le_self _ (Real.arctan_pos.mpr (by linarith [sqrt_two_sub_one_strict_bounds.1])).le)
    le_rfl
  exact (not_lt_of_ge hU.reference_le) (hscore.trans fullWidthGap_forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.centered_half_projection_width_gt_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : (1001 / 1000 : ℝ) < a := by
  by_cases hm : 0 ≤ m
  · exact hU.centered_half_projection_width_gt_of_affine_nonneg hl hr hheight hm haffine
  have hVl : horizontalLeft (AmbidextrousSofa.horizontalMirror U) = -a := by
    rw [horizontalLeft_horizontalMirror hU.isCap, hr]
  have hVr : horizontalRight (AmbidextrousSofa.horizontalMirror U) = a := by
    rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg]
  refine hU.horizontalMirror.centered_half_projection_width_gt_of_affine_nonneg hVl hVr
    (by rw [capHeight_horizontalMirror, hheight]) (m := -m) (c := c) (by linarith)
    fun x hx => ?_
  rw [hVl, hVr, middleHalfInterval_centered] at hx
  rw [capRoof_horizontalMirror, haffine (-x) (by
    rw [hl, hr, middleHalfInterval_centered]
    constructor <;> linarith [hx.1, hx.2])]
  ring

/-- This rational lower bound concerns the original full maximizer's
width, including those that are neither centered nor canonical. -/
theorem IsFullCapMaximizer.width_gt_1001_div_500
    {U : Set Plane} (hU : IsFullCapMaximizer U) : (1001 / 500 : ℝ) < capWidth U := by
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    (capScore_centeredCap hU.isCap _).ge).exists_heightOne_affine_middle
  have := hV.centered_half_projection_width_gt_of_affine
    ((congrArg sInf hproj).trans ((horizontalLeft_centeredCap hU.isCap).trans (neg_div _ _)))
    ((congrArg sSup hproj).trans (horizontalRight_centeredCap hU.isCap)) hheight haffine
  linarith

theorem IsFullCapMaximizer.two_lt_width {U : Set Plane} (hU : IsFullCapMaximizer U) :
    (2 : ℝ) < capWidth U := by
  linarith [hU.width_gt_1001_div_500]

end AmbidextrousSofa
