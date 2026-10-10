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
  have hY : (19 / 64 : ℝ) < Y := by
    apply (cubic_strictMono.lt_iff_lt).mp
    rw [Y_cubic]
    norm_num [cubic]
  have hbeta : Y - Y ^ 3 / 3 ≤ beta := self_sub_cube_div_three_le_arctan Y_pos.le
  have hYsq := mul_pos (sub_pos.mpr hY)
    (show 0 < Y + 19 / 64 by linarith [Y_pos])
  unfold M
  nlinarith [Y_equation]

theorem IsFullCapMaximizer.centered_half_projection_width_gt_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : (1001 / 1000 : ℝ) < a := by
  by_contra hbad
  have hw : capWidth U = 2 * a := by unfold capWidth; rw [hl, hr]; ring
  have ha : 0 < a := by linarith only [hU.width_bounds.1, one_lt_M, hw]
  have hJ : middleHalfInterval (horizontalLeft U) (horizontalRight U) =
      Icc (-a / 2) (a / 2) := by rw [hl, hr, middleHalfInterval_centered]
  have hright : capRoof U (a / 2) = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
    exact h
  let h := 1 - capRoof U (-a / 2)
  have hh : 0 ≤ h := sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  have hleft : capRoof U (-a / 2) = 1 - h := by dsimp [h]; ring
  have hAff : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2),
      capRoof U x = m' * x + c' := by
    refine ⟨m, c, ?_⟩
    simpa only [hJ] using haffine
  have hangle : Real.pi / 2 - Real.arctan (Real.sqrt 2 - 1) ≤ Real.pi / 2 :=
    sub_le_self _ (Real.arctan_pos.mpr
      (by linarith [sqrt_two_sub_one_strict_bounds.1])).le
  have hscore := hU.isCap.capScore_lt_forty_one_fiftieths_of_short_width ha
    (le_of_not_gt hbad) hh hl hr hleft hright hAff hangle le_rfl
  exact (not_lt_of_ge hU.reference_le) (hscore.trans fullWidthGap_forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.centered_half_projection_width_gt_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : (1001 / 1000 : ℝ) < a := by
  by_cases hm : 0 ≤ m
  · exact hU.centered_half_projection_width_gt_of_affine_nonneg hl hr hheight hm haffine
  · have hV := hU.horizontalMirror
    have hVl : horizontalLeft (AmbidextrousSofa.horizontalMirror U) = -a := by
      rw [horizontalLeft_horizontalMirror hU.isCap, hr]
    have hVr : horizontalRight (AmbidextrousSofa.horizontalMirror U) = a := by
      rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg]
    have hVheight : capHeight (AmbidextrousSofa.horizontalMirror U) = 1 := by
      rw [capHeight_horizontalMirror, hheight]
    have hVaffine : ∀ x ∈ middleHalfInterval
        (horizontalLeft (AmbidextrousSofa.horizontalMirror U)) (horizontalRight (AmbidextrousSofa.horizontalMirror U)),
        capRoof (AmbidextrousSofa.horizontalMirror U) x = (-m) * x + c := by
      intro x hx
      rw [hVl, hVr, middleHalfInterval_centered] at hx
      have hxU : -x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
        rw [hl, hr, middleHalfInterval_centered]
        constructor <;> linarith only [hx.1, hx.2]
      rw [capRoof_horizontalMirror, haffine (-x) hxU]
      ring
    exact hV.centered_half_projection_width_gt_of_affine_nonneg hVl hVr hVheight
      (by linarith only [le_of_not_ge hm]) hVaffine

/-- This rational lower bound concerns the original full maximizer's
width, including those that are neither centered nor canonical. -/
theorem IsFullCapMaximizer.width_gt_1001_div_500
    {U : Set Plane} (hU : IsFullCapMaximizer U) : (1001 / 500 : ℝ) < capWidth U := by
  have hcenter : IsFullCapMaximizer (AmbidextrousSofa.centeredCap U) :=
    hU.of_score_le hU.isCap.centeredCap
      (by rw [capScore_centeredCap hU.isCap])
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := hcenter.exists_heightOne_affine_middle
  let a := capWidth U / 2
  have hl : horizontalLeft V = -a := by
    calc
      _ = horizontalLeft (AmbidextrousSofa.centeredCap U) := by unfold horizontalLeft; rw [hproj]
      _ = _ := by rw [horizontalLeft_centeredCap hU.isCap]; dsimp [a]; ring
  have hr : horizontalRight V = a := by
    calc
      _ = horizontalRight (AmbidextrousSofa.centeredCap U) := by unfold horizontalRight; rw [hproj]
      _ = _ := horizontalRight_centeredCap hU.isCap
  have hgap := hV.centered_half_projection_width_gt_of_affine hl hr hheight haffine
  dsimp [a] at hgap
  linarith only [hgap]

theorem IsFullCapMaximizer.two_lt_width {U : Set Plane} (hU : IsFullCapMaximizer U) :
    (2 : ℝ) < capWidth U := by
  linarith only [hU.width_gt_1001_div_500]

end AmbidextrousSofa
