module

public import AmbidextrousSofa.Analysis.ShortWidthExclusion
public import AmbidextrousSofa.Analysis.TopFacetEndpoints

@[expose] public section

/-!
# Every actual full maximizer has width strictly greater than two

Centering and the height and middle canonicalization keep the literal
projection width and maximality, and reflection turns a negative middle
slope. A half-width bound proved for canonical maximizers with a rising
affine middle therefore holds for every full maximizer. The short-width
exclusion gives the stronger rational gap.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem middleHalfInterval_centered (a : ℝ) :
    middleHalfInterval (-a) a = Icc (-a / 2) (a / 2) := by
  unfold middleHalfInterval
  congr 1 <;> ring

/-- At a centered maximizer of height one whose affine middle roof rises, the right middle
endpoint has height one, and the middle roof is affine on `[-a/2, a/2]`. -/
theorem IsFullCapMaximizer.centered_middle {U : Set Plane} (hU : IsFullCapMaximizer U)
    {a m c : ℝ} (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (a / 2) = 1 ∧ ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c := by
  have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
  rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
  exact ⟨h, m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩

/-- A half-width bound proved for centered maximizers of height one with a rising affine middle
roof holds for the half width of every full maximizer. -/
theorem IsFullCapMaximizer.half_width_of_nonneg_slope {P : ℝ → Prop} {U : Set Plane}
    (hU : IsFullCapMaximizer U)
    (hP : ∀ (V : Set Plane) (a m c : ℝ), IsFullCapMaximizer V → horizontalLeft V = -a →
      horizontalRight V = a → capHeight V = 1 → 0 ≤ m →
      (∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V),
        capRoof V x = m * x + c) → P a) :
    P (capWidth U / 2) := by
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    (capScore_centeredCap hU.isCap _).ge).exists_heightOne_affine_middle
  have hl : horizontalLeft V = -(capWidth U / 2) :=
    (congrArg sInf hproj).trans ((horizontalLeft_centeredCap hU.isCap).trans (neg_div _ _))
  have hr : horizontalRight V = capWidth U / 2 :=
    (congrArg sSup hproj).trans (horizontalRight_centeredCap hU.isCap)
  rcases le_total 0 m with hm | hm
  · exact hP V _ m c hV hl hr hheight hm haffine
  -- A falling middle roof rises after the horizontal reflection.
  have hVl := horizontalLeft_horizontalMirror hV.isCap
  have hVr := horizontalRight_horizontalMirror hV.isCap
  refine hP _ _ (-m) c hV.horizontalMirror (by rw [hVl, hr]) (by rw [hVr, hl, neg_neg])
    (by rw [capHeight_horizontalMirror, hheight]) (by linarith) fun x hx => ?_
  rw [hVl, hVr, hl, hr, neg_neg, middleHalfInterval_centered] at hx
  rw [capRoof_horizontalMirror, haffine (-x) (by
    rw [hl, hr, middleHalfInterval_centered]; constructor <;> linarith [hx.1, hx.2])]
  ring

theorem IsFullCapMaximizer.centered_half_projection_width_gt_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : (1001 / 1000 : ℝ) < a := by
  by_contra! ha1
  obtain ⟨hright, hAff⟩ := hU.centered_middle hl hr hheight hm haffine
  have hw : capWidth U = 2 * a := by rw [capWidth, hl, hr]; ring
  exact (not_lt_of_ge hU.reference_le) ((hU.isCap.capScore_lt_forty_one_fiftieths_of_short_width
    (by linarith [hU.width_bounds.1, one_lt_M]) ha1
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)) hl hr
    (sub_sub_cancel 1 _).symm hright hAff
    (sub_le_self _ (Real.arctan_pos.mpr (by linarith [sqrt_two_sub_one_bounds.1])).le)
    le_rfl).trans forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.two_lt_width {U : Set Plane} (hU : IsFullCapMaximizer U) :
    (2 : ℝ) < capWidth U := by
  have : (1001 / 1000 : ℝ) < capWidth U / 2 := hU.half_width_of_nonneg_slope
    fun _ _ _ _ hV hl hr hh hm haff =>
      hV.centered_half_projection_width_gt_of_affine_nonneg hl hr hh hm haff
  linarith

end AmbidextrousSofa
