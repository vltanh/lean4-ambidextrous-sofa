module

public import AmbidextrousSofa.Analysis.FullTriangleArea
public import AmbidextrousSofa.Analysis.FullWidthCeiling

@[expose] public section

/-!
# The actual three-triangle width exclusion

Both nearby support cuts and both full additional niche triangles are
constructed from the original cap. Actual endpoint stationarity and the
middle niche bound of a narrow box pay the floor losses. The resulting
strict score comparison lowers every full maximizer's quarter-width below
thirty-seven fiftieths.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

theorem IsDownwardCap.capScore_lt_of_full_triangles_and_endpoint_laws
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 37 / 25 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEPR : capRoof U a = 1 / 2 + h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (a / 2) - sweptNiche U (Real.pi / 2) (-a / 2)) / 4)
    (hEPL : capRoof U (-a) = 1 / 2 - 3 * h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (-a / 2) - sweptNiche U (Real.pi / 2) (a / 2)) / 4) :
    capScore U (Real.pi / 2) < 41 / 50 := by
  obtain ⟨hk0, hk1, hksq, hc0, hc1⟩ := fullTriangle_offset_bounds
  obtain ⟨hnL, hnR⟩ := hU.middle_niche_le_two_fifths_of_endpoints (C := a / 2)
    (by rw [hl]; ring) (by rw [hr]; ring) (by linarith only [ha1])
  rw [← neg_div] at hnL
  have hn0 := sweptNiche_nonneg U (Real.pi / 2) (a / 2)
  have hn1 := sweptNiche_nonneg U (Real.pi / 2) (-a / 2)
  obtain ⟨hq, hS⟩ := hU.threeAngleScore_le_full_triangles (by linarith only [ha0, hh1])
    ha1 hh0 hh1 hl hr hleft hright haffine (by linarith only [hEPR, hEPL, hn0, hn1])
  have hloss := floor_loss_le_of_bounds (k := Real.sqrt 2 - 1)
    (t := 2 * fullTriangleCos (Real.sqrt 2 - 1) - (1 + (Real.sqrt 2 - 1))) (by linarith only [hk1])
    (by linarith only [hEPR, hnL, hn0] : 1 - capRoof U a ≤ 3 / 5 - h / 4)
    (by linarith only [hEPL, hnR, hn1] : 1 - capRoof U (-a) ≤ 3 / 5 + 3 * h / 4)
    (by linarith only [hc1, hk0, hh1]) (by linarith only [hc1, hk0, hh0])
  have hfin := fullTriangleRelaxation_add_loss_lt ha0 hh0 hh1 hk0 hk1 hksq hc0 hc1 hq
  rw [fullTriangleLoss] at hfin
  linarith only [hU.capScore_le_threeAngleScore
    (sub_le_self _ (Real.arctan_pos.mpr (by linarith only [hk0])).le) le_rfl, hS, hloss, hfin]

theorem IsFullCapMaximizer.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (37 / 25 : ℝ) := by
  by_contra! ha0
  obtain ⟨hright, hAff⟩ := hU.centered_middle hl hr hheight hm haffine
  have hleft := (sub_sub_cancel 1 (capRoof U (-a / 2))).symm
  have hEP := hU.centered_endpoint_laws hheight hl hr hleft hright hAff
  exact (not_lt_of_ge hU.reference_le) ((hU.isCap.capScore_lt_of_full_triangles_and_endpoint_laws
    ha0 (hU.centered_half_projection_width_lt_of_affine_nonneg hl hr hheight hm haffine).le
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _))
    (hU.centered_intermediate_width_tilt hl hr hheight hm haffine).1.le
    hl hr hleft hright hAff hEP.1 hEP.2).trans forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.quarter_width_lt_thirty_seven_fiftieths
    {U : Set Plane} (hU : IsFullCapMaximizer U) : capWidth U / 4 < (37 / 50 : ℝ) := by
  have : capWidth U / 2 < (37 / 25 : ℝ) := hU.half_width_of_nonneg_slope
    fun _ _ _ _ hV hl hr hh hm haff =>
      hV.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg hl hr hh hm haff
  linarith

end AmbidextrousSofa
