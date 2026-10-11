module

public import AmbidextrousSofa.Analysis.ThreeAngleWideWidth

@[expose] public section

/-!
# Actual wide-width exclusion with both endpoint laws

The full barrier lies above the three-angle barrier. A high full score
therefore forces the compact wide box, where the middle niche is at most
two thirds. The two endpoint laws then give the endpoint height bounds of
the three-angle wide-width exclusion. The endpoint laws themselves are
supplied by actual full maximality.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- The wide-width exclusion for the actual full-angle cap. The two displayed endpoint laws
are geometric stationarity identities, subsequently supplied by actual full maximality. -/
theorem IsDownwardCap.capScore_lt_of_wide_width_and_endpoint_laws
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 8 / 5 ≤ a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEPR : capRoof U a = 1 / 2 + h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (a / 2) - sweptNiche U (Real.pi / 2) (-a / 2)) / 4)
    (hEPL : capRoof U (-a) = 1 / 2 - 3 * h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (-a / 2) - sweptNiche U (Real.pi / 2) (a / 2)) / 4) :
    capScore U (Real.pi / 2) < 41 / 50 := by
  by_contra! hscore
  have hnR0 := sweptNiche_nonneg U (Real.pi / 2) (a / 2)
  have hnL0 := sweptNiche_nonneg U (Real.pi / 2) (-a / 2)
  have hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a) := by linarith only [hEPR, hEPL, hnR0, hnL0]
  have h3 := hscore.trans (hU.capScore_le_threeAngleScore
    (sub_le_self _ (Real.arctan_pos.mpr (by linarith [sqrt_two_sub_one_strict_bounds.1])).le) le_rfl)
  obtain ⟨ha9, -, -⟩ :=
    hU.threeAngle_wide_high_score_box ha0 ha1 hh0 hh1 hl hr hleft hright haffine hEP h3
  have hNbox := hU.middle_niche_le_two_thirds_of_box
    (hU.subset_centeredBox_of_endpoints (by rw [hl]; ring) (by rw [hr]; ring)) (C := a / 2)
    (by linarith only [ha9])
  rw [← neg_div] at hNbox
  exact (hU.threeAngleScore_lt_of_wide_width_and_endpoint_bounds ha0 ha1 hh0 hh1 hl hr hleft hright
    haffine hEP (by linarith only [hNbox.1, hEPR, hnR0])
    (by linarith only [hNbox.2, hEPL, hnL0])).not_ge h3

theorem IsFullCapMaximizer.centered_endpoint_laws {U : Set Plane}
    (hU : IsFullCapMaximizer U) {a h : ℝ} (hheight : capHeight U = 1)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    capRoof U a = 1 / 2 + h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (a / 2) - sweptNiche U (Real.pi / 2) (-a / 2)) / 4 ∧
    capRoof U (-a) = 1 / 2 - 3 * h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (-a / 2) - sweptNiche U (Real.pi / 2) (a / 2)) / 4 := by
  obtain ⟨hR, hL⟩ := hU.endpoint_heights_eq_pressures_of_affine hheight
    (by simpa only [hl, hr, middleHalfInterval_centered] using haffine)
  simp only [capRightEndpointPressure, rightEndpointPressure, capLeftEndpointPressure,
    leftEndpointPressure, hl, hr, show a - (a - -a) / 4 = a / 2 by ring,
    show -a + (a - -a) / 4 = -a / 2 by ring, hleft, hright] at hR hL
  constructor <;> linarith only [hR, hL]

end AmbidextrousSofa
