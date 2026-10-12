module

public import AmbidextrousSofa.Analysis.ThreeAngleWideWidth
public import AmbidextrousSofa.Analysis.PartialTriangleScalar

@[expose] public section

/-!
# Actual wide-width exclusion with both endpoint laws

The two endpoint laws and the affine ceiling give the required endpoint
height bounds directly. The three-angle barrier lies below the full
barrier, so its wide-width exclusion applies to the actual full cap.
The endpoint laws themselves are supplied by full maximality.
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
  have hceiling := hU.capRoof_le_tiltedAffineCeiling (by linarith only [ha0])
    hl hr hleft hright haffine (-a)
    ((hl ▸ hr ▸ hU.horizontalProjection_eq_Icc) ▸ ⟨le_rfl, by linarith only [ha0]⟩)
  rw [tiltedAffineCeiling, mul_neg, div_mul_cancel₀ h (by linarith only [ha0] : a ≠ 0)] at hceiling
  obtain ⟨hER, hEL, hEP⟩ := partialTriangle_endpoint_lower_bounds hnR0 hnL0 hEPR hEPL
    (capRoof_le_one hU.isCompact hU.inStrip a) (by linarith only [hceiling])
  have h3 := hscore.trans (hU.capScore_le_threeAngleScore
    (sub_le_self _ (Real.arctan_pos.mpr (sub_pos.mpr Real.one_lt_sqrt_two)).le) le_rfl)
  exact (hU.threeAngleScore_lt_of_wide_width_and_endpoint_bounds ha0 ha1 hh0 hh1 hl hr hleft hright
    haffine hEP (by linarith only [hER, hh0]) (by linarith only [hEL, hh0])).not_ge h3

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
