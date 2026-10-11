module

public import AmbidextrousSofa.Analysis.WideNicheGeometry

@[expose] public section

/-!
# Actual wide-width exclusion with both endpoint laws

The score, roof deficit, diagonal supports, nearby support deficits, and
two retained niche pieces all refer to the original cap. The endpoint
laws first force the compact wide box, then bound the loss from both
baseline truncations. The ordinary exterior and niche areas pay the
positive-square term in the final global comparison.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- TW.2 for the actual full-angle cap. The two displayed endpoint laws
are geometric stationarity identities, subsequently supplied by actual
full maximality. Every support and area payment is constructed here. -/
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
  obtain ⟨hk2, -, hk1⟩ := sqrt_two_sub_one_strict_bounds
  have hksq := sqrt_two_sub_one_quadratic
  set k := Real.sqrt 2 - 1
  have hk : 0 < k := by linarith only [hk2]
  have hk41 : 41 / 100 < k := by linarith only [diagonal_offset_gt_forty_one_ninety_ninths hk hksq]
  have hk12 : k < 1 / 2 := by linarith only [hk1]
  have hk1' : k ≤ 1 := by linarith only [hk1]
  have ha : 0 < a := by linarith only [ha0]
  have hha : h < a := by linarith only [ha0, hh1]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hnR0 := sweptNiche_nonneg U (Real.pi / 2) (a / 2)
  have hnL0 := sweptNiche_nonneg U (Real.pi / 2) (-a / 2)
  have hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a) := by linarith only [hEPR, hEPL, hnR0, hnL0]
  obtain ⟨ha9, hhquarter, hah⟩ := hU.wide_high_score_box ha0 ha1 hh0 hh1
    hl hr hleft hright haffine hEP (by linarith only [Real.pi_pos]) le_rfl hscore
  obtain ⟨huv, hvv, heR, heL⟩ :=
    hU.wide_diagonal_parameters ha hh0 hhhalf hl hr hleft hright haffine
  have hm := hU.wide_diagonal_midpoint_ge ha hh0 hhhalf hl hr hleft hright haffine hEP
  obtain ⟨u, hu⟩ : ∃ u, diagonalRight U = 1 + u := ⟨_, (add_sub_cancel _ _).symm⟩
  obtain ⟨v, hv⟩ : ∃ v, diagonalLeft U = 1 + v := ⟨_, (add_sub_cancel _ _).symm⟩
  simp only [hu, hv, add_sub_cancel_left] at huv hvv heR heL hm
  have hzk : h / a < k := by
    rw [div_lt_iff₀ ha]
    linarith only [mul_nonneg (show 0 ≤ a - 8 / 5 by linarith only [ha0]) hk.le, hk2, hhquarter]
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hk1' hl hr hright hu
  have hδL := hU.wideLeftSupportDeficit_mem ha hha hk1' hzk.le hl hr hleft hright haffine hv
  have hNorm := wide_norm_rational_bounds hk41 hk1
  have hpoints := hU.wide_near_intercepts_lower ha hl hr hleft hright (k := k)
  have hNbox := hU.middle_niche_le_two_thirds_of_box
    (hU.subset_centeredBox_of_endpoints (by rw [hl]; ring) (by rw [hr]; ring)) (C := a / 2)
    (by linarith only [ha9])
  rw [← neg_div] at hNbox
  have hloss := wide_truncation_loss_sum_le ha0 hh0 hk2 hk12 hksq hNorm.2.2 hpoints.1 hpoints.2
    heR heL (by linarith only [hNbox.1, hEPR, heR, hnR0])
    (by linarith only [hNbox.2, hEPL, heL, hnL0])
  have hgain := wide_gain_sum_ge_demand ha.le hh0 (by linarith only [hm, ha0, hhquarter]) hk41
    hk1 hksq hNorm.2.1.le hEP (wideNearRightIntercept_eq ha hha k v)
    (wideNearLeftIntercept_eq U k u) (wideLeftTiltPenalty_bounds ha hh0 hk1'
      (wideLeftIntersection_mem ha hha hvv.1 hvv.2)).2 hloss
  have hpayment := wide_positive_square_payment hk hk12.le hδR.1 hδL.1
    (sub_le_iff_le_add.mp hgain)
  have hcut := hU.wideRoofDeficit_ge_support_cuts ha hh0 hha hk hk1' hzk
    hl hr hleft hright haffine hu hv huv hvv
  have hfit := hU.wide_piece_fitting ha0 hh0 hhquarter hah hk41 hk1 hksq
    hl hr hleft hright haffine hu hv hvv hm
  have hN := hU.wide_niche_integral_ge_pieces hk hk1' hksq rfl hl hr hu hv
    (by linarith only [Real.arctan_pos.mpr hk]) le_rfl
    ⟨by linarith only [huv.1, hvv.2, hh0, ha], by linarith only [huv.2, hvv.1, hhhalf]⟩
    hfit.1 hfit.2.1 hfit.2.2.1 hfit.2.2.2
  rw [max_eq_left (by linarith only [hm, ha0, hhquarter, hk1] : 0 ≤ (u + v) / 2 - k)] at hN
  simp only [wideEndpointIntercept] at hN
  have hP := hU.capScore_eq_intervalSpatialScore (Real.pi / 2)
  rw [hl, hr, intervalSpatialScore, show -a + (a - -a) / 4 = -a / 2 by ring,
    show a - (a - -a) / 4 = a / 2 by ring] at hP
  have hD := hU.wideRoofDeficit_eq ha hha huv hvv
  have hF := wideDiagonalMajorant_le_half (k := k) ha0 hh0 hh1 (by linarith only [ha9, hk2]) u v
  have hpaid := widePaidBound_lt ha0 hh0 hm hk41 hk1 hksq
  simp only [wideDiagonalMajorant, wideHalfBound, wideExteriorMajorant,
    widePaidBound] at hF hD hpaid
  linarith only [hP, hD, hN, hF, hpaid, hpayment, hcut, hscore,
    mul_le_mul_of_nonneg_right (wide_tilt_coefficient_ge ha0) hh0]

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
