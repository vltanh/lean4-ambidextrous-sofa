module

public import AmbidextrousSofa.Analysis.ThreeAngleDeficit
public import AmbidextrousSofa.Analysis.ThreeAngleNiche
public import AmbidextrousSofa.Analysis.WideNicheGeometry

@[expose] public section

/-!
# Wide-width exclusion for the literal three-angle objective

Only inequalities on the actual two endpoint heights enter the proof.
The proper endpoint identities imply these inequalities before any
reflection. Consequently the reflected finite comparison does not need
an endpoint law for a reflected outgoing barrier.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngleScore_lt_of_wide_width_and_endpoint_bounds
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 8 / 5 ≤ a) (ha1 : a < 3) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hER : 1 / 3 + h / 4 ≤ capRoof U a)
    (hEL : 1 / 3 - 3 * h / 4 ≤ capRoof U (-a)) :
    intervalSpatialScore (capRoof U) (threeAngleBarrier U) (horizontalLeft U)
      (horizontalRight U) < 41 / 50 := by
  by_contra! hscore
  obtain ⟨hk0, -, hk1⟩ := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  have hksq := sqrt_two_sub_one_quadratic
  set k := Real.sqrt 2 - 1
  have hk : 0 < k := by linarith only [hk0]
  have hk12 : k < 1 / 2 := by linarith only [hk1]
  have hk1' : k ≤ 1 := by linarith only [hk1]
  have ha : 0 < a := by linarith only [ha0]
  have hha : h < a := by linarith only [ha0, hh1]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  obtain ⟨hak, hspan⟩ := hU.threeAngle_wide_high_score_fitting ha0 ha1 hh0 hh1
    hl hr hleft hright haffine hEP hscore
  obtain ⟨huv, hvv, heR, heL⟩ :=
    hU.wide_diagonal_parameters ha hh0 hhhalf hl hr hleft hright haffine
  have hm := hU.wide_diagonal_midpoint_ge ha hh0 hhhalf hl hr hleft hright haffine hEP
  obtain ⟨u, hu⟩ : ∃ u, diagonalRight U = 1 + u := ⟨_, (add_sub_cancel _ _).symm⟩
  obtain ⟨v, hv⟩ : ∃ v, diagonalLeft U = 1 + v := ⟨_, (add_sub_cancel _ _).symm⟩
  simp only [hu, hv, add_sub_cancel_left] at huv hvv heR heL hm
  have hzk : h / a < k := by
    rw [div_lt_iff₀ ha]
    linarith only [mul_nonneg (show 0 ≤ a - 8 / 5 by linarith only [ha0]) hk.le, hk0, hh1]
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hk1' hl hr hright hu
  have hδL := hU.wideLeftSupportDeficit_mem ha hha hk1' hzk.le hl hr hleft hright haffine hv
  have hNorm := wide_norm_rational_bounds hk0 hk1
  have hpoints := hU.wide_near_intercepts_lower ha hl hr hleft hright (k := k)
  have hloss := wide_truncation_loss_sum_le ha0 hh0 hk0 hk12 hksq hNorm.2.2 hpoints.1 hpoints.2
    heR heL (by linarith only [heR, hER]) (by linarith only [heL, hEL])
  have hgain := wide_gain_sum_ge_demand hk hksq hEP (wideNearRightIntercept_eq ha hha k v)
    (wideNearLeftIntercept_eq U k u) (wideLeftTiltPenalty_bounds ha hh0 hk1'
      (wideLeftIntersection_mem ha hha hvv.1 hvv.2)).2 hloss
  have hpayment := wide_positive_square_payment hk hδR.1 hδL.1
    (sub_le_iff_le_add.mp hgain)
  have hcut := hU.wideRoofDeficit_ge_support_cuts ha hh0 hha hk hk1' hzk
    hl hr hleft hright haffine hu hv huv hvv
  have hfit := hU.wide_piece_fitting ha0 hh0 hh1 hspan hk0 hk1 hksq
    hl hr hleft hright haffine hu hv hvv hm
  have hN := hU.threeAngle_integral_ge_wide_pieces hk hksq rfl hl hr hu hv
    ⟨by linarith only [huv.1, hvv.2, hh0, ha], by linarith only [huv.2, hvv.1, hhhalf]⟩
    hfit.1 hfit.2.1 hfit.2.2.1 hfit.2.2.2
  rw [max_eq_left (by linarith only [hm, ha0, hh1, hk1] : 0 ≤ (u + v) / 2 - k)] at hN
  simp only [wideEndpointIntercept] at hN
  have hD := hU.wideRoofDeficit_eq ha hha huv hvv
  have hF := wideDiagonalMajorant_le_half (k := k) ha0 hh0 hh1 hak u v
  have hpaid := widePaidBound_lt (m := (u + v) / 2) (h := h) ha0 hk0 sqrt_two_sub_one_bounds.2.1 hksq hNorm.2.1.le
  simp only [wideDiagonalMajorant, wideHalfBound, wideExteriorMajorant,
    widePaidBound] at hF hD hpaid
  rw [hl, hr, intervalSpatialScore_centered] at hscore
  linarith only [hD, hN, hF, hpaid, hpayment, hcut, hscore,
    mul_le_mul_of_nonneg_right (wide_tilt_coefficient_ge ha0) hh0]

end AmbidextrousSofa
