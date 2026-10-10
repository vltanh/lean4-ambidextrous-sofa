import AmbidextrousSofa.Analysis.ThreeAngleDeficit

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
    threeAngleComparisonScore U < 41 / 50 := by
  by_contra hbad
  have hscore : 41 / 50 ≤ threeAngleComparisonScore U := le_of_not_gt hbad
  let k := Real.sqrt 2 - 1
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1
  let m := (u + v) / 2
  let δR := nearDiagonalRightDeficit U k u
  let δL := wideLeftSupportDeficit U a h k v
  let τ := wideLeftTiltPenalty a h k v
  let bR := wideNearRightIntercept U k
  let bL := wideNearLeftIntercept U k
  let BR := wideEndpointIntercept a (capRoof U a) k
  let BL := wideEndpointIntercept a (capRoof U (-a)) k
  let HR := wideTruncatedGain k u bR BR
  let HL := wideTruncatedGain k v bL BL
  let D := wideRoofDeficit U a h u v
  let G := ((max HR 0) ^ 2 + (max HL 0) ^ 2) / (2 * (1 + k))
  let F := wideDiagonalMajorant a h k u v
  have ha : 0 < a := by linarith only [ha0]
  have hha : h < a := by linarith only [ha0, hh1]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hk : 0 < k := by dsimp [k]; linarith only [sqrt_two_sub_one_strict_bounds.1]
  have hk2 : 2 / 5 < k := sqrt_two_sub_one_strict_bounds.1
  have hk1 : k < 29 / 70 := sqrt_two_sub_one_strict_bounds.2.2
  have hksq : k ^ 2 + 2 * k = 1 := sqrt_two_sub_one_quadratic
  have hk41 : 41 / 100 < k := by
    have h := diagonal_offset_gt_forty_one_ninety_ninths hk hksq
    linarith only [h]
  have hu : diagonalRight U = 1 + u := by dsimp [u]; ring
  have hv : diagonalLeft U = 1 + v := by dsimp [v]; ring
  obtain ⟨ha9, hhquarter, hah⟩ := hU.threeAngle_wide_high_score_box ha0 ha1 hh0 hh1
    hl hr hleft hright haffine hEP hscore
  have hp := hU.wide_diagonal_parameters ha hh0 hhhalf hl hr hleft hright haffine
  have huv : u ∈ Icc (a / 2) a := hp.1
  have hvv : v ∈ Icc (a / 2 - h) (a - 3 * h / 2) := hp.2.1
  have heR : capRoof U a ≤ 1 - (a - u) := hp.2.2.1
  have heL : capRoof U (-a) ≤ 1 - (a - v) := hp.2.2.2
  have hm : a - 1 / 2 - h / 4 ≤ m :=
    hU.wide_diagonal_midpoint_ge ha hh0 hhhalf hl hr hleft hright haffine hEP
  have hm0 : 0 ≤ m := by linarith only [hm, ha0, hhquarter]
  have hmk : k ≤ m := by linarith only [hm, ha0, hhquarter, hk1]
  have hzk : h / a < k := by
    apply (div_lt_iff₀ ha).mpr
    have hp := mul_nonneg (show 0 ≤ a - 8 / 5 by linarith only [ha0]) hk.le
    nlinarith only [hp, hk2, hhquarter]
  have hδR : δR ∈ Icc 0 (k * (u - a / 2)) :=
    hU.nearDiagonalRightDeficit_mem ha hk.le (by linarith only [hk1]) hl hr hright hu
  have hδL : δL ∈ Icc 0 ((k - h / a) * (wideLeftIntersection a h v - a / 2)) :=
    hU.wideLeftSupportDeficit_mem ha hha (by linarith only [hk1]) hzk.le
      hl hr hleft hright haffine hv
  have hNorm := wide_norm_rational_bounds hk41 hk1
  have hpoints := hU.wide_near_intercepts_lower ha hl hr hleft hright (k := k)
  have hwR : a - u ≤ 2 / 3 - h / 4 := by linarith only [heR, hER]
  have hwL : a - v ≤ 2 / 3 + 3 * h / 4 := by linarith only [heL, hEL]
  have hloss := wide_truncation_loss_sum_le ha0 hh0 hk2
    (by linarith only [hk1]) hksq hNorm.2.2 hpoints.1 hpoints.2 heR heL hwR hwL
  have hτ : τ ≤ 3 * (1 - k) * h / 2 :=
    (wideLeftTiltPenalty_bounds ha hh0 (by linarith only [hk1])
      (wideLeftIntersection_mem ha hha hvv.1 hvv.2)).2
  have hIR : bR = 1 - nearDiagonalNorm k + k * v - δL - τ :=
    wideNearRightIntercept_eq ha hha k v
  have hIL : bL = 1 - nearDiagonalNorm k + k * u - δR := wideNearLeftIntercept_eq U k u
  have hgain : wideGainDemand a m h - (δR + δL) / 2 ≤ HR + HL :=
    wide_gain_sum_ge_demand ha.le hh0 hm0 hk41 hk1 hksq hNorm.2.1.le
      hEP hIR hIL hτ hloss
  have hpayment : (max (wideGainDemand a m h) 0) ^ 2 / 8 ≤
      (δR ^ 2 + δL ^ 2) / (2 * k) + G :=
    wide_positive_square_payment hk (by linarith only [hk1]) hδR.1 hδL.1
      (by linarith only [hgain])
  have hcut : (δR ^ 2 + δL ^ 2) / (2 * k) ≤ D :=
    hU.wideRoofDeficit_ge_support_cuts ha hh0 hha hk (by linarith only [hk1]) hzk
      hl hr hleft hright haffine hu hv huv hvv
  have hfit := hU.wide_piece_fitting ha0 hh0 hhquarter hah hk41 hk1 hksq
    hl hr hleft hright haffine hu hv hvv hm
  have hd : (u - v) / 2 ∈ Icc (-a / 2) (a / 2) := by
    constructor <;> linarith only [huv.1, huv.2, hvv.1, hvv.2, hh0, hhhalf, ha]
  have hN := hU.threeAngle_integral_ge_wide_pieces hk hksq rfl
    hl hr hu hv hd hfit.1 hfit.2.1 hfit.2.2.1 hfit.2.2.2
  change (max (m - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
    (max (v - k - a / 2) 0) ^ 2 / 2 + G ≤ _ at hN
  rw [max_eq_left (sub_nonneg.mpr hmk)] at hN
  have hD := hU.wideRoofDeficit_eq ha hha huv hvv
  have hP := threeAngleComparisonScore_centered hl hr
  have hpaid : threeAngleComparisonScore U + D + G ≤ F := by
    change D = wideExteriorMajorant a h u v - _ at hD
    dsimp [F, wideDiagonalMajorant]
    change threeAngleComparisonScore U + D + G ≤
      wideExteriorMajorant a h u v - (m - k) ^ 2 +
        ((max (u - k - a / 2) 0) ^ 2 + (max (v - k - a / 2) 0) ^ 2) / 2
    linarith only [hP, hD, hN]
  have hF : F ≤ wideHalfBound a m h k := wideDiagonalMajorant_le_half ha0 hh0 hh1
    (by linarith only [ha9, hk2]) u v
  have hcoef := mul_le_mul_of_nonneg_right (wide_tilt_coefficient_ge ha0) hh0
  have hfinal : threeAngleComparisonScore U ≤ widePaidBound a m h k := by
    unfold wideHalfBound at hF
    unfold widePaidBound
    linarith only [hpaid, hF, hcoef, hpayment, hcut]
  exact (not_lt_of_ge hscore) (hfinal.trans_lt (widePaidBound_lt ha0 hh0 hm hk41 hk1 hksq))

end AmbidextrousSofa
