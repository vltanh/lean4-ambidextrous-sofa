module

public import AmbidextrousSofa.Analysis.ThreeAngleShortTail

@[expose] public section

/-!
# Short-width exclusion for the reflection-invariant three-angle objective

The charged roof cuts and both additional niche tails belong to the
actual cap. The objective uses only the diagonal and its two nearby
corners, so the resulting strict comparison can be reflected without
introducing an outgoing wall on the opposite side.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngleScore_lt_of_short_width
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1001 / 1000) (hh : 0 ≤ h)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    threeAngleComparisonScore U < 41 / 50 := by
  by_contra hbad
  have hscore : 41 / 50 ≤ threeAngleComparisonScore U := le_of_not_gt hbad
  let k := Real.sqrt 2 - 1
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1 + h
  let δL := nearDiagonalLeftDeficit U h k v
  let δR := nearDiagonalRightDeficit U k u
  let EL := shortLeftTailHeight k h δL
  let ER := shortRightTailHeight δR
  let G := nearTriangleCoefficient k
  let L := shortOuterTipAllowance k + h / 4
  let D := diagonalRoofDeficit U a h u v
  have hk0 : 2 / 5 < k := sqrt_two_sub_one_strict_bounds.1
  have hk1 : k < 169 / 408 := sqrt_two_sub_one_strict_bounds.2.1
  have hk : 0 < k := by linarith only [hk0]
  have hklt : k < 1 := by linarith only [hk1]
  have hksq : k ^ 2 + 2 * k = 1 := sqrt_two_sub_one_quadratic
  obtain ⟨ha9, hh23, hu, hv, hu323, hv323, hm, _, _, _, huout, hvout, _, hD9⟩ :=
    hU.threeAngle_short_diagonal_geometry ha ha1 hh hl hr hleft hright hscore
  have hha : h ≤ a := by linarith only [ha9, hh23]
  have hhhalf : h ≤ a / 2 := by linarith only [ha9, hh23]
  have hhk : h ≤ k * a := by
    have hprod := mul_nonneg (show 0 ≤ k - 2 / 5 by linarith only [hk0]) ha.le
    nlinarith only [hprod, ha9, hh23]
  have huactual : diagonalRight U = 1 + u := by dsimp [u]; ring
  have hvactual : diagonalLeft U = 1 - h + v := by dsimp [v]; ring
  have hδL := hU.nearDiagonalLeftDeficit_mem ha hh hk.le hklt.le hhk hl hr
    hleft hright haffine hvactual hv.1
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hklt.le hl hr hright huactual
  have hcompR := hU.diagonalRight_companion_support_ge hk.le hklt.le huactual
  have hcompL := hU.diagonalLeft_companion_support_ge ha hh hha hk.le hklt.le hl hr
    hleft hright haffine hvactual
  obtain ⟨_, _, hcut⟩ := hU.short_diagonal_cut_payment ha hh hk0 hklt hksq hl hr
    hleft hright huactual hvactual hδL hδR hvout huout hD9
  have hcut' : G * (δL ^ 2 + δR ^ 2) ≤ D := by
    convert hcut using 1 <;> dsimp [G, D, δL, δR, nearTriangleCoefficient] <;> ring
  have hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2) :=
    tilted_diagonal_apex_mem ha.le hh hhhalf hu hv
  obtain ⟨hpL, hendL, hcompEL, hclipL⟩ :=
    short_left_tail_geometry hk0 hk1 hksq hh hh23 hδL.1 hv323 hm hd
  obtain ⟨hpR, hendR, hcompER, hclipR⟩ :=
    short_right_tail_geometry hk0 hk1 hksq hh hh23 hδR.1 hu323 hm hd
  obtain ⟨hη, _, _, hLbase⟩ := short_nearDiagonal_constants hk0 hk1 hksq
  have hL0 : 0 ≤ L := by dsimp [L]; linarith only [hLbase, hh]
  have hN := hU.threeAngle_integral_ge_diagonal_two_tails ha hk hklt hksq rfl
    huactual hvactual hcompR hcompL hη.le hd hpL hpR hendL.le hendR.le
    hcompEL hcompER hL0 hclipL hclipR
  have hD := hU.diagonalRoofDeficit_eq h hu hv
  have hscoreeq := threeAngleComparisonScore_centered hl hr
  have hpaid : threeAngleComparisonScore U + D + G * (EL ^ 2 + ER ^ 2) - k * L ^ 2 ≤
      diagonalRelaxation a h k u v := by
    dsimp [D, G, EL, ER, δL, δR] at ⊢
    unfold diagonalRelaxation
    linarith only [hN, hD, hscoreeq]
  have hG0 : 0 ≤ G := by
    dsimp [G, nearTriangleCoefficient]
    exact div_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hk.le)
      (sub_nonneg.mpr hklt.le))
  have hηleft : 0 ≤ (2 / 25 : ℝ) - (1 - k) * h :=
    short_left_peak_height_nonneg hk0 hh hh23
  have hpayL := mul_le_mul_of_nonneg_left (positive_deficit_square_payment hηleft δL) hG0
  have hpayR := mul_le_mul_of_nonneg_left
    (positive_deficit_square_payment (by norm_num : (0 : ℝ) ≤ 2 / 25) δR) hG0
  have hpay : G / 2 * (((2 / 25) - (1 - k) * h) ^ 2 + (2 / 25) ^ 2) ≤
      G * (δL ^ 2 + δR ^ 2) + G * (EL ^ 2 + ER ^ 2) := by
    dsimp [EL, ER, shortLeftTailHeight, shortRightTailHeight]
    nlinarith only [hpayL, hpayR]
  have htotal : G / 2 * (((2 / 25) - (1 - k) * h) ^ 2 + (2 / 25) ^ 2) ≤
      D + G * (EL ^ 2 + ER ^ 2) :=
    hpay.trans (add_le_add_right hcut' _)
  have hcritical := diagonalRelaxation_le_critical a h k u v
    (by linarith only [hk1, hh23, ha9])
    (by linarith only [hk, hh]) (by linarith only [hk0, hh23])
  have hwidth := diagonal_critical_width_mono ha1
    (by linarith only [hk0] : (1001 / 1000 : ℝ) ≤ 1 + k)
  have hrelax : diagonalRelaxation a h k u v ≤
      (2001 / 1000) * k - 1 / 2000000 - k * h / 2 - h ^ 2 / 8 := by
    nlinarith only [hcritical, hwidth, hksq]
  have hfinal : threeAngleComparisonScore U ≤ shortWidthPaidEnvelope k h := by
    dsimp [shortWidthPaidEnvelope]
    change threeAngleComparisonScore U ≤
      (2001 / 1000) * k - 1 / 2000000 - k * h / 2 - h ^ 2 / 8 -
        G / 2 * (((2 / 25) - (1 - k) * h) ^ 2 + (2 / 25) ^ 2) + k * L ^ 2
    linarith only [hpaid, htotal, hrelax]
  exact (not_lt_of_ge hscore) (hfinal.trans_lt (shortWidthPaidEnvelope_lt hk0 hk1 hksq hh))

end AmbidextrousSofa
