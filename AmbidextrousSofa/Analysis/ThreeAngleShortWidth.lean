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
  by_contra! hscore
  obtain ⟨ha9, hh23, hu, hv, hu323, hv323, hm, -, -, -, huout, hvout, -, hD9⟩ :=
    hU.threeAngle_short_diagonal_geometry ha ha1 hh hl hr hleft hright hscore
  generalize hkdef : Real.sqrt 2 - 1 = k at huout hvout
  obtain ⟨hk0, hk1, -⟩ := hkdef ▸ sqrt_two_sub_one_strict_bounds
  have hksq : k ^ 2 + 2 * k = 1 := hkdef ▸ sqrt_two_sub_one_quadratic
  have hk : 0 < k := by linarith only [hk0]
  have hklt : k < 1 := by linarith only [hk1]
  generalize hudef : diagonalRight U - 1 = u at hu hu323 hm huout hD9
  generalize hvdef : diagonalLeft U - 1 + h = v at hv hv323 hm hvout hD9
  have huactual : diagonalRight U = 1 + u := by linarith only [hudef]
  have hvactual : diagonalLeft U = 1 - h + v := by linarith only [hvdef]
  have hδL := hU.nearDiagonalLeftDeficit_mem ha hh hk.le hklt.le
    (by linarith only [mul_nonneg (sub_nonneg.2 hk0.le) ha.le, ha9, hh23]) hl hr hleft hright
    haffine hvactual hv.1
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hklt.le hl hr hright huactual
  obtain ⟨-, -, hcut⟩ := hU.short_diagonal_cut_payment ha hh hk0 hklt hksq hl hr
    hleft hright huactual hvactual hδL hδR hvout huout hD9
  have hd := tilted_diagonal_apex_mem ha.le hh (by linarith only [ha9, hh23]) hu hv
  obtain ⟨hpL, hendL, hcompEL, hclipL⟩ :=
    short_left_tail_geometry hk0 hk1 hksq hh hh23 hδL.1 hv323 hm hd
  obtain ⟨hpR, hendR, hcompER, hclipR⟩ :=
    short_right_tail_geometry hk0 hk1 hksq hh hh23 hδR.1 hu323 hm hd
  obtain ⟨hη, -, -, hLbase⟩ := short_nearDiagonal_constants hk0 hk1 hksq
  have hN := hU.threeAngle_integral_ge_diagonal_two_tails ha hk hklt hksq hkdef.symm
    huactual hvactual (hU.diagonalRight_companion_support_ge hk.le hklt.le huactual)
    (hU.diagonalLeft_companion_support_ge ha hh (by linarith only [ha9, hh23]) hk.le hklt.le hl hr
      hleft hright haffine hvactual) hη.le hd hpL hpR hendL.le hendR.le hcompEL hcompER
    (by linarith only [hLbase, hh]) hclipL hclipR
  -- The squared deficits pay for the two tails.
  have hG0 : 0 ≤ nearTriangleCoefficient k :=
    one_div_nonneg.2 (mul_nonneg (mul_nonneg zero_le_two hk.le) (sub_nonneg.2 hklt.le))
  have hpayL := mul_le_mul_of_nonneg_left (positive_deficit_square_payment
    (short_left_peak_height_nonneg hk0 hh hh23) (nearDiagonalLeftDeficit U h k v)) hG0
  have hpayR := mul_le_mul_of_nonneg_left (positive_deficit_square_payment
    (by norm_num : (0 : ℝ) ≤ 2 / 25) (nearDiagonalRightDeficit U k u)) hG0
  have hD := hU.diagonalRoofDeficit_eq h hu hv
  have hrelax := diagonalRelaxation_le_critical a h k u v (by linarith only [hk1, hh23, ha9])
    (by linarith only [hk, hh]) (by linarith only [hk0, hh23])
  have hwidth := diagonal_critical_width_mono ha1
    (by linarith only [hk0] : (1001 / 1000 : ℝ) ≤ 1 + k)
  have henv := shortWidthPaidEnvelope_lt hk0 hk1 hksq hh
  -- Score, roof deficit and tail payment together stay below the critical relaxation value,
  -- so the score is at most the paid envelope, which is below `41 / 50`.
  rw [← one_div_mul_eq_div] at hcut
  change nearTriangleCoefficient k * _ ≤ _ at hcut
  unfold diagonalRelaxation at hrelax
  unfold shortWidthPaidEnvelope at henv
  unfold shortLeftTailHeight shortRightTailHeight at hN
  linarith only [hscore, threeAngleComparisonScore_centered hl hr, hD, hN, hcut, hpayL, hpayR,
    hrelax, hwidth, hksq, henv]

end AmbidextrousSofa
