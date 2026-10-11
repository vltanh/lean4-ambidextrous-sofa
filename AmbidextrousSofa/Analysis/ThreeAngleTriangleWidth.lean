module

public import AmbidextrousSofa.Analysis.ThreeAngleDeficit
public import AmbidextrousSofa.Analysis.PartialTriangleScalar

@[expose] public section

/-!
# The proper joint floor payment in the actual three-angle comparison

The two endpoint lower bounds and their sum constrain the two diagonal
support deficits jointly. The entire floor loss of the two signed
triangles is retained and paid by that joint constraint. All support
cuts, roof integrals and niche triangles belong to the cap being compared.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem fullTriangle_partial_loss_sum_le {a eR eL h k u v : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hh : 0 ≤ h)
    (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - v + h))
    (hwR : a - u ≤ 2 / 3 - h / 2)
    (hwL : a - v + h ≤ 2 / 3 + 2 * h / 3)
    (hwsum : (a - u) + (a - v + h) ≤ 1 + h / 2) :
    fullTriangleFloorCoefficient k *
      ((max (fullTriangleRightZero k u (wideEndpointIntercept a eR k) - (u - k)) 0) ^ 2 +
        (max (fullTriangleRightZero k (v - h) (wideEndpointIntercept a eL k) -
          (v - h - k)) 0) ^ 2) ≤ partialTriangleLoss h k (fullTriangleCos k) := by
  have hk : 0 < k := by linarith only [hk0]
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hR := fullTriangle_floor_loss_le_endpoint hk hksq heR
  have hL := fullTriangle_floor_loss_le_endpoint (u := v - h) hk hksq
    (show eL ≤ 1 - (a - (v - h)) by linarith only [heL])
  rw [fullTriangleFloorCoefficient_eq hk hksq]
  refine (mul_le_mul_of_nonneg_left (add_le_add
    ((sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr hR)
    ((sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr hL)) (by linarith only [hk1])).trans ?_
  exact partialTriangle_floor_loss_le hh (by linarith only [hk1]) (by linarith only [hc.1, hk1])
    (by linarith only [hc.2, hk0]) hwR (by linarith only [hwL]) (by linarith only [hwsum])

theorem IsDownwardCap.threeAngleScore_lt_of_full_triangles_and_endpoint_bounds
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 37 / 25 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hER : 1 / 3 + h / 2 ≤ capRoof U a)
    (hEL : 1 / 3 - 2 * h / 3 ≤ capRoof U (-a)) :
    threeAngleComparisonScore U < 41 / 50 := by
  let k := Real.sqrt 2 - 1
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1 + h
  have ha : 0 < a := by linarith only [ha0]
  have hk : 0 < k := by linarith only [sqrt_two_sub_one_strict_bounds.1]
  have hksq : k ^ 2 + 2 * k = 1 := sqrt_two_sub_one_quadratic
  have hk0 := diagonal_offset_gt_forty_one_ninety_ninths hk hksq
  have hk1 : k < 29 / 70 := sqrt_two_sub_one_strict_bounds.2.2
  have hkunit : k ≤ 1 := by linarith only [hk1]
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hu : diagonalRight U = 1 + u := by ring
  have hv : diagonalLeft U = 1 - h + v := by ring
  have huv : u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a :=
    hU.tilted_diagonal_parameters_mem ha hh0 (by linarith only [ha0, hh1]) hl hr hleft hright
  have hx (x : ℝ) (h1 : -a ≤ x) (h2 : x ≤ a) : x ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨h1, h2⟩
  have heR : capRoof U a ≤ 1 - (a - u) := by
    linarith only [hU.capRoof_le_diagonalRight (hx a (by linarith only [ha]) le_rfl), hu]
  have heL : capRoof U (-a) ≤ 1 - (a - v + h) := by
    linarith only [hU.capRoof_le_diagonalLeft (hx (-a) le_rfl (by linarith only [ha])), hv]
  have hm0 : 179 / 200 ≤ (u + v - h) / 2 := by linarith only [hEP, heR, heL, ha0, hh1]
  have hδR := hU.nearDiagonalRightDeficit_mem ha hk.le hkunit hl hr hright hu
  have hδL := hU.nearDiagonalLeftDeficit_mem ha hh0 hk.le hkunit
    (by linarith only [mul_le_mul_of_nonneg_left ha0 hk.le, hk0, hh1]) hl hr hleft hright haffine
    hv huv.2.1
  have hbR : wideNearRightIntercept U k =
      1 - nearDiagonalNorm k + k * v - h - nearDiagonalLeftDeficit U h k v := by
    rw [wideNearRightIntercept, nearDiagonalLeftDeficit]
    ring
  have hbL := wideNearLeftIntercept_eq U k u
  have hcR := fullTriangle_crossing_after_apex hk0 hk1 hh0 hm0
    (b := wideNearRightIntercept U k) (by linarith only [hbR, hδL.1])
  have hcL := fullTriangle_reflected_crossing_after_apex hk0 hk1 hm0
    (b := wideNearLeftIntercept U k) (by linarith only [hbL, hδR.1])
  have hzR := fullTriangle_outer_zero_le hk hksq heR
  have hzL := fullTriangle_outer_zero_le (u := v - h) hk hksq
    (show capRoof U (-a) ≤ 1 - (a - (v - h)) by linarith only [heL])
  have hN := hU.threeAngle_integral_ge_full_triangles hk hksq rfl hl hr hu
    (show diagonalLeft U = 1 + (v - h) by linarith only [hv])
    (by convert tilted_diagonal_apex_mem ha.le hh0 (by linarith only [ha0, hh1]) huv.1 huv.2
      using 1; ring)
    (by linarith only [hcR]) (by linarith only [hcL]) (by linarith only [hzR, hc.1, ha1])
    (by linarith only [hzL, hc.1, ha1])
  rw [show u + (v - h) = u + v - h by ring, fullTriangleNicheGain,
    fullTriangleNicheFloorLoss] at hN
  have hLoss := fullTriangle_partial_loss_sum_le hk0 hk1 hksq hh0 heR heL
    (by linarith only [heR, hER]) (by linarith only [heL, hEL]) (by linarith only [heR, heL, hEP])
  have hcut := hU.diagonalRoofDeficit_ge_inner_cuts ha hh0 hk hl hr hleft hright hu hv
    huv.1 huv.2 hδR hδL
  have hpay := fullTriangle_square_payment hk hδR.1 hδL.1
    (fullTriangle_gain_sum (a := a) hk hksq hbR hbL hEP)
  have hD := hU.diagonalRoofDeficit_eq h huv.1 huv.2
  have hfin := fullTriangleRelaxation_add_partial_loss_lt (u := u) (v := v) ha0 hh0 hh1 hk0 hk1
    hksq hc.1 hc.2 (by linarith only [hm0, hk1])
  rw [fullTriangleRelaxation, diagonalRelaxation] at hfin
  linarith only [threeAngleComparisonScore_centered hl hr, hD, hN, hpay, hcut, hLoss, hfin]

end AmbidextrousSofa
