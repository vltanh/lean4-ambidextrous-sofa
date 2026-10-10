import AmbidextrousSofa.Analysis.ThreeAngleDeficit
import AmbidextrousSofa.Analysis.PartialTriangleScalar

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
  have hRsq := (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr hR
  have hLsq := (sq_le_sq₀ (le_max_right _ _) (le_max_right _ _)).mpr hL
  have hγ : 0 ≤ (1 - k) / 2 := by linarith only [hk1]
  rw [fullTriangleFloorCoefficient_eq hk hksq]
  apply (mul_le_mul_of_nonneg_left (add_le_add hRsq hLsq) hγ).trans
  apply partialTriangle_floor_loss_le hh (by linarith only [hk1])
    (by linarith only [hc.1, hk1]) (by linarith only [hc.2, hk0]) hwR
  · linarith only [hwL]
  · linarith only [hwsum]

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
  let δR := nearDiagonalRightDeficit U k u
  let δL := nearDiagonalLeftDeficit U h k v
  let bR := wideNearRightIntercept U k
  let bL := wideNearLeftIntercept U k
  let BR := wideEndpointIntercept a (capRoof U a) k
  let BL := wideEndpointIntercept a (capRoof U (-a)) k
  let D := diagonalRoofDeficit U a h u v
  let G := fullTriangleNicheGain U a k u (v - h)
  let L := fullTriangleNicheFloorLoss U a k u (v - h)
  let F := diagonalRelaxation a h k u v
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hk : 0 < k := by dsimp [k]; linarith only [sqrt_two_sub_one_strict_bounds.1]
  have hk0 : 41 / 99 < k := diagonal_offset_gt_forty_one_ninety_ninths hk
    sqrt_two_sub_one_quadratic
  have hk1 : k < 29 / 70 := sqrt_two_sub_one_strict_bounds.2.2
  have hksq : k ^ 2 + 2 * k = 1 := sqrt_two_sub_one_quadratic
  have hkunit : k ≤ 1 := by linarith only [hk1]
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hu : diagonalRight U = 1 + u := by dsimp [u]; ring
  have hv : diagonalLeft U = 1 - h + v := by dsimp [v]; ring
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hhhalf hl hr hleft hright
  change u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a at huv
  have hxR : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith only [ha]
  have hxL : -a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    constructor <;> linarith only [ha]
  have heR : capRoof U a ≤ 1 - (a - u) := by
    linarith only [hU.capRoof_le_diagonalRight hxR, hu]
  have heL : capRoof U (-a) ≤ 1 - (a - v + h) := by
    linarith only [hU.capRoof_le_diagonalLeft hxL, hv]
  have hm : a - 1 / 2 - h / 4 ≤ (u + v - h) / 2 := by
    linarith only [hEP, heR, heL]
  have hm0 : 179 / 200 ≤ (u + v - h) / 2 := by linarith only [hm, ha0, hh1]
  have hq : 0 ≤ (u + v - h) / 2 - k := by linarith only [hm0, hk1]
  have hhk : h ≤ k * a := by
    have hprod := mul_nonneg hk.le (sub_nonneg.mpr ha0)
    nlinarith only [hprod, hk0, hh1]
  have hδR : δR ∈ Icc 0 (k * (u - a / 2)) :=
    hU.nearDiagonalRightDeficit_mem ha hk.le hkunit hl hr hright hu
  have hδL : δL ∈ Icc 0 (k * (v - a / 2)) :=
    hU.nearDiagonalLeftDeficit_mem ha hh0 hk.le hkunit hhk hl hr hleft hright haffine hv huv.2.1
  have hbR : bR = 1 - nearDiagonalNorm k + k * v - h - δL := by
    dsimp [bR, wideNearRightIntercept, δL, nearDiagonalLeftDeficit]
    ring
  have hbL : bL = 1 - nearDiagonalNorm k + k * u - δR := wideNearLeftIntercept_eq U k u
  have hcrossR : (u - (v - h)) / 2 ≤ wideCrossing k u bR := by
    have hc := fullTriangle_crossing_after_apex hk0 hk1 hh0 hm0
      (show bR ≤ 1 - nearDiagonalNorm k + k * v - h by linarith only [hbR, hδL.1])
    linarith only [hc]
  have hcrossL : -(u - (v - h)) / 2 ≤ wideCrossing k (v - h) bL := by
    have hc := fullTriangle_reflected_crossing_after_apex hk0 hk1 hm0
      (show bL ≤ 1 - nearDiagonalNorm k + k * u by linarith only [hbL, hδR.1])
    linarith only [hc]
  have hzeroR : fullTriangleRightZero k u BR ≤ a / 2 := by
    have hz := fullTriangle_outer_zero_le hk hksq heR
    linarith only [hz, ha1, hc.1]
  have hzeroL : fullTriangleRightZero k (v - h) BL ≤ a / 2 := by
    have hz := fullTriangle_outer_zero_le (u := v - h) hk hksq
      (show capRoof U (-a) ≤ 1 - (a - (v - h)) by linarith only [heL])
    linarith only [hz, ha1, hc.1]
  have hLoss : L ≤ partialTriangleLoss h k (fullTriangleCos k) :=
    fullTriangle_partial_loss_sum_le hk0 hk1 hksq hh0 heR heL
      (by linarith only [heR, hER]) (by linarith only [heL, hEL])
      (by linarith only [heR, heL, hEP])
  have hcut : (δR ^ 2 + δL ^ 2) / (2 * k) ≤ D :=
    hU.diagonalRoofDeficit_ge_inner_cuts ha hh0 hk hl hr hleft hright hu hv
      huv.1 huv.2 hδR hδL
  have hgain := fullTriangle_gain_sum hk hksq hbR hbL hEP
  have hpayment : (max (fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k)) 0) ^ 2 /
      (2 + 3 * k) ≤ (δR ^ 2 + δL ^ 2) / (2 * k) + G :=
    fullTriangle_square_payment hk hδR.1 hδL.1 hgain
  have hd : (u - (v - h)) / 2 ∈ Icc (-a / 2) (a / 2) := by
    have h := tilted_diagonal_apex_mem ha.le hh0 hhhalf huv.1 huv.2
    convert h using 1 <;> ring
  have hN := hU.threeAngle_integral_ge_full_triangles hk hksq rfl hl hr hu
    (show diagonalLeft U = 1 + (v - h) by linarith only [hv])
    hd hcrossR hcrossL hzeroR hzeroL
  have hD := hU.diagonalRoofDeficit_eq h huv.1 huv.2
  have hP := threeAngleComparisonScore_centered hl hr
  have hN' : (max ((u + v - h) / 2 - k) 0) ^ 2 -
      (max (u - k - a / 2) 0) ^ 2 / 2 - (max (v - h - k - a / 2) 0) ^ 2 / 2 + G - L ≤
        ∫ x in (-a / 2)..(a / 2), threeAngleBarrier U x := by
    simpa only [show u + (v - h) = u + v - h by ring] using hN
  have hpaid : threeAngleComparisonScore U + D + G - L ≤ F := by
    dsimp [F, diagonalRelaxation]
    change D = _ at hD
    linarith only [hP, hD, hN']
  have hfinal : threeAngleComparisonScore U ≤
      fullTriangleRelaxation a h k (fullTriangleCos k) u v +
        partialTriangleLoss h k (fullTriangleCos k) := by
    unfold fullTriangleRelaxation
    change threeAngleComparisonScore U ≤ F -
      (max (fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k)) 0) ^ 2 / (2 + 3 * k) +
        partialTriangleLoss h k (fullTriangleCos k)
    linarith only [hpaid, hLoss, hpayment, hcut]
  exact hfinal.trans_lt
    (fullTriangleRelaxation_add_partial_loss_lt ha0 hh0 hh1 hk0 hk1 hksq hc.1 hc.2 hq)

end AmbidextrousSofa
