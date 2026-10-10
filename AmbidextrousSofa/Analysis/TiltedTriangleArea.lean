import AmbidextrousSofa.Analysis.TiltedTriangleScalar
import AmbidextrousSofa.Analysis.FullTriangleArea
import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
import AmbidextrousSofa.Analysis.WideWidthExclusion

/-!
# Actual triangle exclusion with a dry low middle endpoint

The supports, exterior cuts, full niche gains, and floor losses all
belong to the original cap. The actual zero left niche sharpens only
the floor payment, and the joint support comparison applies to every
clipping case. No scalar upper bound on the score is a premise.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem tiltedTriangle_loss_sum_le {a eR eL h k u v : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 21 / 100)
    (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - v + h))
    (hwR : a - u ≤ 1 / 2 - h / 4) (hwL : a - v + h ≤ 7 / 12 + 3 * h / 4) :
    fullTriangleFloorCoefficient k *
      ((max (fullTriangleRightZero k u (wideEndpointIntercept a eR k) - (u - k)) 0) ^ 2 +
        (max (fullTriangleRightZero k (v - h) (wideEndpointIntercept a eL k) -
          (v - h - k)) 0) ^ 2) ≤ tiltedTriangleLoss h k (fullTriangleCos k) := by
  have hk : 0 < k := by linarith only [hk0]
  let D := 1 / 2 - (2 * fullTriangleCos k - (1 + k))
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hD : 21 / 400 < D := by dsimp [D]; linarith only [hk0, hc.2]
  have hDR : 0 ≤ D - h / 4 := by linarith only [hD, hh1]
  have hDL : 0 ≤ D + 1 / 12 + 3 * h / 4 := by linarith only [hD, hh0]
  have hR := fullTriangle_floor_loss_le_endpoint hk hksq heR
  have hL := fullTriangle_floor_loss_le_endpoint (u := v - h) hk hksq
    (by linarith only [heL])
  have hR' : max (fullTriangleRightZero k u (wideEndpointIntercept a eR k) - (u - k)) 0 ≤
      D - h / 4 := hR.trans (max_le (by dsimp [D]; linarith only [hwR]) hDR)
  have hL' : max (fullTriangleRightZero k (v - h) (wideEndpointIntercept a eL k) -
      (v - h - k)) 0 ≤ D + 1 / 12 + 3 * h / 4 :=
    hL.trans (max_le (by dsimp [D]; linarith only [hwL]) hDL)
  have hRsq := (sq_le_sq₀ (le_max_right _ _) hDR).mpr hR'
  have hLsq := (sq_le_sq₀ (le_max_right _ _) hDL).mpr hL'
  rw [fullTriangleFloorCoefficient_eq hk hksq]
  exact mul_le_mul_of_nonneg_left (add_le_add hRsq hLsq)
    (by linarith only [hk1] : 0 ≤ (1 - k) / 2)

theorem IsDownwardCap.capScore_lt_of_tilted_triangles_and_zero_left_niche
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 73 / 50 ≤ a) (ha1 : a ≤ 37 / 25) (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEPR : capRoof U a = 1 / 2 + h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (a / 2) - sweptNiche U (Real.pi / 2) (-a / 2)) / 4)
    (hEPL : capRoof U (-a) = 1 / 2 - 3 * h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (-a / 2) - sweptNiche U (Real.pi / 2) (a / 2)) / 4)
    (hnzero : sweptNiche U (Real.pi / 2) (-a / 2) = 0) :
    capScore U (Real.pi / 2) < 41 / 50 := by
  have hhnonneg : 0 ≤ h := by linarith only [hh0]
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
  have huv := hU.tilted_diagonal_parameters_mem ha hhnonneg hhhalf hl hr hleft hright
  change u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a at huv
  have hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a) := by
    linarith only [hEPR, hEPL, sweptNiche_nonneg U (Real.pi / 2) (a / 2),
      sweptNiche_nonneg U (Real.pi / 2) (-a / 2)]
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
    hU.nearDiagonalLeftDeficit_mem ha hhnonneg hk.le hkunit hhk hl hr hleft hright haffine hv huv.2.1
  have hbR : bR = 1 - nearDiagonalNorm k + k * v - h - δL := by
    dsimp [bR, wideNearRightIntercept, δL, nearDiagonalLeftDeficit]
    ring
  have hbL : bL = 1 - nearDiagonalNorm k + k * u - δR := wideNearLeftIntercept_eq U k u
  have hcrossR : (u - (v - h)) / 2 ≤ wideCrossing k u bR := by
    have hc := fullTriangle_crossing_after_apex hk0 hk1 hhnonneg hm0
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
  have hbox : U ⊆ Icc (-2 * (a / 2)) (2 * (a / 2)) ×ˢ Icc (0 : ℝ) 1 :=
    hU.subset_centeredBox_of_endpoints (by rw [hl]; ring) (by rw [hr]; ring)
  have hniche := hU.middle_niche_le_box_height_of_box hbox
    (show 0 ≤ a / 2 by linarith only [ha0]) (show a / 2 ≤ 1 by linarith only [ha1])
  have hH := Analysis.tiltedBoxHeight_lt_thirty_three_hundredths
    (show 0 ≤ a / 2 by linarith only [ha0]) (show a / 2 ≤ 37 / 50 by linarith only [ha1])
  unfold Analysis.tiltedBoxHeight at hH
  have hnR : sweptNiche U (Real.pi / 2) (a / 2) ≤ 1 / 3 := by
    linarith only [hniche.2, hH]
  have hwR : a - u ≤ 1 / 2 - h / 4 := by
    linarith only [heR, hEPR, hnzero, sweptNiche_nonneg U (Real.pi / 2) (a / 2)]
  have hwL : a - v + h ≤ 7 / 12 + 3 * h / 4 := by
    linarith only [heL, hEPL, hnzero, hnR]
  have hLoss : L ≤ tiltedTriangleLoss h k (fullTriangleCos k) :=
    tiltedTriangle_loss_sum_le hk0 hk1 hksq hhnonneg hh1 heR heL hwR hwL
  have hcut : (δR ^ 2 + δL ^ 2) / (2 * k) ≤ D :=
    hU.diagonalRoofDeficit_ge_inner_cuts ha hhnonneg hk hl hr hleft hright hu hv
      huv.1 huv.2 hδR hδL
  have hgain := fullTriangle_gain_sum hk hksq hbR hbL hEP
  have hpayment : (max (fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k)) 0) ^ 2 /
      (2 + 3 * k) ≤ (δR ^ 2 + δL ^ 2) / (2 * k) + G :=
    fullTriangle_square_payment hk hδR.1 hδL.1 hgain
  have hd : (u - (v - h)) / 2 ∈ Icc (-a / 2) (a / 2) := by
    have h := tilted_diagonal_apex_mem ha.le hhnonneg hhhalf huv.1 huv.2
    convert h using 1 <;> ring
  have hα : Real.pi / 2 - Real.arctan k ≤ Real.pi / 2 :=
    sub_le_self _ (Real.arctan_pos.mpr hk).le
  have hN := hU.niche_integral_ge_full_triangles hk hkunit hksq rfl hl hr hu
    (show diagonalLeft U = 1 + (v - h) by linarith only [hv])
    hα le_rfl hd hcrossR hcrossL hzeroR hzeroL
  have hD := hU.diagonalRoofDeficit_eq h huv.1 huv.2
  have hP : capScore U (Real.pi / 2) =
      ((∫ x in (-a)..(-a / 2), capRoof U x) + ∫ x in (a / 2)..a, capRoof U x) -
        ∫ x in (-a / 2)..(a / 2), partialBarrier U (Real.pi / 2) x := by
    rw [hU.capScore_eq_intervalSpatialScore, hl, hr, intervalSpatialScore,
      show -a + (a - -a) / 4 = -a / 2 by ring,
      show a - (a - -a) / 4 = a / 2 by ring]
  have hN' : (max ((u + v - h) / 2 - k) 0) ^ 2 -
      (max (u - k - a / 2) 0) ^ 2 / 2 - (max (v - h - k - a / 2) 0) ^ 2 / 2 + G - L ≤
        ∫ x in (-a / 2)..(a / 2), partialBarrier U (Real.pi / 2) x := by
    simpa only [show u + (v - h) = u + v - h by ring] using hN
  have hpaid : capScore U (Real.pi / 2) + D + G - L ≤ F := by
    dsimp [F, diagonalRelaxation]
    change D = _ at hD
    linarith only [hP, hD, hN']
  have hfinal : capScore U (Real.pi / 2) ≤
      fullTriangleRelaxation a h k (fullTriangleCos k) u v + tiltedTriangleLoss h k (fullTriangleCos k) := by
    unfold fullTriangleRelaxation
    change capScore U (Real.pi / 2) ≤ F -
      (max (fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k)) 0) ^ 2 / (2 + 3 * k) +
        tiltedTriangleLoss h k (fullTriangleCos k)
    linarith only [hpaid, hLoss, hpayment, hcut]
  exact hfinal.trans_lt (tiltedTriangleRelaxation_add_loss_lt ha0 hh0 hh1 hk0 hk1 hksq hc.1 hc.2 hq)

theorem IsFullCapMaximizer.false_of_medium_tilt_large_width_zero_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a h : ℝ}
    (ha0 : 73 / 50 ≤ a) (ha1 : a ≤ 37 / 25) (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hnzero : sweptNiche U (Real.pi / 2) (-a / 2) = 0) : False := by
  have hEP := hU.centered_endpoint_laws hheight hl hr hleft hright haffine
  have hscore := hU.isCap.capScore_lt_of_tilted_triangles_and_zero_left_niche
    ha0 ha1 hh0 hh1 hl hr hleft hright haffine hEP.1 hEP.2 hnzero
  exact (not_lt_of_ge hU.reference_le) (hscore.trans forty_one_fiftieths_lt_half_M)

end AmbidextrousSofa
