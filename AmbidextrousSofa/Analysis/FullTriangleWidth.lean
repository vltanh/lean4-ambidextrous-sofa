import AmbidextrousSofa.Analysis.FullTriangleArea
import AmbidextrousSofa.Analysis.FullWidthCeiling

/-!
# The actual three-triangle width exclusion

Both nearby support cuts and both full additional niche triangles are
constructed from the original cap. Actual endpoint stationarity pays the
floor losses. The resulting strict score comparison lowers every full
maximizer's quarter-width below thirty-seven fiftieths.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.capScore_lt_of_full_triangles_and_endpoint_laws
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 37 / 25 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h ≤ 17 / 50)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEPR : capRoof U a = 1 / 2 + h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (a / 2) - sweptNiche U (Real.pi / 2) (-a / 2)) / 4)
    (hEPL : capRoof U (-a) = 1 / 2 - 3 * h / 4 +
      (3 * sweptNiche U (Real.pi / 2) (-a / 2) - sweptNiche U (Real.pi / 2) (a / 2)) / 4) :
    capScore U (Real.pi / 2) < 41 / 50 := by
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
  have hbox : U ⊆ Icc (-2 * (a / 2)) (2 * (a / 2)) ×ˢ Icc (0 : ℝ) 1 :=
    hU.subset_centeredBox_of_endpoints (by rw [hl]; ring) (by rw [hr]; ring)
  have hniche := hU.middle_niche_le_two_fifths_of_box hbox
    (show a / 2 ≤ 4 / 5 by linarith only [ha1])
  have hnL : sweptNiche U (Real.pi / 2) (-a / 2) ≤ 2 / 5 := by
    simpa only [neg_div] using hniche.1
  have hwR : a - u ≤ 3 / 5 - h / 4 := by
    linarith only [heR, hEPR, hnL, sweptNiche_nonneg U (Real.pi / 2) (a / 2)]
  have hwL : a - v + h ≤ 3 / 5 + 3 * h / 4 := by
    linarith only [heL, hEPL, hniche.2, sweptNiche_nonneg U (Real.pi / 2) (-a / 2)]
  have hLoss : L ≤ fullTriangleLoss h k (fullTriangleCos k) :=
    fullTriangle_loss_sum_le hk0 hk1 hksq hh0 hh1 heR heL hwR hwL
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
      fullTriangleRelaxation a h k (fullTriangleCos k) u v + fullTriangleLoss h k (fullTriangleCos k) := by
    unfold fullTriangleRelaxation
    change capScore U (Real.pi / 2) ≤ F -
      (max (fullTriangleDemand a ((u + v) / 2) h k (fullTriangleCos k)) 0) ^ 2 / (2 + 3 * k) +
        fullTriangleLoss h k (fullTriangleCos k)
    linarith only [hpaid, hLoss, hpayment, hcut]
  exact hfinal.trans_lt (fullTriangleRelaxation_add_loss_lt ha0 hh0 hh1 hk0 hk1 hksq hc.1 hc.2 hq)

theorem IsFullCapMaximizer.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (37 / 25 : ℝ) := by
  by_contra hbad
  have ha0 : 37 / 25 ≤ a := le_of_not_gt hbad
  have ha1 := hU.centered_half_projection_width_lt_of_affine hl hr hheight haffine
  let h := 1 - capRoof U (-a / 2)
  have hh0 : 0 ≤ h := sub_nonneg.mpr
    (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _)
  have hh1 : h < 17 / 50 := (hU.centered_intermediate_width_tilt hl hr hheight hm haffine).1
  have hleft : capRoof U (-a / 2) = 1 - h := by dsimp [h]; ring
  have hright : capRoof U (a / 2) = 1 := by
    have heq := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rw [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at heq
    exact heq
  have hAff : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m' * x + c' := by
    exact ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
  have hEP := hU.centered_endpoint_laws hheight hl hr hleft hright hAff
  have hscore := hU.isCap.capScore_lt_of_full_triangles_and_endpoint_laws
    ha0 ha1.le hh0 hh1.le hl hr hleft hright hAff hEP.1 hEP.2
  exact (not_lt_of_ge hU.reference_le) (hscore.trans forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (37 / 25 : ℝ) := by
  by_cases hm : 0 ≤ m
  · exact hU.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
      hl hr hheight hm haffine
  · have hV := hU.horizontalMirror
    have hVl : horizontalLeft (horizontalMirror U) = -a := by
      rw [horizontalLeft_horizontalMirror hU.isCap, hr]
    have hVr : horizontalRight (horizontalMirror U) = a := by
      rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg]
    have hVheight : capHeight (horizontalMirror U) = 1 := by
      rw [capHeight_horizontalMirror, hheight]
    have hVaffine : ∀ x ∈ middleHalfInterval
        (horizontalLeft (horizontalMirror U)) (horizontalRight (horizontalMirror U)),
        capRoof (horizontalMirror U) x = (-m) * x + c := by
      intro x hx
      rw [hVl, hVr, middleHalfInterval_centered] at hx
      have hxU : -x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U) := by
        rw [hl, hr, middleHalfInterval_centered]
        constructor <;> linarith only [hx.1, hx.2]
      rw [capRoof_horizontalMirror, haffine (-x) hxU]
      ring
    exact hV.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
      hVl hVr hVheight (by linarith only [le_of_not_ge hm]) hVaffine

theorem IsFullCapMaximizer.quarter_width_lt_thirty_seven_fiftieths
    {U : Set Plane} (hU : IsFullCapMaximizer U) : capWidth U / 4 < (37 / 50 : ℝ) := by
  have hcenter : IsFullCapMaximizer (centeredCap U) :=
    hU.of_score_le hU.isCap.centeredCap (by rw [capScore_centeredCap hU.isCap])
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := hcenter.exists_heightOne_affine_middle
  let a := capWidth U / 2
  have hl : horizontalLeft V = -a := by
    calc
      _ = horizontalLeft (centeredCap U) := by unfold horizontalLeft; rw [hproj]
      _ = _ := by rw [horizontalLeft_centeredCap hU.isCap]; dsimp [a]; ring
  have hr : horizontalRight V = a := by
    calc
      _ = horizontalRight (centeredCap U) := by unfold horizontalRight; rw [hproj]
      _ = _ := horizontalRight_centeredCap hU.isCap
  have h := hV.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine hl hr hheight haffine
  dsimp [a] at h
  linarith only [h]

end AmbidextrousSofa
