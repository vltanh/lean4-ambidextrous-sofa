module

public import AmbidextrousSofa.Analysis.FullTriangleArea
public import AmbidextrousSofa.Analysis.FullWidthCeiling

@[expose] public section

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

/-- `41/50 < M/2`; the same statement and proof as `forty_one_fiftieths_lt_half_M` of
`TerminalScalar`, which this module does not import. -/
private theorem fullTriangleWidth_forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 := by
  have hY : (19 / 64 : ℝ) < Y := cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])
  unfold M beta
  linarith [Y_equation, self_sub_cube_div_three_le_arctan Y_pos.le,
    mul_pos (sub_pos.mpr hY) (show 0 < Y + 19 / 64 by linarith [Y_pos])]

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
  obtain ⟨hnL, hnR⟩ := hU.middle_niche_le_two_fifths_of_box
    (hU.subset_centeredBox_of_endpoints (C := a / 2) (by rw [hl]; ring) (by rw [hr]; ring))
    (by linarith only [ha1])
  rw [← neg_div] at hnL
  have hn0 := sweptNiche_nonneg U (Real.pi / 2) (a / 2)
  have hn1 := sweptNiche_nonneg U (Real.pi / 2) (-a / 2)
  have hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a) := by
    linarith only [hEPR, hEPL, hn0, hn1]
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
  have hN := hU.niche_integral_ge_full_triangles hk hkunit hksq rfl hl hr hu
    (show diagonalLeft U = 1 + (v - h) by linarith only [hv])
    (sub_le_self _ (Real.arctan_pos.mpr hk).le) le_rfl
    (by convert tilted_diagonal_apex_mem ha.le hh0 (by linarith only [ha0, hh1]) huv.1 huv.2
      using 1; ring)
    (by linarith only [hcR]) (by linarith only [hcL]) (by linarith only [hzR, hc.1, ha1])
    (by linarith only [hzL, hc.1, ha1])
  rw [show u + (v - h) = u + v - h by ring, fullTriangleNicheGain,
    fullTriangleNicheFloorLoss] at hN
  have hLoss := fullTriangle_loss_sum_le hk0 hk1 hksq hh0 hh1 heR heL
    (by linarith only [heR, hEPR, hnL, hn0]) (by linarith only [heL, hEPL, hnR, hn1])
  have hcut := hU.diagonalRoofDeficit_ge_inner_cuts ha hh0 hk hl hr hleft hright hu hv
    huv.1 huv.2 hδR hδL
  have hpay := fullTriangle_square_payment hk hδR.1 hδL.1
    (fullTriangle_gain_sum (a := a) hk hksq hbR hbL hEP)
  have hD := hU.diagonalRoofDeficit_eq h huv.1 huv.2
  have hP : capScore U (Real.pi / 2) =
      ((∫ x in (-a)..(-a / 2), capRoof U x) + ∫ x in (a / 2)..a, capRoof U x) -
        ∫ x in (-a / 2)..(a / 2), partialBarrier U (Real.pi / 2) x := by
    rw [hU.capScore_eq_intervalSpatialScore, hl, hr, intervalSpatialScore,
      show -a + (a - -a) / 4 = -a / 2 by ring, show a - (a - -a) / 4 = a / 2 by ring]
  have hfin := fullTriangleRelaxation_add_loss_lt (u := u) (v := v) ha0 hh0 hh1 hk0 hk1 hksq
    hc.1 hc.2 (by linarith only [hm0, hk1])
  rw [fullTriangleRelaxation, diagonalRelaxation] at hfin
  linarith only [hP, hD, hN, hpay, hcut, hLoss, hfin]

theorem IsFullCapMaximizer.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1) (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (37 / 25 : ℝ) := by
  by_contra! ha0
  have hright : capRoof U (a / 2) = 1 := by
    have h := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rwa [hl, hr, show a - (a - -a) / 4 = a / 2 by ring] at h
  have hleft := (sub_sub_cancel 1 (capRoof U (-a / 2))).symm
  have hAff : ∃ m' c' : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m' * x + c' :=
    ⟨m, c, by simpa only [hl, hr, middleHalfInterval_centered] using haffine⟩
  have hEP := hU.centered_endpoint_laws hheight hl hr hleft hright hAff
  have hscore := hU.isCap.capScore_lt_of_full_triangles_and_endpoint_laws ha0
    (hU.centered_half_projection_width_lt_of_affine hl hr hheight haffine).le
    (sub_nonneg.mpr (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _))
    (hU.centered_intermediate_width_tilt hl hr hheight hm haffine).1.le
    hl hr hleft hright hAff hEP.1 hEP.2
  exact (not_lt_of_ge hU.reference_le)
    (hscore.trans fullTriangleWidth_forty_one_fiftieths_lt_half_M)

theorem IsFullCapMaximizer.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a m c : ℝ}
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) : a < (37 / 25 : ℝ) := by
  by_cases hm : 0 ≤ m
  · exact hU.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
      hl hr hheight hm haffine
  have hVl : horizontalLeft (AmbidextrousSofa.horizontalMirror U) = -a := by
    rw [horizontalLeft_horizontalMirror hU.isCap, hr]
  have hVr : horizontalRight (AmbidextrousSofa.horizontalMirror U) = a := by
    rw [horizontalRight_horizontalMirror hU.isCap, hl, neg_neg]
  refine hU.horizontalMirror.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine_nonneg
    hVl hVr (by rw [capHeight_horizontalMirror, hheight]) (m := -m) (c := c) (by linarith)
    fun x hx => ?_
  rw [hVl, hVr, middleHalfInterval_centered] at hx
  rw [capRoof_horizontalMirror, haffine (-x) (by
    rw [hl, hr, middleHalfInterval_centered]
    constructor <;> linarith [hx.1, hx.2])]
  ring

theorem IsFullCapMaximizer.quarter_width_lt_thirty_seven_fiftieths
    {U : Set Plane} (hU : IsFullCapMaximizer U) : capWidth U / 4 < (37 / 50 : ℝ) := by
  obtain ⟨V, hV, hproj, hheight, _, m, c, haffine⟩ := (hU.of_score_le hU.isCap.centeredCap
    (capScore_centeredCap hU.isCap _).ge).exists_heightOne_affine_middle
  have := hV.centered_half_width_lt_thirty_seven_twenty_fifths_of_affine
    ((congrArg sInf hproj).trans ((horizontalLeft_centeredCap hU.isCap).trans (neg_div _ _)))
    ((congrArg sSup hproj).trans (horizontalRight_centeredCap hU.isCap)) hheight haffine
  linarith

end AmbidextrousSofa
