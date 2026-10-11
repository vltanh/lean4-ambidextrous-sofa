module

public import AmbidextrousSofa.Analysis.TiltedTriangleScalar
public import AmbidextrousSofa.Analysis.FullTriangleArea
public import AmbidextrousSofa.Analysis.HorizontalEndpointBounds
public import AmbidextrousSofa.Analysis.TiltedInitialEnergyBounds
public import AmbidextrousSofa.Analysis.WideWidthExclusion

@[expose] public section

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

theorem tiltedTriangle_loss_sum_le {a eR eL h k u w : ℝ}
    (hk0 : 41 / 99 < k) (hk1 : k < 29 / 70) (hksq : k ^ 2 + 2 * k = 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 21 / 100) (heR : eR ≤ 1 - (a - u)) (heL : eL ≤ 1 - (a - w))
    (hwR : a - u ≤ 1 / 2 - h / 4) (hwL : a - w ≤ 7 / 12 + 3 * h / 4) :
    fullTriangleFloorCoefficient k *
      ((max (fullTriangleRightZero k u (wideEndpointIntercept a eR k) - (u - k)) 0) ^ 2 +
        (max (fullTriangleRightZero k w (wideEndpointIntercept a eL k) - (w - k)) 0) ^ 2) ≤
      tiltedTriangleLoss h k (fullTriangleCos k) := by
  have hk : 0 < k := by linarith only [hk0]
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  rw [fullTriangleFloorCoefficient_eq hk hksq, tiltedTriangleLoss]
  refine mul_le_mul_of_nonneg_left (add_le_add
    (pow_le_pow_left₀ (le_max_right _ _) ((fullTriangle_floor_loss_le_endpoint hk hksq heR).trans
      (max_le (by linarith only [hwR]) (by linarith only [hk0, hc.2, hh1]))) 2)
    (pow_le_pow_left₀ (le_max_right _ _) ((fullTriangle_floor_loss_le_endpoint hk hksq heL).trans
      (max_le (by linarith only [hwL]) (by linarith only [hk0, hc.2, hh0]))) 2))
    (by linarith only [hk1])

/-- `41/50 < M/2`, as `forty_one_fiftieths_lt_half_M` of `TerminalScalar`, which this module
does not import. -/
private theorem tiltedTriangleArea_forty_one_fiftieths_lt_half_M : (41 / 50 : ℝ) < M / 2 := by
  have hY : (19 / 64 : ℝ) < Y := cubic_strictMono.lt_iff_lt.mp (by rw [Y_cubic]; norm_num [cubic])
  unfold M beta
  nlinarith [Y_equation, self_sub_cube_div_three_le_arctan Y_pos.le,
    mul_pos (sub_pos.mpr hY) (show 0 < Y + 19 / 64 by linarith [Y_pos])]

theorem IsFullCapMaximizer.false_of_medium_tilt_large_width_zero_left
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a h : ℝ}
    (ha0 : 73 / 50 ≤ a) (ha1 : a ≤ 37 / 25) (hh0 : 1 / 20 ≤ h) (hh1 : h ≤ 21 / 100)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hheight : capHeight U = 1)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hnzero : sweptNiche U (Real.pi / 2) (-a / 2) = 0) : False := by
  obtain ⟨hEPR, hEPL⟩ := hU.centered_endpoint_laws hheight hl hr hleft hright haffine
  have hC := hU.isCap
  have ha : 0 < a := by linarith only [ha0]
  have hh : 0 ≤ h := by linarith only [hh0]
  let k := Real.sqrt 2 - 1
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1 + h
  have hk : 0 < k := by linarith only [sqrt_two_sub_one_strict_bounds.1]
  have hk1 : k < 29 / 70 := sqrt_two_sub_one_strict_bounds.2.2
  have hksq : k ^ 2 + 2 * k = 1 := sqrt_two_sub_one_quadratic
  have hk0 := diagonal_offset_gt_forty_one_ninety_ninths hk hksq
  have hkunit : k ≤ 1 := by linarith only [hk1]
  have hc := fullTriangleCos_bounds hk0 hk1 hksq
  have hu : diagonalRight U = 1 + u := by dsimp only [u]; ring
  have hv : diagonalLeft U = 1 - h + v := by dsimp only [v]; ring
  have huv : u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a :=
    hC.tilted_diagonal_parameters_mem ha hh (by linarith only [ha0, hh1]) hl hr hleft hright
  have hproj : Icc (-a) a ⊆ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hC.nonempty hC.isCompact hC.convex, hl, hr]
  have heR : capRoof U a ≤ 1 - (a - u) := by
    linarith only [hC.capRoof_le_diagonalRight (hproj ⟨by linarith only [ha], le_rfl⟩), hu]
  have heL : capRoof U (-a) ≤ 1 - (a - (v - h)) := by
    linarith only [hC.capRoof_le_diagonalLeft (hproj ⟨le_rfl, by linarith only [ha]⟩), hv]
  have hn := sweptNiche_nonneg U (Real.pi / 2) (a / 2)
  have hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a) := by
    linarith only [hEPR, hEPL, hn, hnzero]
  have hm0 : 179 / 200 ≤ (u + v - h) / 2 := by linarith only [hEP, heR, heL, ha0, hh1]
  have hδR := hC.nearDiagonalRightDeficit_mem ha hk.le hkunit hl hr hright hu
  have hδL := hC.nearDiagonalLeftDeficit_mem ha hh hk.le hkunit
    (by linarith only [mul_le_mul_of_nonneg_left ha0 hk.le, hk0, hh1]) hl hr hleft hright haffine
    hv huv.2.1
  have hbR : wideNearRightIntercept U k =
      1 - nearDiagonalNorm k + k * v - h - nearDiagonalLeftDeficit U h k v := by
    rw [wideNearRightIntercept, nearDiagonalLeftDeficit]; ring
  have hbL := wideNearLeftIntercept_eq U k u
  have hcrossR := fullTriangle_crossing_after_apex (b := wideNearRightIntercept U k) hk0 hk1 hh hm0
    (by linarith only [hbR, hδL.1])
  have hcrossL := fullTriangle_reflected_crossing_after_apex (b := wideNearLeftIntercept U k) hk0
    hk1 hm0 (by linarith only [hbL, hδR.1])
  have hcos : 1 + a - 2 * fullTriangleCos k ≤ a / 2 := by linarith only [ha1, hc.1]
  have hnR : sweptNiche U (Real.pi / 2) (a / 2) ≤ 1 / 3 := by
    have hH : 1 - Real.sqrt (1 - (a / 2) ^ 2) < 33 / 100 :=
      Analysis.tiltedBoxHeight_lt_thirty_three_hundredths (by linarith only [ha0])
        (by linarith only [ha1])
    have := hC.middle_niche_le_box_height_of_box
      (hC.subset_centeredBox_of_endpoints (by rw [hl]; ring) (by rw [hr]; ring))
      (by linarith only [ha0]) (by linarith only [ha1] : a / 2 ≤ 1)
    linarith only [this.2, hH]
  have hLoss : fullTriangleNicheFloorLoss U a k u (v - h) ≤
      tiltedTriangleLoss h k (fullTriangleCos k) :=
    tiltedTriangle_loss_sum_le hk0 hk1 hksq hh hh1 heR heL
      (by linarith only [heR, hEPR, hnzero, hn]) (by linarith only [heL, hEPL, hnzero, hnR])
  have hcut := hC.diagonalRoofDeficit_ge_inner_cuts ha hh hk hl hr hleft hright hu hv huv.1 huv.2
    hδR hδL
  have hpay := fullTriangle_square_payment hk hδR.1 hδL.1
    (fullTriangle_gain_sum (a := a) hk hksq hbR hbL hEP)
  have hN := hC.niche_integral_ge_full_triangles hk hkunit hksq rfl hl hr hu
    (by linarith only [hv] : diagonalLeft U = 1 + (v - h))
    (sub_le_self _ (Real.arctan_pos.mpr hk).le) le_rfl
    (by constructor <;> linarith only [huv.1.1, huv.1.2, huv.2.1, huv.2.2, ha0, hh, hh1])
    (by linarith only [hcrossR]) (by linarith only [hcrossL])
    ((fullTriangle_outer_zero_le hk hksq heR).trans hcos)
    ((fullTriangle_outer_zero_le hk hksq heL).trans hcos)
  rw [show u + (v - h) = u + v - h by ring, fullTriangleNicheGain] at hN
  have hfin := tiltedTriangleRelaxation_add_loss_lt ha0 hh0 hh1 hk0 hk1 hksq hc.1 hc.2
    (by linarith only [hm0, hk1] : 0 ≤ (u + v - h) / 2 - k)
  rw [fullTriangleRelaxation, diagonalRelaxation] at hfin
  have hP := hC.capScore_eq_intervalSpatialScore (Real.pi / 2)
  rw [hl, hr, intervalSpatialScore, show -a + (a - -a) / 4 = -a / 2 by ring,
    show a - (a - -a) / 4 = a / 2 by ring] at hP
  linarith only [hU.reference_le, tiltedTriangleArea_forty_one_fiftieths_lt_half_M, hP, hN, hpay,
    hcut, hLoss, hfin, hC.diagonalRoofDeficit_eq h huv.1 huv.2]

end AmbidextrousSofa
