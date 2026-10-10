module

public import AmbidextrousSofa.Analysis.ThreeAngleNiche

@[expose] public section

/-!
# Diagonal geometry of the literal three-angle objective

The unchanged actual roof deficits subtract from this finite objective.
Its diagonal member alone supplies the short-width stability estimates,
the wide high-score box, and the intermediate tilt bound. These are
comparisons for every cap in the stated geometric form, so they also
apply to the cap used only for comparative reflection.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.threeAngle_diagonal_integral_le {U : Set Plane}
    (hU : IsDownwardCap U) {a h k u v : ℝ} (hk : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2)) :
    (max ((u + v - h) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - h - k - a / 2) 0) ^ 2 / 2 ≤
        ∫ x in (-a / 2)..(a / 2), threeAngleBarrier U x := by
  rw [← integral_tilted_diagonal_tent k hd]
  apply intervalIntegral.integral_mono_on (hd.1.trans hd.2)
    ((show Continuous (fun x : ℝ => max (min (u - k - x) (v - h - k + x)) 0)
      by fun_prop).intervalIntegrable _ _)
    ((continuous_threeAngleBarrier U).intervalIntegrable _ _)
  exact fun x _ => hU.threeAngle_diagonal_floor hk hu hv x

theorem IsDownwardCap.threeAngleScore_add_diagonalRoofDeficit_le {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    threeAngleComparisonScore U +
        diagonalRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1 + h) ≤
      diagonalRelaxation a h (Real.sqrt 2 - 1)
        (diagonalRight U - 1) (diagonalLeft U - 1 + h) := by
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hh1 hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_eq h huv.1 huv.2
  have hN := hU.threeAngle_diagonal_integral_le rfl
    (show diagonalRight U = 1 + (diagonalRight U - 1) by ring)
    (show diagonalLeft U = 1 - h + (diagonalLeft U - 1 + h) by ring)
    (tilted_diagonal_apex_mem ha.le hh0 hh1 huv.1 huv.2)
  rw [threeAngleComparisonScore_centered hl hr]
  unfold diagonalRelaxation
  linarith only [hD, hN]

theorem IsDownwardCap.threeAngleScore_le_tilted_charged_rectangle {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    threeAngleComparisonScore U ≤ a * (1 - h / 2) := by
  have hL := intervalIntegral.integral_mono_on (by linarith only [ha] : -a ≤ -a / 2)
    (hU.intervalIntegrable_capRoof _ _) (continuous_const.intervalIntegrable _ _)
    (hU.left_roof_le_middle_height ha hh hl hr hleft hright)
  have hR := intervalIntegral.integral_mono_on (by linarith only [ha] : a / 2 ≤ a)
    (hU.intervalIntegrable_capRoof _ _) (continuous_const.intervalIntegrable _ _)
    (fun x (_ : x ∈ Icc (a / 2) a) => capRoof_le_one hU.isCompact hU.inStrip x)
  have hN := intervalIntegral.integral_nonneg_of_forall
    (by linarith only [ha] : -a / 2 ≤ a / 2) (threeAngleBarrier_nonneg U)
  rw [intervalIntegral.integral_const] at hL hR
  simp only [smul_eq_mul] at hL hR
  rw [threeAngleComparisonScore_centered hl hr]
  nlinarith only [hL, hR, hN]

theorem IsDownwardCap.threeAngle_short_diagonal_geometry {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (ha1 : a ≤ 1001 / 1000)
    (hh : 0 ≤ h) (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hscore : 41 / 50 ≤ threeAngleComparisonScore U) :
    let u := diagonalRight U - 1
    let v := diagonalLeft U - 1 + h
    let k := Real.sqrt 2 - 1
    9 / 10 < a ∧ h < 1 / 23 ∧
      u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a ∧
      u - a / 2 < 323 / 1000 + h / 4 ∧ v - a / 2 < 323 / 1000 + h / 4 ∧
      16 / 25 < (u + v) / 2 - h / 4 ∧ 0 < (u + v - h) / 2 - k ∧
      u - k - a / 2 < 0 ∧ v - h - k - a / 2 < 0 ∧
      23 / 200 < a - u ∧ 23 / 200 < a - v ∧
      0 ≤ diagonalRoofDeficit U a h u v ∧ diagonalRoofDeficit U a h u v < 9 / 1000 := by
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1 + h
  let k := Real.sqrt 2 - 1
  have hrect := hU.threeAngleScore_le_tilted_charged_rectangle ha hh hl hr hleft hright
  have ha0 : 41 / 50 ≤ a := by nlinarith [mul_nonneg ha.le hh]
  have hh37 : h ≤ 37 / 100 := by
    by_contra hbad
    have hprod := mul_nonneg ha.le (sub_nonneg.mpr (le_of_not_ge hbad))
    nlinarith
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh37]
  have huv := hU.tilted_diagonal_parameters_mem ha hh hhhalf hl hr hleft hright
  have hbound := hU.threeAngleScore_add_diagonalRoofDeficit_le ha hh hhhalf hl hr hleft hright
  have hD0 := hU.diagonalRoofDeficit_nonneg ha hh hl hr hleft hright
  have hk := sqrt_two_sub_one_strict_bounds
  have hksq := sqrt_two_sub_one_quadratic
  obtain ⟨ha9, hh23, hu323, hv323, hm, hq, hclipR, hclipL⟩ :=
    short_diagonal_stability ha0 ha1 hh hh37 hk.1 hk.2.1 hk.2.2 hksq
      huv.1 huv.2 (by linarith : 41 / 50 ≤ diagonalRelaxation a h k u v)
  have hcritical := diagonalRelaxation_le_critical a h k u v
    (by dsimp [k]; linarith [hk.2.1]) (by dsimp [k]; linarith [hk.1])
    (by dsimp [k]; linarith [hk.1])
  have hwidth := diagonal_critical_width_mono ha1
    (by dsimp [k]; linarith [hk.1] : (1001 / 1000 : ℝ) ≤ 1 + k)
  have hD1 : diagonalRoofDeficit U a h u v < 9 / 1000 := by
    have hkh : 0 ≤ k * h := mul_nonneg (by dsimp [k]; linarith [hk.1]) hh
    dsimp [k] at hcritical hwidth hkh
    dsimp [u, v] at hcritical ⊢
    nlinarith [sq_nonneg h]
  exact ⟨ha9, hh23, huv.1, huv.2, hu323, hv323, hm, hq, hclipR, hclipL,
    by linarith, by linarith, hD0, hD1⟩

theorem IsDownwardCap.threeAngleScore_add_wideRoofDeficit_le {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hm : Real.sqrt 2 - 1 ≤ ((diagonalRight U - 1) + (diagonalLeft U - 1)) / 2) :
    threeAngleComparisonScore U + wideRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1) ≤
      wideDiagonalMajorant a h (Real.sqrt 2 - 1) (diagonalRight U - 1) (diagonalLeft U - 1) := by
  have hp := hU.wide_diagonal_parameters ha hh hh1 hl hr hleft hright haffine
  have hD := hU.wideRoofDeficit_eq ha (by linarith only [ha, hh1]) hp.1 hp.2.1
  have huv := hU.tilted_diagonal_parameters_mem ha hh hh1 hl hr hleft hright
  have hN := hU.threeAngle_diagonal_integral_le rfl
    (show diagonalRight U = 1 + (diagonalRight U - 1) by ring)
    (show diagonalLeft U = 1 - h + (diagonalLeft U - 1 + h) by ring)
    (tilted_diagonal_apex_mem ha.le hh hh1 huv.1 huv.2)
  rw [show ((diagonalRight U - 1) + (diagonalLeft U - 1 + h) - h) / 2 -
      (Real.sqrt 2 - 1) = ((diagonalRight U - 1) + (diagonalLeft U - 1)) / 2 -
      (Real.sqrt 2 - 1) by ring,
    max_eq_left (sub_nonneg.mpr hm)] at hN
  rw [threeAngleComparisonScore_centered hl hr]
  unfold wideExteriorMajorant at hD
  unfold wideDiagonalMajorant
  have htail : diagonalLeft U - 1 + h - h - (Real.sqrt 2 - 1) - a / 2 =
      diagonalLeft U - 1 - (Real.sqrt 2 - 1) - a / 2 := by ring
  rw [htail] at hN
  linarith only [hD, hN]

theorem IsDownwardCap.threeAngle_wide_high_score_box {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha0 : 8 / 5 ≤ a) (ha1 : a < 3)
    (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hscore : 41 / 50 ≤ threeAngleComparisonScore U) :
    a < 9 / 5 ∧ h < 1 / 4 ∧ a + h < 37 / 20 := by
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hm := hU.wide_diagonal_midpoint_ge ha hh hhhalf hl hr hleft hright haffine hEP
  have hbound := hU.threeAngleScore_add_wideRoofDeficit_le ha hh hhhalf hl hr hleft hright haffine
    (by linarith only [hm, ha0, hh1, sqrt_two_sub_one_strict_bounds.2.2])
  have hdef := hU.wideRoofDeficit_nonneg ha hl hr hleft hright haffine
  exact wide_diagonal_high_score_box ha0 ha1 hh hh1 sqrt_two_sub_one_strict_bounds.1
    sqrt_two_sub_one_strict_bounds.2.2 sqrt_two_sub_one_quadratic hm (by linarith only [hscore, hbound, hdef])

theorem IsDownwardCap.threeAngleScore_le_tiltedDiagonalBound {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ}
    (ha : 1 ≤ a) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    threeAngleComparisonScore U ≤ tiltedDiagonalBound a h (Real.sqrt 2 - 1) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hhhalf : h ≤ a / 2 := by linarith only [ha, hh1]
  have hha : h < a := by linarith only [ha, hh1]
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1 + h
  have huv := hU.tilted_diagonal_parameters_mem ha0 hh0 hhhalf hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_ge_tilt_loss ha0 hha hl hr hleft hright haffine
    (show diagonalRight U = 1 + u by dsimp [u]; ring)
    (show diagonalLeft U = 1 - h + v by dsimp [v]; ring) huv.1 huv.2
  have hP := hU.threeAngleScore_add_diagonalRoofDeficit_le ha0 hh0 hhhalf hl hr hleft hright
  have hscalar := tiltedDiagonalRelaxation_le_bound ha hh0 hh1
    sqrt_two_sub_one_strict_bounds.1 sqrt_two_sub_one_strict_bounds.2.1 u v
  unfold tiltedDiagonalRelaxation at hscalar
  linarith only [hD, hP, hscalar]

theorem IsDownwardCap.threeAngle_intermediate_width_tilt_bound {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hscore : 41 / 50 ≤ threeAngleComparisonScore U) :
    h < 17 / 50 ∧ (a - Real.sqrt 2) ^ 2 +
      (4 * a / (4 * a - h)) * (Real.sqrt 2 - 1 + h / 2) ^ 2 ≤ 9 / 25 := by
  have hP := hU.threeAngleScore_le_tiltedDiagonalBound ha0 hh0 hh1 hl hr hleft hright haffine
  have h4 : 0 < 4 * a - h := by linarith only [ha0, hh1]
  have hksq := sqrt_two_sub_one_quadratic
  have htilt : h < 17 / 50 := by
    by_contra h
    exact (not_lt_of_ge hscore) (hP.trans_lt
      (tiltedDiagonalBound_lt_of_large_tilt ha0 ha1 (le_of_not_gt h) hh1
        (by linarith only [sqrt_two_sub_one_strict_bounds.1]) hksq))
  refine ⟨htilt, ?_⟩
  rw [tiltedDiagonalBound_eq_width_tilt h4.ne' hksq,
    show (Real.sqrt 2 - 1) + 1 = Real.sqrt 2 by ring] at hP
  nlinarith only [hP, hscore]

end AmbidextrousSofa
