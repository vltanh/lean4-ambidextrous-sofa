module

public import AmbidextrousSofa.Analysis.DiagonalScalar

@[expose] public section

/-!
# Actual exterior deficit and short-width stability

The deficit is the sum of two ordinary integrals between the actual
charged roof and its diagonal upper bounds. Its exact subtraction from
the diagonal relaxation retains the area available to pay for further
support cuts. A hypothetical short cap with score at least 41/50 has
small tilt, inactive diagonal clipping and a strictly positive reserve
on each outer diagonal segment.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def diagonalRoofDeficit (U : Set Plane) (a h u v : ℝ) : ℝ :=
  (∫ x in (-a)..(-a / 2), min (1 - h) (1 - h + v + x) - capRoof U x) +
    ∫ x in (a / 2)..a, min 1 (1 + u - x) - capRoof U x

theorem IsDownwardCap.diagonalRoofDeficit_eq {U : Set Plane} (hU : IsDownwardCap U)
    {a u v : ℝ} (h : ℝ) (hu : u ∈ Icc (a / 2) a) (hv : v ∈ Icc (a / 2) a) :
    diagonalRoofDeficit U a h u v =
      a - ((a - u) ^ 2 + (a - v) ^ 2) / 2 - a * h / 2 -
        ((∫ x in (-a)..(-a / 2), capRoof U x) + ∫ x in (a / 2)..a, capRoof U x) := by
  unfold diagonalRoofDeficit
  rw [intervalIntegral.integral_sub ((show Continuous fun x : ℝ => min (1 - h) (1 - h + v + x)
      by fun_prop).intervalIntegrable _ _) (hU.intervalIntegrable_capRoof _ _),
    intervalIntegral.integral_sub ((show Continuous fun x : ℝ => min 1 (1 + u - x)
      by fun_prop).intervalIntegrable _ _) (hU.intervalIntegrable_capRoof _ _),
    integral_diagonal_left_roof h hv.1 hv.2, integral_diagonal_right_roof hu.1 hu.2]
  ring

theorem IsDownwardCap.diagonalRoofDeficit_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    0 ≤ diagonalRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1 + h) := by
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  refine add_nonneg (intervalIntegral.integral_nonneg (by linarith) fun x hx => sub_nonneg.mpr
      (le_min (hU.left_roof_le_middle_height ha hh hl hr hleft hright x hx) ?_))
    (intervalIntegral.integral_nonneg (by linarith) fun x hx => sub_nonneg.mpr
      (le_min (capRoof_le_one hU.isCompact hU.inStrip x) ?_))
  · linarith [hU.capRoof_le_diagonalLeft (x := x) (hproj ▸ ⟨hx.1, by linarith [hx.2]⟩)]
  · linarith [hU.capRoof_le_diagonalRight (x := x) (hproj ▸ ⟨by linarith [hx.1], hx.2⟩)]

theorem IsDownwardCap.tilted_diagonal_tent_integral_le {U : Set Plane}
    (hU : IsDownwardCap U) {a h α : ℝ} (ha : 0 < a)
    (hh0 : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    let u := diagonalRight U - 1
    let v := diagonalLeft U - 1 + h
    let k := Real.sqrt 2 - 1
    (max ((u + v - h) / 2 - k) 0) ^ 2 -
      (max (u - k - a / 2) 0) ^ 2 / 2 - (max (v - h - k - a / 2) 0) ^ 2 / 2 ≤
        ∫ x in (-a / 2)..(a / 2), partialBarrier U α x := by
  dsimp only
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hh1 hl hr hleft hright
  rw [← integral_tilted_diagonal_tent (Real.sqrt 2 - 1)
    (tilted_diagonal_apex_mem ha.le hh0 hh1 huv.1 huv.2)]
  refine intervalIntegral.integral_mono_on (by linarith)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (hU.intervalIntegrable_partialBarrier (by linarith [Real.pi_pos]) hαL _ _) fun x _ => ?_
  have := max_le (cornerWall_pi_div_four_le_partialBarrier hU.isCompact hα0 hαL x)
    (partialBarrier_nonneg U α x)
  rw [cornerWall, firstWall_pi_div_four_eq_diagonal hU,
    secondWall_pi_div_four_eq_diagonal hU] at this
  convert this using 3 <;> ring

theorem IsDownwardCap.capScore_add_diagonalRoofDeficit_le {U : Set Plane}
    (hU : IsDownwardCap U) {a h α : ℝ} (ha : 0 < a)
    (hh0 : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α +
        diagonalRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1 + h) ≤
      diagonalRelaxation a h (Real.sqrt 2 - 1)
        (diagonalRight U - 1) (diagonalLeft U - 1 + h) := by
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hh1 hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_eq h huv.1 huv.2
  have hN := hU.tilted_diagonal_tent_integral_le ha hh0 hh1 hl hr hleft hright hα0 hαL
  dsimp only at hN
  rw [hU.capScore_eq_intervalSpatialScore, hl, hr, intervalSpatialScore,
    show -a + (a - -a) / 4 = -a / 2 by ring, show a - (a - -a) / 4 = a / 2 by ring]
  unfold diagonalRelaxation
  linarith

/-- The necessary geometric and scalar reserves follow from the actual
score, without a hypothesis about a relaxed optimizer. -/
theorem IsDownwardCap.short_diagonal_geometry {U : Set Plane}
    (hU : IsDownwardCap U) {a h α : ℝ} (ha : 0 < a) (ha1 : a ≤ 1001 / 1000)
    (hh : 0 ≤ h) (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2)
    (hscore : 41 / 50 ≤ capScore U α) :
    let u := diagonalRight U - 1
    let v := diagonalLeft U - 1 + h
    let k := Real.sqrt 2 - 1
    9 / 10 < a ∧ h < 1 / 23 ∧
      u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a ∧
      u - a / 2 < 323 / 1000 + h / 4 ∧
      v - a / 2 < 323 / 1000 + h / 4 ∧
      16 / 25 < (u + v) / 2 - h / 4 ∧
      0 < (u + v - h) / 2 - k ∧
      u - k - a / 2 < 0 ∧ v - h - k - a / 2 < 0 ∧
      23 / 200 < a - u ∧ 23 / 200 < a - v ∧
      0 ≤ diagonalRoofDeficit U a h u v ∧ diagonalRoofDeficit U a h u v < 9 / 1000 := by
  have hrect : capScore U α ≤ a * (1 - h / 2) := by
    have hL := intervalIntegral.integral_mono_on (by linarith : -a ≤ -a / 2)
      (hU.intervalIntegrable_capRoof _ _) (continuous_const.intervalIntegrable _ _)
      (hU.left_roof_le_middle_height ha hh hl hr hleft hright)
    have hR := intervalIntegral.integral_mono_on (by linarith : a / 2 ≤ a)
      (hU.intervalIntegrable_capRoof _ _) (continuous_const.intervalIntegrable _ _)
      (fun x (_ : x ∈ Icc (a / 2) a) => capRoof_le_one hU.isCompact hU.inStrip x)
    have hN := intervalIntegral.integral_nonneg_of_forall (μ := volume)
      (by linarith : -a / 2 ≤ a / 2) (partialBarrier_nonneg U α)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hL hR
    rw [hU.capScore_eq_intervalSpatialScore, hl, hr, intervalSpatialScore,
      show -a + (a - -a) / 4 = -a / 2 by ring, show a - (a - -a) / 4 = a / 2 by ring]
    linarith
  have ha0 : 41 / 50 ≤ a := by linarith [mul_nonneg ha.le hh]
  have hh37 : h ≤ 37 / 100 := by nlinarith
  have huv := hU.tilted_diagonal_parameters_mem ha hh (by linarith) hl hr hleft hright
  have hbound := hU.capScore_add_diagonalRoofDeficit_le ha hh (by linarith) hl hr hleft hright
    hα0 hαL
  have hD0 := hU.diagonalRoofDeficit_nonneg ha hh hl hr hleft hright
  obtain ⟨hk0, hk1, hk2⟩ := sqrt_two_sub_one_strict_bounds
  obtain ⟨ha9, hh23, hu323, hv323, hm, hq, hclipR, hclipL⟩ :=
    short_diagonal_stability ha0 ha1 hh hh37 hk0 hk1 hk2 sqrt_two_sub_one_quadratic
      huv.1 huv.2 (by linarith)
  have hcritical := diagonalRelaxation_le_critical a h (Real.sqrt 2 - 1) (diagonalRight U - 1)
    (diagonalLeft U - 1 + h) (by linarith) (by linarith) (by linarith)
  have hwidth := diagonal_critical_width_mono ha1
    (by linarith : (1001 / 1000 : ℝ) ≤ 1 + (Real.sqrt 2 - 1))
  exact ⟨ha9, hh23, huv.1, huv.2, hu323, hv323, hm, hq, hclipR, hclipL,
    by linarith, by linarith, hD0,
    by linarith [sqrt_two_sub_one_quadratic, mul_nonneg (by linarith : 0 ≤ Real.sqrt 2 - 1) hh,
      sq_nonneg h]⟩

end AmbidextrousSofa
