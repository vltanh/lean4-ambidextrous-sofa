module

public import AmbidextrousSofa.Analysis.DiagonalScalar

@[expose] public section

/-!
# Actual exterior deficit and short-width stability

The deficit is the sum of two ordinary integrals between the actual
charged roof and its diagonal upper bounds. Its exact subtraction from
the diagonal relaxation retains the area available to pay for further
support cuts. The comparison holds for the spatial score of every barrier
above the diagonal barrier. A hypothetical short cap reaching the
generated reference budget has small tilt and a strictly positive
reserve on each outer diagonal segment.
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
  have hproj := (hl ▸ hr ▸ hU.horizontalProjection_eq_Icc)
  refine add_nonneg (intervalIntegral.integral_nonneg (by linarith) fun x hx => sub_nonneg.mpr
      (le_min (hU.left_roof_le_middle_height ha hh hl hr hleft hright x hx) ?_))
    (intervalIntegral.integral_nonneg (by linarith) fun x hx => sub_nonneg.mpr
      (le_min (capRoof_le_one hU.isCompact hU.inStrip x) ?_))
  · linarith [hU.capRoof_le_diagonalLeft (x := x) (hproj ▸ ⟨hx.1, by linarith [hx.2]⟩)]
  · linarith [hU.capRoof_le_diagonalRight (x := x) (hproj ▸ ⟨by linarith [hx.1], hx.2⟩)]

/-- In the coordinates `diagonalRight U = 1 + u` and `diagonalLeft U = 1 - h + v`, with
`k = √2 - 1`, the diagonal barrier is a clipped tent. -/
theorem IsDownwardCap.diagonalBarrier_eq_tilted {U : Set Plane} (hU : IsDownwardCap U)
    {h k u v : ℝ} (hk : k = Real.sqrt 2 - 1) (hu : diagonalRight U = 1 + u)
    (hv : diagonalLeft U = 1 - h + v) (x : ℝ) :
    diagonalBarrier U x = max (min (u - k - x) (v - h - k + x)) 0 := by
  rw [diagonalBarrier, cornerWall, firstWall_pi_div_four_eq_diagonal hU,
    secondWall_pi_div_four_eq_diagonal hU, hu, hv, hk]
  ring_nf

/-- Every barrier above the diagonal barrier integrates at least the tilted diagonal tent. -/
theorem IsDownwardCap.diagonal_tent_le_integral {U : Set Plane} (hU : IsDownwardCap U)
    {n : ℝ → ℝ} (hn : ∀ l r, IntervalIntegrable n volume l r)
    (hdiag : ∀ x, diagonalBarrier U x ≤ n x) {a h k u v : ℝ} (hk : k = Real.sqrt 2 - 1)
    (hu : diagonalRight U = 1 + u) (hv : diagonalLeft U = 1 - h + v)
    (hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2)) :
    (max ((u + v - h) / 2 - k) 0) ^ 2 - (max (u - k - a / 2) 0) ^ 2 / 2 -
      (max (v - h - k - a / 2) 0) ^ 2 / 2 ≤ ∫ x in (-a / 2)..(a / 2), n x := by
  rw [← integral_tilted_diagonal_tent k hd]
  exact intervalIntegral.integral_mono_on (hd.1.trans hd.2)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (hn _ _)
    fun x _ => (hU.diagonalBarrier_eq_tilted hk hu hv x).ge.trans (hdiag x)

/-- The spatial score of every barrier above the diagonal barrier, plus the roof deficit, is at
most the diagonal relaxation. -/
theorem IsDownwardCap.score_add_diagonalRoofDeficit_le {U : Set Plane} (hU : IsDownwardCap U)
    {n : ℝ → ℝ} (hn : ∀ l r, IntervalIntegrable n volume l r)
    (hdiag : ∀ x, diagonalBarrier U x ≤ n x) {a h : ℝ} (ha : 0 < a) (hh0 : 0 ≤ h)
    (hh1 : h ≤ a / 2) (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    intervalSpatialScore (capRoof U) n (-a) a +
        diagonalRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1 + h) ≤
      diagonalRelaxation a h (Real.sqrt 2 - 1)
        (diagonalRight U - 1) (diagonalLeft U - 1 + h) := by
  have huv := hU.tilted_diagonal_parameters_mem ha hh0 hh1 hl hr hleft hright
  have hN := hU.diagonal_tent_le_integral hn hdiag rfl (by ring) (by ring)
    (tilted_diagonal_apex_mem ha.le hh0 hh1 huv.1 huv.2)
  rw [intervalSpatialScore_centered, hU.diagonalRoofDeficit_eq h huv.1 huv.2, diagonalRelaxation]
  linarith only [hN]

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
  rw [hU.capScore_eq_intervalSpatialScore, hl, hr]
  exact hU.score_add_diagonalRoofDeficit_le (hU.intervalIntegrable_partialBarrier
    (by linarith [Real.pi_pos]) hαL) (hU.diagonalBarrier_le_partialBarrier hα0 hαL) ha hh0 hh1
    hl hr hleft hright

/-- The necessary geometric and scalar reserves follow from the actual
score, without a hypothesis about a relaxed optimizer. -/
theorem IsDownwardCap.short_diagonal_geometry {U : Set Plane} (hU : IsDownwardCap U)
    {n : ℝ → ℝ} (hn : ∀ l r, IntervalIntegrable n volume l r)
    (hdiag : ∀ x, diagonalBarrier U x ≤ n x) {a h : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hh : 0 ≤ h) (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (hscore : referenceHalfAreaLower ≤ intervalSpatialScore (capRoof U) n (-a) a) :
    let k := Real.sqrt 2 - 1
    let u := diagonalRight U - 1
    let v := diagonalLeft U - 1 + h
    (1 - k ^ 2 / 4) < a ∧ h < (k ^ 2 / 4) ∧ u ∈ Icc (a / 2) a ∧ v ∈ Icc (a / 2) a ∧
      u - a / 2 < shortTipThreshold k + h / 4 ∧ v - a / 2 < shortTipThreshold k + h / 4 ∧
      shortApexThreshold k < (u + v) / 2 - h / 4 ∧ k / 3 < a - u ∧ k / 3 < a - v ∧
      diagonalRoofDeficit U a h u v < shortOuterCutBudget k := by
  let k := Real.sqrt 2 - 1
  have hk := sqrt_two_sub_one_bounds
  try dsimp only [diagonalOffsetLower, diagonalOffsetUpper, squareRootNewton] at *
  -- The score is at most that of the charged rectangle.
  have hrect : intervalSpatialScore (capRoof U) n (-a) a ≤ a * (1 - h / 2) := by
    have hL := intervalIntegral.integral_mono_on (by linarith only [ha] : -a ≤ -a / 2)
      (hU.intervalIntegrable_capRoof _ _) (continuous_const.intervalIntegrable _ _)
      (hU.left_roof_le_middle_height ha hh hl hr hleft hright)
    have hR := intervalIntegral.integral_mono_on (by linarith only [ha] : a / 2 ≤ a)
      (hU.intervalIntegrable_capRoof _ _) (continuous_const.intervalIntegrable _ _)
      fun x _ => capRoof_le_one hU.isCompact hU.inStrip x
    have hN := intervalIntegral.integral_nonneg_of_forall (μ := volume)
      (by linarith only [ha] : -a / 2 ≤ a / 2) fun x => (diagonalBarrier_nonneg U x).trans (hdiag x)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hL hR
    rw [intervalSpatialScore_centered]
    linarith only [hL, hR, hN]
  have href := forty_one_fiftieths_lt_referenceHalfAreaLower
  have ha0 : 41 / 50 ≤ a := by nlinarith only [hrect, hscore, href, mul_nonneg ha.le hh]
  have hh37 : h ≤ 37 / 100 := by nlinarith only [hrect, hscore, href, ha, ha1]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh37]
  have huv := hU.tilted_diagonal_parameters_mem ha hh hhhalf hl hr hleft hright
  have hbound := hU.score_add_diagonalRoofDeficit_le hn hdiag ha hh hhhalf hl hr hleft hright
  have hD0 := hU.diagonalRoofDeficit_nonneg ha hh hl hr hleft hright
  obtain ⟨ha9, hh23, hu323, hv323, hm⟩ :=
    short_diagonal_stability ha0 ha1 hh hh37 hk.1 hk.2.1 sqrt_two_sub_one_quadratic
      huv.1 huv.2 (by linarith only [hbound, hD0, hscore])
  obtain ⟨-, -, -, -, -, -, -, -, -, hOuter, hBudget⟩ :=
    short_geometry_scalar_estimates hk.1 hk.2.1 sqrt_two_sub_one_quadratic
  have hRefLower := referenceHalfAreaLower_le_half_M
  change 1 - k ^ 2 / 4 < a at ha9
  change h < k ^ 2 / 4 at hh23
  have hksq : k ^ 2 + 2 * k = 1 := sqrt_two_sub_one_quadratic
  have hcrit := hbound.trans (diagonalRelaxation_le_critical _ _ _ _ _
    (by linarith only [hk.2.1, ha0, hh37]) (by linarith only [hk.1, hh])
    (by nlinarith only [hk.1, hk.2.1, hksq, hh23]))
  have hwidth := diagonal_critical_width_mono ha1
    (by linarith only [hk.1] : (1 : ℝ) ≤ 1 + (Real.sqrt 2 - 1))
  have hKH : 0 ≤ k * h := mul_nonneg (by linarith only [hk.1]) hh
  have hDeficit : diagonalRoofDeficit U a h (diagonalRight U - 1)
      (diagonalLeft U - 1 + h) < shortOuterCutBudget k := by
    nlinarith only [hcrit, hwidth, hscore, hBudget, hRefLower, hksq, hKH, sq_nonneg h]
  exact ⟨ha9, hh23, huv.1, huv.2, hu323, hv323, hm,
    by linarith only [hu323, ha9, hh23, hOuter],
    by linarith only [hv323, ha9, hh23, hOuter], hDeficit⟩

end AmbidextrousSofa
