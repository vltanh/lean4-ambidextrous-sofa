module

public import AmbidextrousSofa.Analysis.WideDiagonalScalar
public import AmbidextrousSofa.Analysis.EndpointPositivity

@[expose] public section

/-!
# The wide majorant and deficit of the actual cap

The left ceiling is the literal affine continuation of the middle roof.
Both exterior integrals and both clipped diagonal niche tails are kept.
The endpoint height sum supplies the lower diagonal midpoint bound used
in the wide scalar comparison.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def wideExteriorMajorant (a h u v : ℝ) : ℝ :=
  a - 5 * a * h / 8 -
    ((a - u) ^ 2 + (a - v - 3 * h / 2) ^ 2 / (1 - h / a)) / 2

def wideRoofDeficit (U : Set Plane) (a h u v : ℝ) : ℝ :=
  (∫ x in (-a)..(-a / 2),
    min (tiltedAffineCeiling a h x) (1 + v + x) - capRoof U x) +
    ∫ x in (a / 2)..a, min 1 (1 + u - x) - capRoof U x

def wideLeftIntersection (a h v : ℝ) : ℝ := (v + h / 2) / (1 - h / a)

theorem wideLeftIntersection_mem {a h v : ℝ} (ha : 0 < a) (hha : h < a)
    (hv0 : a / 2 - h ≤ v) (hv1 : v ≤ a - 3 * h / 2) :
    wideLeftIntersection a h v ∈ Icc (a / 2) a := by
  have h := tilted_diagonal_intersection_mem ha hha
    (show a / 2 ≤ v + h by linarith only [hv0])
    (show v + h ≤ a - h / 2 by linarith only [hv1])
  convert h using 1 <;> unfold wideLeftIntersection <;> congr 2 <;> ring

theorem IsDownwardCap.wide_diagonal_parameters {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    diagonalRight U - 1 ∈ Icc (a / 2) a ∧
      diagonalLeft U - 1 ∈ Icc (a / 2 - h) (a - 3 * h / 2) ∧
      capRoof U a ≤ 1 - (a - (diagonalRight U - 1)) ∧
      capRoof U (-a) ≤ 1 - (a - (diagonalLeft U - 1)) := by
  have hp := hU.tilted_diagonal_parameters_mem ha hh hh1 hl hr hleft hright
  have hv := hU.tilted_diagonalLeft_le ha (by linarith only [hh1, ha])
    hl hr hleft hright haffine
  have hxR : a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨by linarith only [ha], le_rfl⟩
  have hxL : -a ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
    exact ⟨le_rfl, by linarith only [ha]⟩
  refine ⟨hp.1, ⟨?_, ?_⟩, ?_, ?_⟩
  · linarith only [hp.2.1]
  · linarith only [hv]
  · linarith only [hU.capRoof_le_diagonalRight hxR]
  · linarith only [hU.capRoof_le_diagonalLeft hxL]

theorem IsDownwardCap.wide_diagonal_midpoint_ge {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a)) :
    a - 1 / 2 - h / 4 ≤ ((diagonalRight U - 1) + (diagonalLeft U - 1)) / 2 := by
  have hp := hU.wide_diagonal_parameters ha hh hh1 hl hr hleft hright haffine
  linarith only [hp.2.2.1, hp.2.2.2, hEP]

theorem IsDownwardCap.wideRoofDeficit_eq {U : Set Plane} (hU : IsDownwardCap U)
    {a h u v : ℝ} (ha : 0 < a) (hha : h < a)
    (hu : u ∈ Icc (a / 2) a) (hv : v ∈ Icc (a / 2 - h) (a - 3 * h / 2)) :
    wideRoofDeficit U a h u v = wideExteriorMajorant a h u v -
      ((∫ x in (-a)..(-a / 2), capRoof U x) + ∫ x in (a / 2)..a, capRoof U x) := by
  have hleft := integral_tilted_diagonal_left_roof ha hha
    (show a / 2 ≤ v + h by linarith only [hv.1])
    (show v + h ≤ a - h / 2 by linarith only [hv.2])
  have hleft' : (∫ x in (-a)..(-a / 2),
      min (tiltedAffineCeiling a h x) (1 + v + x)) =
      a / 2 - 5 * a * h / 8 - (a - v - 3 * h / 2) ^ 2 / (2 * (1 - h / a)) := by
    simpa only [show 1 - h + (v + h) = 1 + v by ring,
      show a - (v + h) - h / 2 = a - v - 3 * h / 2 by ring] using hleft
  unfold wideRoofDeficit
  rw [intervalIntegral.integral_sub
      (((continuous_tiltedAffineCeiling a h).min (by fun_prop)).intervalIntegrable _ _)
      (hU.intervalIntegrable_capRoof _ _),
    intervalIntegral.integral_sub
      ((show Continuous (fun x : ℝ => min 1 (1 + u - x)) by fun_prop).intervalIntegrable _ _)
      (hU.intervalIntegrable_capRoof _ _), hleft', integral_diagonal_right_roof hu.1 hu.2]
  unfold wideExteriorMajorant
  ring

theorem IsDownwardCap.wideRoofDeficit_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    0 ≤ wideRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1) := by
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  unfold wideRoofDeficit
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg (by linarith only [ha])
    intro x hx
    have hxU : x ∈ horizontalProjection U := by rw [hproj]; exact ⟨hx.1, by linarith only [hx.2, ha]⟩
    apply sub_nonneg.mpr
    exact le_min (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright haffine x hxU)
      (by linarith only [hU.capRoof_le_diagonalLeft hxU])
  · apply intervalIntegral.integral_nonneg (by linarith only [ha])
    intro x hx
    have hxU : x ∈ horizontalProjection U := by rw [hproj]; exact ⟨by linarith only [hx.1, ha], hx.2⟩
    apply sub_nonneg.mpr
    exact le_min (capRoof_le_one hU.isCompact hU.inStrip x)
      (by linarith only [hU.capRoof_le_diagonalRight hxU])

theorem IsDownwardCap.capScore_add_wideRoofDeficit_le {U : Set Plane}
    (hU : IsDownwardCap U) {a h α : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hm : Real.sqrt 2 - 1 ≤ ((diagonalRight U - 1) + (diagonalLeft U - 1)) / 2)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α + wideRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1) ≤
      wideDiagonalMajorant a h (Real.sqrt 2 - 1) (diagonalRight U - 1) (diagonalLeft U - 1) := by
  have hp := hU.wide_diagonal_parameters ha hh hh1 hl hr hleft hright haffine
  have hD := hU.wideRoofDeficit_eq ha (by linarith only [ha, hh1]) hp.1 hp.2.1
  have hN := hU.tilted_diagonal_tent_integral_le ha hh hh1 hl hr hleft hright hα0 hαL
  dsimp only at hN
  rw [show ((diagonalRight U - 1) + (diagonalLeft U - 1 + h) - h) / 2 -
      (Real.sqrt 2 - 1) = ((diagonalRight U - 1) + (diagonalLeft U - 1)) / 2 -
      (Real.sqrt 2 - 1) by ring,
    max_eq_left (sub_nonneg.mpr hm)] at hN
  rw [hU.capScore_eq_intervalSpatialScore, hl, hr, intervalSpatialScore,
    show -a + (a - -a) / 4 = -a / 2 by ring,
    show a - (a - -a) / 4 = a / 2 by ring]
  unfold wideExteriorMajorant at hD
  unfold wideDiagonalMajorant
  have htail : diagonalLeft U - 1 + h - h - (Real.sqrt 2 - 1) - a / 2 =
      diagonalLeft U - 1 - (Real.sqrt 2 - 1) - a / 2 := by ring
  rw [htail] at hN
  linarith only [hD, hN]

/-- The preliminary wide box is a consequence of the literal cap score,
its actual affine middle, and its endpoint height sum. -/
theorem IsDownwardCap.wide_high_score_box {U : Set Plane}
    (hU : IsDownwardCap U) {a h α : ℝ} (ha0 : 8 / 5 ≤ a) (ha1 : a < 3)
    (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hEP : 1 - h / 2 ≤ capRoof U a + capRoof U (-a))
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2)
    (hscore : 41 / 50 ≤ capScore U α) :
    a < 9 / 5 ∧ h < 1 / 4 ∧ a + h < 37 / 20 := by
  have ha : 0 < a := by linarith only [ha0]
  have hhhalf : h ≤ a / 2 := by linarith only [ha0, hh1]
  have hm := hU.wide_diagonal_midpoint_ge ha hh hhhalf hl hr hleft hright haffine hEP
  have hbound := hU.capScore_add_wideRoofDeficit_le ha hh hhhalf hl hr hleft hright haffine
    (by linarith only [hm, ha0, hh1, sqrt_two_sub_one_strict_bounds.2.2]) hα0 hαL
  have hdef := hU.wideRoofDeficit_nonneg ha hl hr hleft hright haffine
  exact wide_diagonal_high_score_box ha0 ha1 hh hh1 sqrt_two_sub_one_strict_bounds.1
    sqrt_two_sub_one_strict_bounds.2.2 sqrt_two_sub_one_quadratic hm (by linarith only [hscore, hbound, hdef])

end AmbidextrousSofa
