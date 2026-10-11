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
  rw [wideLeftIntersection, show v + h / 2 = v + h - h / 2 by ring]
  exact tilted_diagonal_intersection_mem ha hha (by linarith only [hv0]) (by linarith only [hv1])

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
  have hv := hU.tilted_diagonalLeft_le ha (by linarith only [hh1, ha]) hl hr hleft hright haffine
  have hproj := (hU.horizontalProjection_eq_of hl hr).superset
  refine ⟨hp.1, ⟨by linarith only [hp.2.1], by linarith only [hv]⟩, ?_, ?_⟩
  · linarith only [hU.capRoof_le_diagonalRight (hproj ⟨by linarith only [ha], le_rfl⟩)]
  · linarith only [hU.capRoof_le_diagonalLeft (hproj ⟨le_rfl, by linarith only [ha]⟩)]

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
  have hleft := integral_tilted_diagonal_left_roof (v := v + h) ha hha (by linarith only [hv.1])
    (by linarith only [hv.2])
  rw [show 1 - h + (v + h) = 1 + v by ring] at hleft
  rw [wideRoofDeficit, intervalIntegral.integral_sub
      (((continuous_tiltedAffineCeiling a h).min (by fun_prop)).intervalIntegrable _ _)
      (hU.intervalIntegrable_capRoof _ _),
    intervalIntegral.integral_sub
      ((show Continuous (fun x : ℝ => min 1 (1 + u - x)) by fun_prop).intervalIntegrable _ _)
      (hU.intervalIntegrable_capRoof _ _), hleft, integral_diagonal_right_roof hu.1 hu.2,
    wideExteriorMajorant, div_mul_eq_div_div_swap]
  ring

theorem IsDownwardCap.wideRoofDeficit_nonneg {U : Set Plane}
    (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c) :
    0 ≤ wideRoofDeficit U a h (diagonalRight U - 1) (diagonalLeft U - 1) := by
  have hproj := (hU.horizontalProjection_eq_of hl hr).superset
  refine add_nonneg (intervalIntegral.integral_nonneg (by linarith only [ha]) fun x hx => ?_)
    (intervalIntegral.integral_nonneg (by linarith only [ha]) fun x hx => ?_)
  · have hxU := hproj ⟨hx.1, by linarith only [hx.2, ha]⟩
    exact sub_nonneg.mpr (le_min (hU.capRoof_le_tiltedAffineCeiling ha hl hr hleft hright
      haffine x hxU) (by linarith only [hU.capRoof_le_diagonalLeft hxU]))
  · have hxU := hproj ⟨by linarith only [hx.1, ha], hx.2⟩
    exact sub_nonneg.mpr (le_min (capRoof_le_one hU.isCompact hU.inStrip x)
      (by linarith only [hU.capRoof_le_diagonalRight hxU]))

end AmbidextrousSofa
