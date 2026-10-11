module

public import AmbidextrousSofa.Analysis.LowHeightScore

@[expose] public section

/-!
# The actual tilted diagonal relaxation

Two attained middle heights bound the left charged roof by its lower
middle height. The two actual diagonal supports then give separate
clipped affine roof bounds and the complete positive diagonal niche
tent. Integrating these literal functions gives the tilted relaxation,
with both window-clipping terms retained. No auxiliary lifted cap or
improvement of the original score is assumed.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def diagonalRelaxation (a h k u v : ℝ) : ℝ :=
  a - ((a - u) ^ 2 + (a - v) ^ 2) / 2 - a * h / 2 -
    (max ((u + v - h) / 2 - k) 0) ^ 2 +
      ((max (u - k - a / 2) 0) ^ 2 + (max (v - h - k - a / 2) 0) ^ 2) / 2

theorem min_eq_left_sub_positive (z w : ℝ) : min z w = z - max (z - w) 0 := by
  rw [← min_sub_sub_left, sub_sub_cancel, sub_zero, min_comm]

theorem integral_diagonal_right_roof {a u : ℝ} (hu0 : a / 2 ≤ u) (hu1 : u ≤ a) :
    (∫ x in (a / 2)..a, min 1 (1 + u - x)) = a / 2 - (a - u) ^ 2 / 2 := by
  simp_rw [fun x => show min 1 (1 + u - x) = 1 - max ((-u) + x) 0 by
    rw [min_eq_left_sub_positive]; ring_nf]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((show Continuous (fun x : ℝ => max ((-u) + x) 0) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_positive_ramp_add, smul_eq_mul,
    max_eq_left (by linarith : 0 ≤ -u + a), max_eq_right (by linarith : -u + a / 2 ≤ 0)]
  ring

theorem integral_diagonal_left_roof {a v : ℝ} (h : ℝ)
    (hv0 : a / 2 ≤ v) (hv1 : v ≤ a) :
    (∫ x in (-a)..(-a / 2), min (1 - h) (1 - h + v + x)) =
      a / 2 - a * h / 2 - (a - v) ^ 2 / 2 := by
  simp_rw [fun x => show min (1 - h) (1 - h + v + x) = (1 - h) - max ((-v) - x) 0 by
    rw [min_eq_left_sub_positive]; ring_nf]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((show Continuous (fun x : ℝ => max ((-v) - x) 0) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_positive_ramp_sub, smul_eq_mul,
    max_eq_left (by linarith : 0 ≤ -v - -a), max_eq_right (by linarith : -v - (-a / 2) ≤ 0)]
  ring

theorem IsDownwardCap.left_roof_le_middle_height
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    ∀ x ∈ Icc (-a) (-a / 2), capRoof U x ≤ 1 - h := by
  intro x hx
  have hproj := (hl ▸ hr ▸ hU.horizontalProjection_eq_Icc)
  have hchord := ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof
    (hproj ▸ ⟨hx.1, by linarith [hx.2]⟩ : x ∈ _) (hproj ▸ ⟨by linarith, by linarith⟩ : a / 2 ∈ _)
    (by linarith : -a / 2 < a / 2) hx.2
  rw [roofChord, hleft, hright] at hchord
  linarith [mul_nonpos_of_nonneg_of_nonpos (div_nonneg (by linarith : (0 : ℝ) ≤ 1 - (1 - h))
    (by linarith : (0 : ℝ) ≤ a / 2 - -a / 2)) (by linarith [hx.2] : x - -a / 2 ≤ 0)]

theorem IsDownwardCap.tilted_diagonal_parameters_mem
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a)
    (hh0 : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    diagonalRight U - 1 ∈ Icc (a / 2) a ∧
      diagonalLeft U - 1 + h ∈ Icc (a / 2) a := by
  have hproj := (hl ▸ hr ▸ hU.horizontalProjection_eq_Icc)
  have hL := hU.diagonalLeft_ge (capRoof_mem hU.isCompact
    (hproj ▸ ⟨by linarith, by linarith⟩ : -a / 2 ∈ horizontalProjection U))
  have hR := hU.diagonalRight_ge (capRoof_mem hU.isCompact
    (hproj ▸ ⟨by linarith, by linarith⟩ : a / 2 ∈ horizontalProjection U))
  have hLU : diagonalLeft U ≤ 1 - h + a := support_le_of_forall hU.nonempty fun p hp => by
    have hx : p.1 ∈ Icc (-a) a := hproj ▸ ⟨p, hp, rfl⟩
    simp only [coordDot, mul_neg_one, mul_one]
    by_cases hpx : p.1 ≤ -a / 2
    · linarith [hx.1, le_capRoof hU.isCompact (x := p.1) (y := p.2) hp,
        hU.left_roof_le_middle_height ha hh0 hl hr hleft hright p.1 ⟨hx.1, hpx⟩]
    · linarith [(hU.inStrip hp).2]
  exact ⟨⟨by linarith, by linarith [hU.diagonalRight_le]⟩, ⟨by linarith, by linarith⟩⟩

theorem tilted_diagonal_apex_mem {a h u v : ℝ} (ha : 0 ≤ a)
    (hh0 : 0 ≤ h) (hh1 : h ≤ a / 2) (hu : u ∈ Icc (a / 2) a)
    (hv : v ∈ Icc (a / 2) a) : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2) := by
  constructor <;> linarith [hu.1, hu.2, hv.1, hv.2]

theorem integral_tilted_diagonal_tent {a h u v : ℝ} (k : ℝ)
    (hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2)) :
    (∫ x in (-a / 2)..(a / 2), max (min (u - k - x) (v - h - k + x)) 0) =
      (max ((u + v - h) / 2 - k) 0) ^ 2 -
        (max (u - k - a / 2) 0) ^ 2 / 2 -
          (max (v - h - k - a / 2) 0) ^ 2 / 2 := by
  simp_rw [fun x => show min (u - k - x) (v - h - k + x) =
      ((u + v - h) / 2 - k) - |x - (u - v + h) / 2| by
    rw [← min_symmetric_lines]; ring_nf]
  rw [integral_positive_tent hd.1 hd.2]
  ring_nf

end AmbidextrousSofa
