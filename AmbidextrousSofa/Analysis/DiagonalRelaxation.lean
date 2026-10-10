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
  by_cases h : z ≤ w
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
    ring

theorem integral_diagonal_right_roof {a u : ℝ} (hu0 : a / 2 ≤ u) (hu1 : u ≤ a) :
    (∫ x in (a / 2)..a, min 1 (1 + u - x)) = a / 2 - (a - u) ^ 2 / 2 := by
  have heq (x : ℝ) : min 1 (1 + u - x) = 1 - max ((-u) + x) 0 := by
    rw [min_eq_left_sub_positive]
    congr 2
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((show Continuous (fun x : ℝ => max ((-u) + x) 0) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_positive_ramp_add,
    max_eq_left (by linarith : 0 ≤ -u + a),
    max_eq_right (by linarith : -u + a / 2 ≤ 0)]
  simp only [smul_eq_mul]
  ring

theorem integral_diagonal_left_roof {a v : ℝ} (h : ℝ)
    (hv0 : a / 2 ≤ v) (hv1 : v ≤ a) :
    (∫ x in (-a)..(-a / 2), min (1 - h) (1 - h + v + x)) =
      a / 2 - a * h / 2 - (a - v) ^ 2 / 2 := by
  have heq (x : ℝ) : min (1 - h) (1 - h + v + x) =
      (1 - h) - max ((-v) - x) 0 := by
    rw [min_eq_left_sub_positive]
    congr 2
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((show Continuous (fun x : ℝ => max ((-v) - x) 0) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_positive_ramp_sub,
    max_eq_left (by linarith : 0 ≤ -v - -a),
    max_eq_right (by linarith : -v - (-a / 2) ≤ 0)]
  simp only [smul_eq_mul]
  ring

theorem IsDownwardCap.left_roof_le_middle_height
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    ∀ x ∈ Icc (-a) (-a / 2), capRoof U x ≤ 1 - h := by
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  intro x hx
  have hxU : x ∈ horizontalProjection U := by rw [hproj]; exact ⟨hx.1, by linarith [hx.2]⟩
  have haU : a / 2 ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hchord := ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof hxU haU
    (by linarith : -a / 2 < a / 2) hx.2
  have hnonpos : (capRoof U (a / 2) - capRoof U (-a / 2)) /
      (a / 2 - (-a / 2)) * (x - (-a / 2)) ≤ 0 := by
    rw [hleft, hright]
    exact mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (by linarith) (by linarith)) (by linarith [hx.2])
  unfold roofChord at hchord
  rw [hleft, hright] at hchord hnonpos
  linarith

theorem IsDownwardCap.tilted_diagonal_parameters_mem
    {U : Set Plane} (hU : IsDownwardCap U) {a h : ℝ} (ha : 0 < a)
    (hh0 : 0 ≤ h) (hh1 : h ≤ a / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1) :
    diagonalRight U - 1 ∈ Icc (a / 2) a ∧
      diagonalLeft U - 1 + h ∈ Icc (a / 2) a := by
  have hproj : horizontalProjection U = Icc (-a) a := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex, hl, hr]
  have hleftMem : -a / 2 ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hrightMem : a / 2 ∈ horizontalProjection U := by rw [hproj]; constructor <;> linarith
  have hL := hU.diagonalLeft_ge (capRoof_mem hU.isCompact hleftMem)
  have hR := hU.diagonalRight_ge (capRoof_mem hU.isCompact hrightMem)
  rw [hleft] at hL
  rw [hright] at hR
  have hRU := hU.diagonalRight_le
  rw [hr] at hRU
  have hLU : diagonalLeft U ≤ 1 - h + a := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    have hx : p.1 ∈ Icc (-a) a := by
      rw [← hproj]
      exact ⟨p, hp, rfl⟩
    have hy := le_capRoof hU.isCompact (show (p.1, p.2) ∈ U by simpa only [Prod.mk.eta] using hp)
    simp only [coordDot, mul_neg_one, mul_one]
    by_cases hpx : p.1 ≤ -a / 2
    · have hbound := hU.left_roof_le_middle_height ha hh0 hl hr hleft hright p.1 ⟨hx.1, hpx⟩
      linarith [hx.1]
    · have hbound := (hU.inStrip hp).2
      linarith
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

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
  have heq (x : ℝ) : min (u - k - x) (v - h - k + x) =
      ((u + v - h) / 2 - k) - |x - (u - v + h) / 2| := by
    convert min_symmetric_lines ((u + v - h) / 2 - k) ((u - v + h) / 2) x using 1
      <;> congr 1 <;> ring
  simp_rw [heq]
  rw [integral_positive_tent hd.1 hd.2]
  rw [show ((u + v - h) / 2 - k) - ((u - v + h) / 2 - (-a / 2)) =
      v - h - k - a / 2 by ring,
    show ((u + v - h) / 2 - k) - (a / 2 - (u - v + h) / 2) =
      u - k - a / 2 by ring]
  ring

end AmbidextrousSofa
