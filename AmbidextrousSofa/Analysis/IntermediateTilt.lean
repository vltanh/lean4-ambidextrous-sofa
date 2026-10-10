module

public import AmbidextrousSofa.Analysis.TiltedDiagonalRoof

@[expose] public section

/-!
# The actual intermediate-width tilt bound

The mandatory affine-ceiling loss is subtracted from the complete
diagonal relaxation. A global supporting plane at its explicit unclipped
stationary point gives the exact coupled width/tilt bound. The positive
parts are retained until the supporting-plane comparison is applied.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def tiltedDiagonalRelaxation (a h k u v : ℝ) : ℝ :=
  diagonalRelaxation a h k u v - h * (v - a / 2) ^ 2 / (2 * (a - h))

def tiltedDiagonalBound (a h k : ℝ) : ℝ :=
  a - 5 * a * h / 8 - 2 * a * (a - 3 * h / 4 - k) ^ 2 / (4 * a - h)

theorem tiltedDiagonalRelaxation_le_tangent {a h : ℝ} (ha : h < a) (hh : 0 ≤ h)
    (k u v u0 v0 : ℝ) (hq : 0 ≤ (u0 + v0 - h) / 2 - k)
    (hu0 : u0 ≤ k + a / 2) (hv0 : v0 ≤ h + k + a / 2) :
    tiltedDiagonalRelaxation a h k u v ≤
      a - ((a - u0) ^ 2 + (a - v0) ^ 2) / 2 - a * h / 2 -
        ((u0 + v0 - h) / 2 - k) ^ 2 - h * (v0 - a / 2) ^ 2 / (2 * (a - h)) +
      (a - u0 - ((u0 + v0 - h) / 2 - k)) * (u - u0) +
      (a - v0 - ((u0 + v0 - h) / 2 - k) - h * (v0 - a / 2) / (a - h)) * (v - v0) := by
  have hd := diagonalRelaxation_le_tangent a h k u v u0 v0 hq hu0 hv0
  have hsq : (v0 - a / 2) ^ 2 + 2 * (v0 - a / 2) * (v - v0) ≤ (v - a / 2) ^ 2 := by
    nlinarith only [sq_nonneg (v - v0)]
  have hscale := mul_le_mul_of_nonneg_left hsq
    (div_nonneg hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sub_pos.mpr ha).le))
  have htilt : h * (v0 - a / 2) ^ 2 / (2 * (a - h)) +
      h * (v0 - a / 2) / (a - h) * (v - v0) ≤
      h * (v - a / 2) ^ 2 / (2 * (a - h)) := by
    convert hscale using 1 <;> field_simp [(sub_pos.mpr ha).ne'] <;> ring
  unfold tiltedDiagonalRelaxation
  nlinarith only [hd, htilt]

theorem tiltedDiagonalRelaxation_le_bound {a h k : ℝ}
    (ha : 1 ≤ a) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 2 / 5 < k) (hk1 : k < 169 / 408) (u v : ℝ) :
    tiltedDiagonalRelaxation a h k u v ≤ tiltedDiagonalBound a h k := by
  have ha0 : 0 < a := by linarith only [ha]
  have hha : h < a := by linarith only [hh1, ha]
  have h4 : 0 < 4 * a - h := by linarith only [ha, hh1]
  let z := h / a
  let D := 2 * a * (a - 3 * h / 4 - k) / (4 * a - h)
  let u0 := a - D
  let v0 := a - h / 2 - (1 - z) * D
  have hz0 : 0 ≤ z := div_nonneg hh0 ha0.le
  have hz1 : z < 1 / 2 := by
    apply (div_lt_iff₀ ha0).mpr
    linarith only [hh1, ha]
  have hza : z * a = h := div_mul_cancel₀ h ha0.ne'
  have hden : 0 < 4 - z := by linarith only [hz1]
  have hDform : D = 2 * (a - 3 * h / 4 - k) / (4 - z) := by
    rw [show 4 - z = (4 * a - h) / a by dsimp [z]; field_simp [ha0.ne']; ring]
    dsimp [D, z]
    field_simp [ha0.ne', h4.ne'] <;> ring
  have hD0 : 0 < D := by
    rw [hDform]
    exact div_pos (by linarith only [ha, hh1, hk1]) hden
  have hDhalf : D < a / 2 := by
    rw [hDform]
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [hza, hh0, hk0]
  have hclip : a / 2 - k ≤ D := by
    rw [hDform]
    apply (le_div_iff₀ hden).mpr
    have hprod := mul_nonneg (show 0 ≤ k by linarith only [hk0])
      (show 0 ≤ 1 / 2 - z by linarith only [hz1])
    nlinarith only [hza, hprod, hh1, hk0]
  have hDden : D * (4 - z) = 2 * (a - 3 * h / 4 - k) := by
    rw [hDform]
    exact div_mul_cancel₀ _ hden.ne'
  have hq : (u0 + v0 - h) / 2 - k = D := by
    dsimp [u0, v0]
    nlinarith only [hDden]
  have huclip : u0 ≤ k + a / 2 := by dsimp [u0]; linarith only [hclip]
  have hvclip : v0 ≤ h + k + a / 2 := by
    have hprod := mul_nonneg hz0 (sub_nonneg.mpr hDhalf.le)
    dsimp [v0]
    nlinarith only [hprod, hza, hclip, hh0]
  have hgradU : a - u0 - ((u0 + v0 - h) / 2 - k) = 0 := by
    rw [hq]
    dsimp [u0]
    ring
  have hgradV : a - v0 - ((u0 + v0 - h) / 2 - k) -
      h * (v0 - a / 2) / (a - h) = 0 := by
    rw [hq]
    dsimp [v0, z]
    field_simp [ha0.ne', (sub_pos.mpr hha).ne'] <;> ring
  have ht := tiltedDiagonalRelaxation_le_tangent hha hh0 k u v u0 v0
    (by rw [hq]; exact hD0.le) huclip hvclip
  rw [hgradU, hgradV, zero_mul, zero_mul, add_zero, add_zero, hq] at ht
  have hvalue : a - ((a - u0) ^ 2 + (a - v0) ^ 2) / 2 - a * h / 2 - D ^ 2 -
      h * (v0 - a / 2) ^ 2 / (2 * (a - h)) = tiltedDiagonalBound a h k := by
    dsimp [u0, v0, z, D, tiltedDiagonalBound]
    field_simp [ha0.ne', (sub_pos.mpr hha).ne', h4.ne'] <;> ring
  rwa [hvalue] at ht

theorem tiltedDiagonalBound_eq_width_tilt {a h k : ℝ} (h4 : 4 * a - h ≠ 0)
    (hksq : k ^ 2 + 2 * k = 1) :
    tiltedDiagonalBound a h k =
      1 - (a - (k + 1)) ^ 2 / 2 - (2 * a / (4 * a - h)) * (k + h / 2) ^ 2 := by
  calc
    _ = 1 - (a - (k + 1)) ^ 2 / 2 - (2 * a / (4 * a - h)) * (k + h / 2) ^ 2 +
        (k ^ 2 + 2 * k - 1) / 2 := by
      unfold tiltedDiagonalBound
      field_simp [h4] <;> ring
    _ = _ := by rw [hksq]; ring

theorem diagonal_offset_gt_forty_one_ninety_ninths {k : ℝ} (hk : 0 < k)
    (hksq : k ^ 2 + 2 * k = 1) : (41 / 99 : ℝ) < k := by
  by_contra h
  have hprod := mul_nonneg (show 0 ≤ 41 / 99 - k by linarith only [le_of_not_gt h])
    (show 0 ≤ 41 / 99 + k by linarith only [hk])
  nlinarith only [hprod, hksq, le_of_not_gt h]

theorem tiltedDiagonalBound_lt_of_large_tilt {a h k : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 17 / 50 ≤ h) (hh1 : h < 1 / 2)
    (hk : 0 < k) (hksq : k ^ 2 + 2 * k = 1) :
    tiltedDiagonalBound a h k < (41 / 50 : ℝ) := by
  have h4 : 0 < 4 * a - h := by linarith only [ha0, hh1]
  have hcoef : (160 / 303 : ℝ) ≤ 2 * a / (4 * a - h) := by
    apply (le_div_iff₀ h4).mpr
    linarith only [ha1, hh0]
  have hkq := diagonal_offset_gt_forty_one_ninety_ninths hk hksq
  have hq : (41 / 99 + 17 / 100 : ℝ) < k + h / 2 := by linarith only [hkq, hh0]
  have hqsum : 0 < k + h / 2 + (41 / 99 + 17 / 100 : ℝ) := by
    linarith only [hk, hh0]
  have hqprod := mul_pos (sub_pos.mpr hq) hqsum
  have hpay := mul_nonneg (sub_nonneg.mpr hcoef) (sq_nonneg (k + h / 2))
  rw [tiltedDiagonalBound_eq_width_tilt h4.ne' hksq]
  nlinarith only [hqprod, hpay, sq_nonneg (a - (k + 1))]

/-- INT.1 for the actual tilted cap, including every diagonal clipping
configuration. Only the original cap's middle geometry is assumed. -/
theorem IsDownwardCap.capScore_le_tiltedDiagonalBound
    {U : Set Plane} (hU : IsDownwardCap U) {a h α : ℝ}
    (ha : 1 ≤ a) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2) :
    capScore U α ≤ tiltedDiagonalBound a h (Real.sqrt 2 - 1) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hhhalf : h ≤ a / 2 := by linarith only [ha, hh1]
  have hha : h < a := by linarith only [ha, hh1]
  let u := diagonalRight U - 1
  let v := diagonalLeft U - 1 + h
  have huv := hU.tilted_diagonal_parameters_mem ha0 hh0 hhhalf hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_ge_tilt_loss ha0 hha hl hr hleft hright haffine
    (show diagonalRight U = 1 + u by dsimp [u]; ring)
    (show diagonalLeft U = 1 - h + v by dsimp [v]; ring) huv.1 huv.2
  have hP := hU.capScore_add_diagonalRoofDeficit_le ha0 hh0 hhhalf hl hr hleft hright hα0 hαL
  have hscalar := tiltedDiagonalRelaxation_le_bound ha hh0 hh1
    sqrt_two_sub_one_strict_bounds.1 sqrt_two_sub_one_strict_bounds.2.1 u v
  unfold tiltedDiagonalRelaxation at hscalar
  linarith only [hD, hP, hscalar]

theorem IsDownwardCap.intermediate_width_tilt_bound
    {U : Set Plane} (hU : IsDownwardCap U) {a h α : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hl : horizontalLeft U = -a) (hr : horizontalRight U = a)
    (hleft : capRoof U (-a / 2) = 1 - h) (hright : capRoof U (a / 2) = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ Icc (-a / 2) (a / 2), capRoof U x = m * x + c)
    (hα0 : Real.pi / 4 ≤ α) (hαL : α ≤ Real.pi / 2)
    (hscore : 41 / 50 ≤ capScore U α) :
    h < 17 / 50 ∧ (a - Real.sqrt 2) ^ 2 +
      (4 * a / (4 * a - h)) * (Real.sqrt 2 - 1 + h / 2) ^ 2 ≤ 9 / 25 := by
  have hP := hU.capScore_le_tiltedDiagonalBound ha0 hh0 hh1 hl hr hleft hright haffine hα0 hαL
  have h4 : 0 < 4 * a - h := by linarith only [ha0, hh1]
  have hksq := sqrt_two_sub_one_quadratic
  have htilt : h < 17 / 50 := by
    by_contra h
    exact (not_lt_of_ge hscore) (hP.trans_lt
      (tiltedDiagonalBound_lt_of_large_tilt ha0 ha1 (le_of_not_gt h) hh1
        (by linarith [sqrt_two_sub_one_strict_bounds.1]) hksq))
  refine ⟨htilt, ?_⟩
  rw [tiltedDiagonalBound_eq_width_tilt h4.ne' hksq,
    show (Real.sqrt 2 - 1) + 1 = Real.sqrt 2 by ring] at hP
  nlinarith only [hP, hscore]

end AmbidextrousSofa
