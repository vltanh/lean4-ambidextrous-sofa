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
  have hscale := mul_le_mul_of_nonneg_left
    (show (v0 - a / 2) ^ 2 + 2 * (v0 - a / 2) * (v - v0) ≤ (v - a / 2) ^ 2 by
      nlinarith only [sq_nonneg (v - v0)])
    (div_nonneg hh (by linarith : (0 : ℝ) ≤ 2 * (a - h)))
  have htilt : h * (v0 - a / 2) ^ 2 / (2 * (a - h)) +
      h * (v0 - a / 2) / (a - h) * (v - v0) ≤ h * (v - a / 2) ^ 2 / (2 * (a - h)) := by
    convert hscale using 1 <;> field_simp [(sub_pos.mpr ha).ne']
  unfold tiltedDiagonalRelaxation
  linarith [diagonalRelaxation_le_tangent a h k u v u0 v0 hq hu0 hv0]

theorem tiltedDiagonalRelaxation_le_bound {a h k : ℝ}
    (ha : 1 ≤ a) (hh0 : 0 ≤ h) (hh1 : h < 1 / 2)
    (hk0 : 41 / 99 < k) (hk1 : k < 169 / 408) (u v : ℝ) :
    tiltedDiagonalRelaxation a h k u v ≤ tiltedDiagonalBound a h k := by
  have hha : h < a := by linarith only [hh1, ha]
  have h4 : 0 < 4 * a - h := by linarith only [ha, hh1]
  -- The tangent plane is taken at the stationary point `(a - a * E, a - h / 2 - (a - h) * E)`.
  obtain ⟨E, hE⟩ : ∃ E, E * (4 * a - h) = 2 * (a - 3 * h / 4 - k) :=
    ⟨_, div_mul_cancel₀ _ h4.ne'⟩
  have hE0 : 0 < E := by nlinarith
  have hE1 : E < 1 / 2 := by nlinarith
  have hu : a - a * E ≤ k + a / 2 := by
    nlinarith [congrArg (a * ·) hE, mul_nonneg (sub_nonneg.2 ha) (by linarith : 0 ≤ 2 * k - h),
      mul_nonneg (by linarith : (0 : ℝ) ≤ k) (by linarith : 0 ≤ 1 / 2 - h)]
  have hq : (a - a * E + (a - h / 2 - (a - h) * E) - h) / 2 - k = a * E := by linarith
  refine (tiltedDiagonalRelaxation_le_tangent hha hh0 k u v _ _ (by rw [hq]; positivity) hu
    (by nlinarith [mul_le_mul_of_nonneg_left hE1.le hh0])).trans_eq ?_
  rw [hq]
  obtain rfl : k = a - 3 * h / 4 - E * (4 * a - h) / 2 := by linarith
  unfold tiltedDiagonalBound
  field_simp [(sub_pos.2 hha).ne', h4.ne', (by linarith : 0 < a * 4 - h).ne']
  ring

theorem tiltedDiagonalBound_eq_width_tilt {a h k : ℝ} (h4 : 4 * a - h ≠ 0)
    (hksq : k ^ 2 + 2 * k = 1) :
    tiltedDiagonalBound a h k =
      1 - (a - (k + 1)) ^ 2 / 2 - (2 * a / (4 * a - h)) * (k + h / 2) ^ 2 := by
  have h4' : a * 4 - h ≠ 0 := by rwa [mul_comm] at h4
  unfold tiltedDiagonalBound
  field_simp
  linear_combination 128 * (a * 4 - h) * hksq

theorem tiltedDiagonalBound_lt_of_large_tilt {a h k : ℝ}
    (ha0 : 1 ≤ a) (ha1 : a ≤ 8 / 5) (hh0 : 17 / 50 ≤ h) (hh1 : h < 1 / 2)
    (hk : 41 / 99 < k) (hksq : k ^ 2 + 2 * k = 1) :
    tiltedDiagonalBound a h k < (41 / 50 : ℝ) := by
  have h4 : 0 < 4 * a - h := by linarith only [ha0, hh1]
  have hcoef : (160 / 303 : ℝ) ≤ 2 * a / (4 * a - h) := by
    rw [le_div_iff₀ h4]
    linarith only [ha1, hh0]
  have hq : (41 / 99 + 17 / 100 : ℝ) < k + h / 2 := by
    linarith only [hk, hh0]
  rw [tiltedDiagonalBound_eq_width_tilt h4.ne' hksq]
  nlinarith only [mul_pos (sub_pos.mpr hq) (by linarith only [hk, hh0] :
    0 < k + h / 2 + (41 / 99 + 17 / 100 : ℝ)), mul_nonneg (sub_nonneg.mpr hcoef)
    (sq_nonneg (k + h / 2)), sq_nonneg (a - (k + 1))]

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
  have huv := hU.tilted_diagonal_parameters_mem ha0 hh0 hhhalf hl hr hleft hright
  have hD := hU.diagonalRoofDeficit_ge_tilt_loss ha0 (by linarith only [ha, hh1]) hl hr hleft
    hright haffine (by ring) (by ring) huv.1 huv.2
  have hscalar := tiltedDiagonalRelaxation_le_bound ha hh0 hh1
    sqrt_two_sub_one_bounds.1 sqrt_two_sub_one_bounds.2.1
    (diagonalRight U - 1) (diagonalLeft U - 1 + h)
  unfold tiltedDiagonalRelaxation at hscalar
  linarith only [hD, hscalar,
    hU.capScore_add_diagonalRoofDeficit_le ha0 hh0 hhhalf hl hr hleft hright hα0 hαL]

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
  have hksq := sqrt_two_sub_one_quadratic
  refine ⟨lt_of_not_ge fun h' => (hP.trans_lt (tiltedDiagonalBound_lt_of_large_tilt ha0 ha1 h'
    hh1 sqrt_two_sub_one_bounds.1 hksq)).not_ge hscore, ?_⟩
  rw [tiltedDiagonalBound_eq_width_tilt (by linarith only [ha0, hh1]) hksq,
    show Real.sqrt 2 - 1 + 1 = Real.sqrt 2 by ring] at hP
  rw [show 4 * a / (4 * a - h) = 2 * (2 * a / (4 * a - h)) by ring]
  linarith

end AmbidextrousSofa
