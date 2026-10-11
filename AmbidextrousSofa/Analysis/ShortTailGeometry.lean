module

public import AmbidextrousSofa.Analysis.ShortWidthPayment

@[expose] public section

/-!
# Positions and companion inequalities for the two short-width tails

The high-score diagonal stability bounds place both extra triangles on
their own side of the diagonal apex. The two companion inequalities keep
the actual lower middle height on its original side. Only the outer
tips can leave the middle window, with a common explicit length bound.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def shortLeftTailHeight (k h δ : ℝ) : ℝ := max ((2 / 25) - (1 - k) * h - δ) 0

def shortRightTailHeight (δ : ℝ) : ℝ := max ((2 / 25) - δ) 0

theorem short_left_peak_height_nonneg {k h : ℝ} (hk : 2 / 5 < k)
    (hh0 : 0 ≤ h) (hh1 : h < 1 / 23) : 0 ≤ (2 / 25 : ℝ) - (1 - k) * h := by
  nlinarith [mul_nonneg (sub_nonneg.2 hk.le) hh0]

theorem short_left_tail_geometry {a h k u v δ : ℝ}
    (hk0 : 2 / 5 < k) (hk1 : k < 169 / 408) (hksq : k ^ 2 + 2 * k = 1)
    (hh0 : 0 ≤ h) (hh1 : h < 1 / 23) (hδ : 0 ≤ δ)
    (hv : v - a / 2 < 323 / 1000 + h / 4)
    (hm : 16 / 25 < (u + v) / 2 - h / 4)
    (hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2)) :
    k - v + h ∈ Icc (-a / 2) (a / 2) ∧
      k - v + h + shortLeftTailHeight k h δ / (1 - k) < (u - v + h) / 2 ∧
      nearDiagonalNorm k + shortLeftTailHeight k h δ / k ≤ u + v - h ∧
      shortLeftTailHeight k h δ / k - (k - v + h + a / 2) ≤
        shortOuterTipAllowance k + h / 4 := by
  have hk : 0 < k := by linarith
  have hj : 0 < 1 - k := by linarith
  obtain ⟨-, hnorm, hpeak, -⟩ := short_nearDiagonal_constants hk0 hk1 hksq
  have hE0 : 0 ≤ shortLeftTailHeight k h δ := le_max_right _ _
  have hE : shortLeftTailHeight k h δ ≤ 2 / 25 - (1 - k) * h :=
    max_le (by linarith) (short_left_peak_height_nonneg hk0 hh0 hh1)
  have hEj : shortLeftTailHeight k h δ / (1 - k) ≤ 2 / 25 / (1 - k) - h := by
    rw [div_le_iff₀ hj]
    linarith [div_mul_cancel₀ (2 / 25 : ℝ) hj.ne']
  have hEk : shortLeftTailHeight k h δ / k ≤ 2 / 25 / k - (k + 1) * h := by
    rw [div_le_iff₀ hk]
    linarith [div_mul_cancel₀ (2 / 25 : ℝ) hk.ne', congrArg (· * h) hksq]
  refine ⟨⟨by linarith, by linarith [div_nonneg hE0 hj.le, hd.2]⟩, by linarith,
    by nlinarith [mul_nonneg (show 0 ≤ k + 1 / 2 by linarith) hh0], ?_⟩
  unfold shortOuterTipAllowance
  linarith [div_le_div_of_nonneg_right (hE.trans (sub_le_self _ (mul_nonneg hj.le hh0))) hk.le]

theorem short_right_tail_geometry {a h k u v δ : ℝ}
    (hk0 : 2 / 5 < k) (hk1 : k < 169 / 408) (hksq : k ^ 2 + 2 * k = 1)
    (hh0 : 0 ≤ h) (hh1 : h < 1 / 23) (hδ : 0 ≤ δ)
    (hu : u - a / 2 < 323 / 1000 + h / 4)
    (hm : 16 / 25 < (u + v) / 2 - h / 4)
    (hd : (u - v + h) / 2 ∈ Icc (-a / 2) (a / 2)) :
    k - u ∈ Icc (-a / 2) (a / 2) ∧
      k - u + shortRightTailHeight δ / (1 - k) < -(u - v + h) / 2 ∧
      nearDiagonalNorm k + shortRightTailHeight δ / k ≤ u + v - k * h ∧
      shortRightTailHeight δ / k - (k - u + a / 2) ≤ shortOuterTipAllowance k + h / 4 := by
  have hk : 0 < k := by linarith
  have hj : 0 < 1 - k := by linarith
  obtain ⟨-, hnorm, hpeak, -⟩ := short_nearDiagonal_constants hk0 hk1 hksq
  have hE0 : 0 ≤ shortRightTailHeight δ := le_max_right _ _
  have hE : shortRightTailHeight δ ≤ 2 / 25 := max_le (by linarith) (by norm_num)
  have hEj := div_le_div_of_nonneg_right hE hj.le
  have hEk := div_le_div_of_nonneg_right hE hk.le
  refine ⟨⟨by linarith, by linarith [div_nonneg hE0 hj.le, hd.1]⟩, by linarith,
    by nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - k by linarith) hh0], ?_⟩
  unfold shortOuterTipAllowance
  linarith

/-- At every point before a tail's inner tip, its actual companion
lower bound dominates the proposed extra line. -/
theorem near_tail_companion_bound {k E z A : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hksq : k ^ 2 + 2 * k = 1) (hA : E / k ≤ A)
    (hz : z ≤ E / (1 - k)) : E + k * z ≤ (A - z) / k := by
  have hshort : (1 - k) * z ≤ E := by
    have h := (le_div_iff₀ (sub_pos.mpr hk1)).mp hz
    nlinarith only [h]
  rw [div_eq_mul_one_div, diagonal_offset_inv hk hksq] at hA
  rw [le_div_iff₀ hk]
  nlinarith only [hA, hshort, congrArg (· * z) hksq]

end AmbidextrousSofa
