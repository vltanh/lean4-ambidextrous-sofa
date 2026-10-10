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
  have hprod := mul_nonneg (show 0 ≤ k - 2 / 5 by linarith) hh0
  nlinarith

theorem shortLeftTailHeight_bounds {k h δ : ℝ} (hk0 : 2 / 5 < k) (hk1 : k < 1)
    (hh0 : 0 ≤ h) (hh1 : h < 1 / 23) (hδ : 0 ≤ δ) :
    0 ≤ shortLeftTailHeight k h δ ∧
      shortLeftTailHeight k h δ ≤ (2 / 25) - (1 - k) * h ∧
      shortLeftTailHeight k h δ ≤ 2 / 25 := by
  have hη := short_left_peak_height_nonneg hk0 hh0 hh1
  have hbound : shortLeftTailHeight k h δ ≤ (2 / 25) - (1 - k) * h :=
    max_le (by linarith) hη
  refine ⟨le_max_right _ _, hbound, ?_⟩
  exact hbound.trans (by nlinarith [mul_nonneg (sub_pos.mpr hk1).le hh0])

theorem shortRightTailHeight_bounds {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ shortRightTailHeight δ ∧ shortRightTailHeight δ ≤ 2 / 25 :=
  ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩

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
  have hklt : k < 1 := by linarith
  have hj : 0 < 1 - k := sub_pos.mpr hklt
  obtain ⟨_, hnorm, hpeak, _⟩ := short_nearDiagonal_constants hk0 hk1 hksq
  obtain ⟨hE0, hEη, hEmax⟩ := shortLeftTailHeight_bounds hk0 hklt hh0 hh1 hδ
  have hEdiv : shortLeftTailHeight k h δ / (1 - k) ≤ (2 / 25) / (1 - k) - h := by
    calc
      _ ≤ ((2 / 25) - (1 - k) * h) / (1 - k) := div_le_div_of_nonneg_right hEη hj.le
      _ = _ := by field_simp [hj.ne'] <;> ring
  have hend : k - v + h + shortLeftTailHeight k h δ / (1 - k) < (u - v + h) / 2 := by
    linarith
  have hratio : (1 - k) / k = k + 1 := by
    apply (div_eq_iff hk.ne').mpr
    nlinarith
  have hEk : shortLeftTailHeight k h δ / k ≤ (2 / 25) / k - (k + 1) * h := by
    calc
      _ ≤ ((2 / 25) - (1 - k) * h) / k := div_le_div_of_nonneg_right hEη hk.le
      _ = (2 / 25) / k - ((1 - k) / k) * h := by ring
      _ = _ := by rw [hratio]
  have hcomp : nearDiagonalNorm k + shortLeftTailHeight k h δ / k ≤ u + v - h := by
    have hprod := mul_nonneg (show 0 ≤ k + 1 / 2 by linarith) hh0
    nlinarith
  have hmaxk := div_le_div_of_nonneg_right hEmax hk.le
  refine ⟨⟨by linarith, ?_⟩, hend, hcomp, ?_⟩
  · linarith [div_nonneg hE0 hj.le, hd.2]
  · unfold shortOuterTipAllowance
    linarith

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
  have hklt : k < 1 := by linarith
  have hj : 0 < 1 - k := sub_pos.mpr hklt
  obtain ⟨_, hnorm, hpeak, _⟩ := short_nearDiagonal_constants hk0 hk1 hksq
  obtain ⟨hE0, hEmax⟩ := shortRightTailHeight_bounds hδ
  have hEdiv := div_le_div_of_nonneg_right hEmax hj.le
  have hend : k - u + shortRightTailHeight δ / (1 - k) < -(u - v + h) / 2 := by
    linarith
  have hEk := div_le_div_of_nonneg_right hEmax hk.le
  have hcomp : nearDiagonalNorm k + shortRightTailHeight δ / k ≤ u + v - k * h := by
    have hprod := mul_nonneg (show 0 ≤ 1 / 2 - k by linarith) hh0
    nlinarith
  refine ⟨⟨by linarith, ?_⟩, hend, hcomp, ?_⟩
  · linarith [div_nonneg hE0 hj.le, hd.1]
  · unfold shortOuterTipAllowance
    linarith

/-- At every point before a tail's inner tip, its actual companion
lower bound dominates the proposed extra line. -/
theorem near_tail_companion_bound {k E z A : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hksq : k ^ 2 + 2 * k = 1) (hA : E / k ≤ A)
    (hz : z ≤ E / (1 - k)) : E + k * z ≤ (A - z) / k := by
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hshort : (1 - k) * z ≤ E := by
    have h := (le_div_iff₀ hj).mp hz
    nlinarith only [h]
  have hdiv : E / k = (k + 2) * E := by
    calc
      _ = (1 / k) * E := by ring
      _ = _ := by rw [diagonal_offset_inv hk hksq]
  rw [hdiv] at hA
  have hscale := congrArg (fun w : ℝ => w * z) hksq
  apply (le_div_iff₀ hk).mpr
  nlinarith only [hA, hshort, hscale]

end AmbidextrousSofa
