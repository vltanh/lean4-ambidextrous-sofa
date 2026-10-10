module

public import AmbidextrousSofa.Analysis.DiagonalCutTriangles

@[expose] public section

/-!
# Exact one-sided clipping of an extra niche triangle

Only the outer tip of each added niche triangle may leave the middle
window. Its omitted area is the ordinary triangular area with slope k.
This calculation retains the positive part and covers zero-height tails.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem affineCutTriangle_eq_zero_of_right {k δ p x : ℝ}
    (hk1 : k < 1) (hx : p + δ / (1 - k) ≤ x) : affineCutTriangle k δ p x = 0 := by
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hδ : δ ≤ (1 - k) * (x - p) := by
    have hdiv : δ / (1 - k) ≤ x - p := by linarith
    have h := (div_le_iff₀ hj).mp hdiv
    nlinarith only [h]
  exact max_eq_right ((min_le_right _ _).trans (by linarith))

theorem affineCutTriangle_eq_zero_of_height_nonpos {k δ : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hδ : δ ≤ 0) (p x : ℝ) :
    affineCutTriangle k δ p x = 0 := by
  apply max_eq_right
  by_cases hx : x ≤ p
  · exact (min_le_left _ _).trans (by
      have h := mul_nonpos_of_nonneg_of_nonpos hk0 (sub_nonpos.mpr hx)
      linarith)
  · exact (min_le_right _ _).trans (by
      have h := mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr (le_of_not_ge hx))
      linarith)

theorem affineCutTriangle_eq_positive_excess (k δ p x : ℝ) :
    affineCutTriangle k δ p x =
      max (δ + k * (x - p) - max (x - p) 0) 0 := by
  unfold affineCutTriangle
  rw [min_eq_left_sub_positive]
  rw [show (δ + k * (x - p)) - (δ - (1 - k) * (x - p)) = x - p by ring]

theorem affineCutTriangle_add_floor_le {k δ p x n : ℝ}
    (hfloor : max (x - p) 0 ≤ n) (hline : δ + k * (x - p) ≤ n) :
    max (x - p) 0 + affineCutTriangle k δ p x ≤ n := by
  rw [affineCutTriangle_eq_positive_excess]
  have hbound : max (δ + k * (x - p) - max (x - p) 0) 0 ≤ n - max (x - p) 0 :=
    max_le (by linarith) (sub_nonneg.mpr hfloor)
  linarith

theorem integral_affineCutTriangle_clipped_left {k δ p A B : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hδ : 0 ≤ δ)
    (hAp : A ≤ p) (hpB : p ≤ B) (hright : δ ≤ (1 - k) * (B - p)) :
    (∫ x in A..B, affineCutTriangle k δ p x) =
      δ ^ 2 / (2 * k * (1 - k)) -
        k / 2 * (max (δ / k - (p - A)) 0) ^ 2 := by
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hc := continuous_affineCutTriangle k δ p
  have hL : (∫ x in A..p, affineCutTriangle k δ p x) =
      δ ^ 2 / (2 * k) - k / 2 * (max (δ / k - (p - A)) 0) ^ 2 := by
    calc
      _ = ∫ x in A..p, k * max (δ / k - p + x) 0 := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hAp]
        intro x hx
        unfold affineCutTriangle
        rw [min_eq_left (by nlinarith only [hx.2] :
          δ + k * (x - p) ≤ δ - (1 - k) * (x - p))]
        have heq : δ + k * (x - p) = k * (δ / k - p + x) := by
          field_simp [hk.ne'] <;> ring
        rw [heq]
        simpa only [mul_zero] using (mul_max_of_nonneg (δ / k - p + x) 0 hk.le).symm
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_positive_ramp_add,
          show δ / k - p + p = δ / k by ring,
          max_eq_left (div_nonneg hδ hk.le),
          show δ / k - p + A = δ / k - (p - A) by ring]
        field_simp [hk.ne'] <;> ring
  have hR : (∫ x in p..B, affineCutTriangle k δ p x) = δ ^ 2 / (2 * (1 - k)) := by
    calc
      _ = ∫ x in p..B, (1 - k) * max (p + δ / (1 - k) - x) 0 := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hpB]
        intro x hx
        unfold affineCutTriangle
        rw [min_eq_right (by nlinarith only [hx.1] :
          δ - (1 - k) * (x - p) ≤ δ + k * (x - p))]
        have heq : δ - (1 - k) * (x - p) = (1 - k) * (p + δ / (1 - k) - x) := by
          field_simp [hj.ne'] <;> ring
        rw [heq]
        simpa only [mul_zero] using
          (mul_max_of_nonneg (p + δ / (1 - k) - x) 0 hj.le).symm
      _ = _ := by
        have hzero : p + δ / (1 - k) - B ≤ 0 := by
          have h := (div_le_iff₀ hj).mpr hright
          linarith
        rw [intervalIntegral.integral_const_mul, integral_positive_ramp_sub,
          show p + δ / (1 - k) - p = δ / (1 - k) by ring,
          max_eq_left (div_nonneg hδ hj.le), max_eq_right hzero]
        field_simp [hj.ne'] <;> ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable A p) (hc.intervalIntegrable p B), hL, hR]
  field_simp [hk.ne', hj.ne'] <;> ring

theorem integral_affineCutTriangle_ge_of_outer_tip_bound {k δ p A B L : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hδ : 0 ≤ δ)
    (hAp : A ≤ p) (hpB : p ≤ B) (hright : δ ≤ (1 - k) * (B - p))
    (hL : 0 ≤ L) (hclip : δ / k - (p - A) ≤ L) :
    δ ^ 2 / (2 * k * (1 - k)) - k / 2 * L ^ 2 ≤
      ∫ x in A..B, affineCutTriangle k δ p x := by
  rw [integral_affineCutTriangle_clipped_left hk hk1 hδ hAp hpB hright]
  have hmax : max (δ / k - (p - A)) 0 ≤ L := max_le hclip hL
  have hsquare : (max (δ / k - (p - A)) 0) ^ 2 ≤ L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmax)
      (add_nonneg hL (le_max_right (δ / k - (p - A)) 0))]
  have hprod := mul_nonneg (div_nonneg hk.le (by norm_num : (0 : ℝ) ≤ 2))
    (sub_nonneg.mpr hsquare)
  linarith

theorem positive_deficit_square_payment {η : ℝ} (hη : 0 ≤ η) (δ : ℝ) :
    η ^ 2 / 2 ≤ δ ^ 2 + (max (η - δ) 0) ^ 2 := by
  by_cases hδ : δ ≤ η
  · rw [max_eq_left (sub_nonneg.mpr hδ)]
    nlinarith [sq_nonneg (2 * δ - η)]
  · rw [max_eq_right (by linarith [le_of_not_ge hδ] : η - δ ≤ 0)]
    have hprod := mul_nonneg (show 0 ≤ δ - η by linarith [le_of_not_ge hδ])
      (show 0 ≤ δ + η by linarith [le_of_not_ge hδ])
    nlinarith [sq_nonneg η]

end AmbidextrousSofa
