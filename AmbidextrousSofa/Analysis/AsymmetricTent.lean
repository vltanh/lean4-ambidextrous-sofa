module

public import AmbidextrousSofa.Analysis.PositiveTent

@[expose] public section

/-!
# Finite increments of clipped affine tents

The integral of a complete positive asymmetric tent is its triangle area,
including the empty-tent case. Raising an additional floor can only
decrease a monotone wall increment. These elementary facts permit finite
parameter comparisons without differentiating a clipped integral.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The complete area of a positive asymmetric tent on any interval
containing its two zeros. Reversed zeros give the identically zero tent. -/
theorem integral_positive_asymmetric_tent_full {s t l r A B : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hAl : A ≤ l) (hrB : r ≤ B) :
    (∫ x in A..B, max (min (s * (x - l)) (t * (r - x))) 0) =
      s * t * (max (r - l) 0) ^ 2 / (2 * (s + t)) := by
  have hst : 0 < s + t := add_pos hs ht
  rcases le_total l r with hlr | hrl
  · set p := (s * l + t * r) / (s + t) with hpdef
    have hp : (s + t) * p = s * l + t * r := mul_div_cancel₀ _ hst.ne'
    have hlp : l ≤ p := by
      rw [le_div_iff₀ hst]; linarith only [mul_nonneg ht.le (sub_nonneg.mpr hlr)]
    have hpr : p ≤ r := by
      rw [div_le_iff₀ hst]; linarith only [mul_nonneg hs.le (sub_nonneg.mpr hlr)]
    have hc : Continuous fun x : ℝ => max (min (s * (x - l)) (t * (r - x))) 0 := by fun_prop
    have hleft : (∫ x in A..p, max (min (s * (x - l)) (t * (r - x))) 0) =
        ∫ x in A..p, s * max (-l + x) 0 := intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le (hAl.trans hlp)] at hx
      rw [min_eq_left (by linarith only [hp, mul_nonneg hst.le (sub_nonneg.mpr hx.2)]),
        mul_max_of_nonneg _ _ hs.le, mul_zero, neg_add_eq_sub]
    have hright : (∫ x in p..B, max (min (s * (x - l)) (t * (r - x))) 0) =
        ∫ x in p..B, t * max (r - x) 0 := intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le (hpr.trans hrB)] at hx
      rw [min_eq_right (by linarith only [hp, mul_nonneg hst.le (sub_nonneg.mpr hx.1)]),
        mul_max_of_nonneg _ _ ht.le, mul_zero]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable A p)
      (hc.intervalIntegrable p B), hleft, hright, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_positive_ramp_add, integral_positive_ramp_sub,
      max_eq_left (by linarith : 0 ≤ -l + p), max_eq_right (by linarith : -l + A ≤ 0),
      max_eq_left (sub_nonneg.mpr hpr), max_eq_right (sub_nonpos.mpr hrB),
      max_eq_left (sub_nonneg.mpr hlr), hpdef]
    field_simp
    ring
  · have h0 (x : ℝ) : max (min (s * (x - l)) (t * (r - x))) 0 = 0 := max_eq_right <| by
      rcases le_total x l with h | h
      · exact (min_le_left _ _).trans (mul_nonpos_of_nonneg_of_nonpos hs.le (by linarith))
      · exact (min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith))
    simp [h0, max_eq_right (sub_nonpos.mpr hrl)]

/-- The square of the positive part has its finite secant bounded by
twice its final positive height. -/
theorem positivePart_square_increment_le {a b : ℝ} (hab : a ≤ b) :
    (max b 0) ^ 2 - (max a 0) ^ 2 ≤ 2 * max b 0 * (b - a) := by
  rcases le_total b 0 with hb | hb
  · simp [max_eq_right hb, max_eq_right (hab.trans hb)]
  rcases le_total a 0 with ha | ha
  · rw [max_eq_left hb, max_eq_right ha]
    nlinarith only [sq_nonneg b, mul_nonpos_of_nonneg_of_nonpos hb ha]
  · rw [max_eq_left hb, max_eq_left ha]; nlinarith only [sq_nonneg (b - a)]

/-- An added zero floor can only reduce the increment of a tent above
a fixed wall. Subtracting that wall leaves an ordinary positive tent. -/
theorem wall_increment_le_shifted_tent {A B₀ B₁ L : ℝ} (hB : B₀ ≤ B₁) :
    max (max 0 (min A B₁)) L - max (max 0 (min A B₀)) L ≤
      max (min (A - L) (B₁ - L)) 0 - max (min (A - L) (B₀ - L)) 0 := by
  have := min_le_min_left A hB
  rw [min_sub_sub_right, min_sub_sub_right]
  grind

end AmbidextrousSofa
