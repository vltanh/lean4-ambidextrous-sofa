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
  by_cases hlr : l ≤ r
  · let p := (s * l + t * r) / (s + t)
    have hst : 0 < s + t := add_pos hs ht
    have hp : (s + t) * p = s * l + t * r := mul_div_cancel₀ _ (ne_of_gt hst)
    have hlp : l ≤ p := by
      apply (le_div_iff₀ hst).2
      nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr hlr)]
    have hpr : p ≤ r := by
      apply (div_le_iff₀ hst).2
      nlinarith only [mul_nonneg hs.le (sub_nonneg.mpr hlr)]
    have hsplit : s * (p - l) = t * (r - p) := by nlinarith only [hp]
    have hc : Continuous (fun x : ℝ => max (min (s * (x - l)) (t * (r - x))) 0) := by
      fun_prop
    have hleft : (∫ x in A..p, max (min (s * (x - l)) (t * (r - x))) 0) =
        s * (p - l) ^ 2 / 2 := by
      calc
        _ = ∫ x in A..p, s * max (-l + x) 0 := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le (hAl.trans hlp)]
          intro x hx
          have hlines : s * (x - l) ≤ t * (r - x) := by
            nlinarith only [hsplit, mul_nonneg hst.le (sub_nonneg.mpr hx.2)]
          rw [min_eq_left hlines, show -l + x = x - l by ring]
          simpa only [mul_zero] using (mul_max_of_nonneg (x - l) 0 hs.le).symm
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, integral_positive_ramp_add,
            max_eq_left (show 0 ≤ -l + p by linarith),
            max_eq_right (show -l + A ≤ 0 by linarith)]
          ring
    have hright : (∫ x in p..B, max (min (s * (x - l)) (t * (r - x))) 0) =
        t * (r - p) ^ 2 / 2 := by
      calc
        _ = ∫ x in p..B, t * max (r - x) 0 := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le (hpr.trans hrB)]
          intro x hx
          have hlines : t * (r - x) ≤ s * (x - l) := by
            nlinarith only [hsplit, mul_nonneg hst.le (sub_nonneg.mpr hx.1)]
          rw [min_eq_right hlines]
          simpa only [mul_zero] using (mul_max_of_nonneg (r - x) 0 ht.le).symm
        _ = _ := by
          rw [intervalIntegral.integral_const_mul, integral_positive_ramp_sub,
            max_eq_left (sub_nonneg.mpr hpr), max_eq_right (sub_nonpos.mpr hrB)]
          ring
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable A p) (hc.intervalIntegrable p B), hleft, hright,
      max_eq_left (sub_nonneg.mpr hlr)]
    dsimp [p]
    field_simp [ne_of_gt hst] <;> ring
  · have hrl : r ≤ l := le_of_not_ge hlr
    have hzero : (fun x : ℝ => max (min (s * (x - l)) (t * (r - x))) 0) =
        (fun _ : ℝ => 0) := by
      funext x
      apply max_eq_right
      by_cases hxl : x ≤ l
      · exact (min_le_left _ _).trans
          (mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.mpr hxl))
      · have hrx : r ≤ x := hrl.trans (le_of_not_ge hxl)
        exact (min_le_right _ _).trans
          (mul_nonpos_of_nonneg_of_nonpos ht.le (sub_nonpos.mpr hrx))
    rw [hzero, intervalIntegral.integral_zero, max_eq_right (sub_nonpos.mpr hrl)]
    ring

/-- The square of the positive part has its finite secant bounded by
twice its final positive height. -/
theorem positivePart_square_increment_le {a b : ℝ} (hab : a ≤ b) :
    (max b 0) ^ 2 - (max a 0) ^ 2 ≤ 2 * max b 0 * (b - a) := by
  by_cases hb : b ≤ 0
  · rw [max_eq_right hb, max_eq_right (hab.trans hb)]
    norm_num
  · have hb0 : 0 ≤ b := le_of_not_ge hb
    rw [max_eq_left hb0]
    by_cases ha : a ≤ 0
    · rw [max_eq_right ha]
      nlinarith only [sq_nonneg b, mul_nonpos_of_nonneg_of_nonpos hb0 ha]
    · rw [max_eq_left (le_of_not_ge ha)]
      nlinarith only [sq_nonneg (b - a)]

/-- Increasing a fixed floor reduces any increasing signal's finite
increment after taking the maximum. -/
theorem max_increment_le_of_floor_le {L D a b : ℝ} (hLD : L ≤ D) (hab : a ≤ b) :
    max D b - max D a ≤ max L b - max L a := by
  by_cases hbD : b ≤ D
  · rw [max_eq_left hbD, max_eq_left (hab.trans hbD), sub_self]
    exact sub_nonneg.mpr (max_le_max le_rfl hab)
  · have hDb : D ≤ b := le_of_not_ge hbD
    by_cases hDa : D ≤ a
    · rw [max_eq_right hDb, max_eq_right hDa, max_eq_right (hLD.trans hDb),
        max_eq_right (hLD.trans hDa)]
    · have haD : a ≤ D := le_of_not_ge hDa
      have hmax : max L a ≤ D := max_le hLD haD
      rw [max_eq_right hDb, max_eq_left haD, max_eq_right (hLD.trans hDb)]
      linarith only [hmax]

/-- An added zero floor can only reduce the increment of a tent above
a fixed wall. Subtracting that wall leaves an ordinary positive tent. -/
theorem wall_increment_le_shifted_tent {A B₀ B₁ L : ℝ} (hB : B₀ ≤ B₁) :
    max (max 0 (min A B₁)) L - max (max 0 (min A B₀)) L ≤
      max (min (A - L) (B₁ - L)) 0 - max (min (A - L) (B₀ - L)) 0 := by
  have hshift (B : ℝ) : max L (min A B) = L + max (min (A - L) (B - L)) 0 := by
    rw [min_sub_sub_right]
    by_cases h : L ≤ min A B
    · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
      ring
    · have h' : min A B ≤ L := le_of_not_ge h
      rw [max_eq_left h', max_eq_right (sub_nonpos.mpr h')]
      ring
  have h := max_increment_le_of_floor_le (L := L) (D := max 0 L)
    (le_max_right 0 L) (min_le_min le_rfl hB)
  have horder (B : ℝ) : max (max 0 (min A B)) L = max (max 0 L) (min A B) := by
    ac_rfl
  rw [← horder B₁, ← horder B₀, hshift B₁, hshift B₀] at h
  linarith only [h]

end AmbidextrousSofa
