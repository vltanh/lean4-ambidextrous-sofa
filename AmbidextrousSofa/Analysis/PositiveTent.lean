module

public import AmbidextrousSofa.Reference.Support
public import AmbidextrousSofa.Geometry.BarrierAnalysis

@[expose] public section

/-!
# Exact integrals of positive tents and ramps

Squaring the positive part removes the derivative corner at zero. Its
ordinary derivative gives exact formulas for clipped affine ramps and for
the two-ray tent on any interval containing its apex. These formulas retain
both tails; an absent tail is removed only after its sign is proved.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem hasDerivAt_positivePart_square (x : ℝ) :
    HasDerivAt (fun t : ℝ => (max t 0) ^ 2) (2 * max x 0) x := by
  have hquad (t : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2) (2 * t) t := by
    simpa only [pow_one, mul_one] using (hasDerivAt_id t).pow 2
  have h := Reference.hasDerivAt_if_le 0 (fun t => hasDerivAt_const t (0 : ℝ)) hquad
    (by norm_num) (by norm_num) x
  have hfun : (fun t : ℝ => if t ≤ 0 then 0 else t ^ 2) =
      (fun t : ℝ => (max t 0) ^ 2) := by
    funext t
    by_cases ht : t ≤ 0
    · simp only [if_pos ht, max_eq_right ht, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    · simp only [if_neg ht, max_eq_left (le_of_not_ge ht)]
  rw [hfun] at h
  by_cases hx : x ≤ 0
  · simpa only [if_pos hx, max_eq_right hx, mul_zero] using h
  · simpa only [if_neg hx, max_eq_left (le_of_not_ge hx)] using h

theorem integral_positive_ramp_add (h a b : ℝ) :
    (∫ x in a..b, max (h + x) 0) = ((max (h + b) 0) ^ 2 - (max (h + a) 0) ^ 2) / 2 := by
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ => (max (h + t) 0) ^ 2 / 2)
      (max (h + x) 0) x := by
    have hx := (hasDerivAt_positivePart_square (h + x)).comp x
      ((hasDerivAt_const x h).add (hasDerivAt_id x))
    convert hx.div_const 2 using 1 <;> norm_num <;> ring
  have hc : Continuous (fun x : ℝ => max (h + x) 0) := by fun_prop
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) (hc.intervalIntegrable a b)
  simpa only [sub_div] using heq

theorem integral_positive_ramp_sub (h a b : ℝ) :
    (∫ x in a..b, max (h - x) 0) = ((max (h - a) 0) ^ 2 - (max (h - b) 0) ^ 2) / 2 := by
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ => -(max (h - t) 0) ^ 2 / 2)
      (max (h - x) 0) x := by
    have hx := (hasDerivAt_positivePart_square (h - x)).comp x
      ((hasDerivAt_const x h).sub (hasDerivAt_id x))
    convert hx.neg.div_const 2 using 1 <;> norm_num <;> ring
  have hc : Continuous (fun x : ℝ => max (h - x) 0) := by fun_prop
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) (hc.intervalIntegrable a b)
  calc
    _ = -(max (h - b) 0) ^ 2 / 2 - -(max (h - a) 0) ^ 2 / 2 := heq
    _ = _ := by ring

theorem integral_positive_tent {a b d : ℝ} (had : a ≤ d) (hdb : d ≤ b) (h : ℝ) :
    (∫ x in a..b, max (h - |x - d|) 0) =
      (max h 0) ^ 2 - (max (h - (d - a)) 0) ^ 2 / 2 -
        (max (h - (b - d)) 0) ^ 2 / 2 := by
  have hc : Continuous (fun x : ℝ => max (h - |x - d|) 0) := by fun_prop
  have hleft : (∫ x in a..d, max (h - |x - d|) 0) =
      (∫ x in a..d, max ((h - d) + x) 0) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le had]
    intro x hx
    rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
    congr 1
    ring
  have hright : (∫ x in d..b, max (h - |x - d|) 0) =
      (∫ x in d..b, max ((h + d) - x) 0) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hdb]
    intro x hx
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    congr 1
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a d) (hc.intervalIntegrable d b), hleft, hright,
    integral_positive_ramp_add, integral_positive_ramp_sub]
  rw [sub_add_cancel, add_sub_cancel_right,
    show h - d + a = h - (d - a) by ring,
    show h + d - b = h - (b - d) by ring]
  ring

theorem integral_positive_tent_centered {C d : ℝ} (hd : d ∈ Icc (-C) C) (h : ℝ) :
    (∫ x in (-C)..C, max (h - |x - d|) 0) =
      (max h 0) ^ 2 - (max (h - C - d) 0) ^ 2 / 2 -
        (max (h - C + d) 0) ^ 2 / 2 := by
  rw [integral_positive_tent hd.1 hd.2]
  rw [show h - (d - -C) = h - C - d by ring,
    show h - (C - d) = h - C + d by ring]

theorem min_symmetric_lines (h d x : ℝ) :
    min (h + d - x) (h - d + x) = h - |x - d| := by
  by_cases hx : x ≤ d
  · rw [min_eq_right (by linarith), abs_of_nonpos (sub_nonpos.mpr hx)]
    ring
  · rw [min_eq_left (by linarith), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hx))]
    ring

end AmbidextrousSofa
