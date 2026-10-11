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
  convert Reference.hasDerivAt_if_le 0 (fun t => hasDerivAt_const t (0 : ℝ))
    (fun t => hasDerivAt_pow 2 t) (by norm_num) (by norm_num) x using 1
  · funext t
    split_ifs with ht <;> simp [ht, max_def]
  · split_ifs with hx <;> simp [hx, max_def]

theorem integral_positive_ramp_add (h a b : ℝ) :
    (∫ x in a..b, max (h + x) 0) = ((max (h + b) 0) ^ 2 - (max (h + a) 0) ^ 2) / 2 := by
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ => (max (h + t) 0) ^ 2 / 2) (max (h + x) 0) x := by
    convert ((hasDerivAt_positivePart_square (h + x)).comp x
      ((hasDerivAt_id x).const_add h)).div_const 2 using 1 <;> norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) a b), sub_div]

theorem integral_positive_ramp_sub (h a b : ℝ) :
    (∫ x in a..b, max (h - x) 0) = ((max (h - a) 0) ^ 2 - (max (h - b) 0) ^ 2) / 2 := by
  have hderiv (x : ℝ) : HasDerivAt (fun t : ℝ => -(max (h - t) 0) ^ 2 / 2) (max (h - x) 0) x := by
    convert ((hasDerivAt_positivePart_square (h - x)).comp x
      ((hasDerivAt_id x).const_sub h)).neg.div_const 2 using 1 <;> norm_num
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (Continuous.intervalIntegrable (by fun_prop) a b)]
  ring

theorem integral_positive_tent {a b d : ℝ} (had : a ≤ d) (hdb : d ≤ b) (h : ℝ) :
    (∫ x in a..b, max (h - |x - d|) 0) =
      (max h 0) ^ 2 - (max (h - (d - a)) 0) ^ 2 / 2 -
        (max (h - (b - d)) 0) ^ 2 / 2 := by
  have hc : Continuous (fun x : ℝ => max (h - |x - d|) 0) := by fun_prop
  have hl : ∫ x in a..d, max (h - |x - d|) 0 = ∫ x in a..d, max ((h - d) + x) 0 :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le had] at hx
      simp only [abs_of_nonpos (sub_nonpos.mpr hx.2)]; ring_nf
  have hr : ∫ x in d..b, max (h - |x - d|) 0 = ∫ x in d..b, max ((h + d) - x) 0 :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le hdb] at hx
      simp only [abs_of_nonneg (sub_nonneg.mpr hx.1)]; ring_nf
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a d)
    (hc.intervalIntegrable d b), hl, hr, integral_positive_ramp_add, integral_positive_ramp_sub]
  ring_nf

theorem integral_positive_tent_centered {C d : ℝ} (hd : d ∈ Icc (-C) C) (h : ℝ) :
    (∫ x in (-C)..C, max (h - |x - d|) 0) =
      (max h 0) ^ 2 - (max (h - C - d) 0) ^ 2 / 2 -
        (max (h - C + d) 0) ^ 2 / 2 := by
  rw [integral_positive_tent hd.1 hd.2]
  ring_nf

theorem min_symmetric_lines (h d x : ℝ) :
    min (h + d - x) (h - d + x) = h - |x - d| := by
  rw [abs_eq_max_neg, ← min_sub_sub_left]
  ring_nf

end AmbidextrousSofa
