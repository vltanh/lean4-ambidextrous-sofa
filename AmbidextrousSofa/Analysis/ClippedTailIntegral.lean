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
  have := (div_le_iff₀' (sub_pos.mpr hk1)).mp (le_sub_iff_add_le'.mpr hx)
  exact max_eq_right ((min_le_right _ _).trans (by linarith))

theorem affineCutTriangle_eq_zero_of_height_nonpos {k δ : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hδ : δ ≤ 0) (p x : ℝ) :
    affineCutTriangle k δ p x = 0 := by
  refine max_eq_right ?_
  rcases le_total x p with hx | hx
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem affineCutTriangle_add_floor_le {k δ p x n : ℝ}
    (hfloor : max (x - p) 0 ≤ n) (hline : δ + k * (x - p) ≤ n) :
    max (x - p) 0 + affineCutTriangle k δ p x ≤ n := by
  rw [affineCutTriangle, min_eq_left_sub_positive,
    show δ + k * (x - p) - (δ - (1 - k) * (x - p)) = x - p by ring]
  exact le_sub_iff_add_le'.mp (max_le (by linarith) (sub_nonneg.mpr hfloor))

theorem integral_affineCutTriangle_clipped_left {k δ p A B : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hδ : 0 ≤ δ)
    (hAp : A ≤ p) (hpB : p ≤ B) (hright : δ ≤ (1 - k) * (B - p)) :
    (∫ x in A..B, affineCutTriangle k δ p x) =
      δ ^ 2 / (2 * k * (1 - k)) -
        k / 2 * (max (δ / k - (p - A)) 0) ^ 2 := by
  have hj : 0 < 1 - k := sub_pos.mpr hk1
  have hc := continuous_affineCutTriangle k δ p
  have hL : ∀ x ∈ uIcc A p, affineCutTriangle k δ p x = k * max (δ / k - p + x) 0 := by
    intro x hx
    rw [uIcc_of_le hAp] at hx
    rw [affineCutTriangle, min_eq_left (by linarith [hx.2]), mul_max_of_nonneg _ _ hk.le, mul_zero]
    congr 1
    field_simp
    ring
  have hR : ∀ x ∈ uIcc p B,
      affineCutTriangle k δ p x = (1 - k) * max (p + δ / (1 - k) - x) 0 := by
    intro x hx
    rw [uIcc_of_le hpB] at hx
    rw [affineCutTriangle, min_eq_right (by linarith [hx.1]), mul_max_of_nonneg _ _ hj.le,
      mul_zero]
    congr 1
    field_simp
    ring
  have hzero : p + δ / (1 - k) - B ≤ 0 := by linarith [(div_le_iff₀' hj).mpr hright]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable A p)
    (hc.intervalIntegrable p B), intervalIntegral.integral_congr hL,
    intervalIntegral.integral_congr hR, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_positive_ramp_add, integral_positive_ramp_sub,
    sub_add_cancel, add_sub_cancel_left, max_eq_left (div_nonneg hδ hk.le),
    max_eq_left (div_nonneg hδ hj.le), max_eq_right hzero,
    show δ / k - p + A = δ / k - (p - A) by ring]
  field_simp
  ring

theorem integral_affineCutTriangle_ge_of_outer_tip_bound {k δ p A B L : ℝ}
    (hk : 0 < k) (hk1 : k < 1) (hδ : 0 ≤ δ)
    (hAp : A ≤ p) (hpB : p ≤ B) (hright : δ ≤ (1 - k) * (B - p))
    (hL : 0 ≤ L) (hclip : δ / k - (p - A) ≤ L) :
    δ ^ 2 / (2 * k * (1 - k)) - k / 2 * L ^ 2 ≤
      ∫ x in A..B, affineCutTriangle k δ p x := by
  rw [integral_affineCutTriangle_clipped_left hk hk1 hδ hAp hpB hright]
  gcongr
  exact max_le hclip hL

theorem positive_deficit_square_payment {η : ℝ} (hη : 0 ≤ η) (δ : ℝ) :
    η ^ 2 / 2 ≤ δ ^ 2 + (max (η - δ) 0) ^ 2 := by
  rcases le_total δ η with hδ | hδ
  · rw [max_eq_left (sub_nonneg.mpr hδ)]
    nlinarith [sq_nonneg (2 * δ - η)]
  · rw [max_eq_right (by linarith : η - δ ≤ 0)]
    nlinarith

end AmbidextrousSofa
