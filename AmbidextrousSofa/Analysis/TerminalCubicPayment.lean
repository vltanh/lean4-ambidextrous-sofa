module

public import AmbidextrousSofa.Analysis.TerminalThreeSupports

@[expose] public section

/-!
# The exact weighted cubic payment for a late companion excess

The weighted error in the proper-terminal comparison is an ordinary
integral of the positive curvature excess. Its trigonometric kernel is
nonnegative before the selected prefix endpoint. A linear late-tail
envelope therefore pays a cubic amount, with all clipping retained.

The numerical allowance is proved by exact rational inequalities. The
cosine cut at `147/200` follows from the elementary quadratic cosine
bound and two double-angle identities. The late-tail envelope is a
hypothesis of the payment.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def terminalWeightedExcess (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in 0..θ, max (v t - 1) 0 *
    (Real.tan θ * Real.cos t - Real.sin t)

theorem integral_quadratic_tail_kernel (a b : ℝ) :
    (∫ t in a..b, (t - a) * (b - t)) = (b - a) ^ 3 / 6 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => (b - a) * (t - a) ^ 2 / 2 - (t - a) ^ 3 / 3)
      ((x - a) * (b - x)) x := by
    have hx := (hasDerivAt_id' x).sub_const a
    convert (((hx.pow 2).const_mul (b - a)).div_const 2).sub ((hx.pow 3).div_const 3) using 1
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun t : ℝ => (t - a) * (b - t)).intervalIntegrable a b)]
  ring

/-- The positive part makes the formula valid even when the excess has
not begun before the prefix ends. -/
theorem integral_positive_quadratic_tail_kernel {θ t₀ : ℝ}
    (hθ : 0 ≤ θ) (ht₀ : 0 ≤ t₀) :
    (∫ t in 0..θ, max (t - t₀) 0 * (θ - t)) =
      (max (θ - t₀) 0) ^ 3 / 6 := by
  have hc : Continuous (fun t : ℝ => max (t - t₀) 0 * (θ - t)) := by fun_prop
  -- The integrand vanishes before `t₀`.
  have hzero (c : ℝ) (hc0 : 0 ≤ c) (hct : c ≤ t₀) :
      (∫ t in 0..c, max (t - t₀) 0 * (θ - t)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) fun t ht => ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hc0] at ht
    simp [max_eq_right (show t - t₀ ≤ 0 by linarith [ht.2])]
  rcases le_total θ t₀ with hθt | htθ
  · rw [hzero θ hθ hθt, max_eq_right (sub_nonpos.mpr hθt)]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 t₀)
    (hc.intervalIntegrable t₀ θ), hzero t₀ ht₀ le_rfl, zero_add, max_eq_left (sub_nonneg.mpr htθ),
    ← integral_quadratic_tail_kernel]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le htθ] at ht
  simp [max_eq_left (sub_nonneg.mpr ht.1)]

theorem terminal_weight_kernel_eq {θ t : ℝ} (hcos : Real.cos θ ≠ 0) :
    Real.tan θ * Real.cos t - Real.sin t =
      Real.sin (θ - t) / Real.cos θ := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub]
  field_simp

theorem terminal_weight_kernel_bounds {θ t : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) (ht : t ∈ Icc 0 θ) :
    0 ≤ Real.tan θ * Real.cos t - Real.sin t ∧
      Real.tan θ * Real.cos t - Real.sin t ≤ (θ - t) / Real.cos θ := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθL⟩
  rw [terminal_weight_kernel_eq hc.ne']
  refine ⟨div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith [ht.2]) (by linarith [ht.1, Real.pi_pos])) hc.le, ?_⟩
  exact div_le_div_of_nonneg_right (Real.sin_le (by linarith [ht.2])) hc.le

/-- The analytic part of the cubic payment. The envelope is an
almost-everywhere density estimate, and no continuity of `v` is needed. -/
theorem terminalWeightedExcess_le_cubic {v : ℝ → ℝ} {θ t₀ K : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) (ht₀ : 0 ≤ t₀) (hK : 0 ≤ K)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan θ * Real.cos t - Real.sin t)) volume 0 θ)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (v t - 1) 0 ≤ K * max (t - t₀) 0) :
    terminalWeightedExcess v θ ≤ K * (max (θ - t₀) 0) ^ 3 / (6 * Real.cos θ) := by
  have hmono := intervalIntegral.integral_mono_ae_restrict hθ0 hint
    ((by fun_prop : Continuous fun t : ℝ => K / Real.cos θ * (max (t - t₀) 0 * (θ - t)))
      |>.intervalIntegrable 0 θ) <| by
    filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht htm
    obtain ⟨hk0, hk1⟩ := terminal_weight_kernel_bounds hθ0 hθL htm
    exact (mul_le_mul ht hk1 hk0 (mul_nonneg hK (le_max_right _ _))).trans_eq (by ring)
  rw [intervalIntegral.integral_const_mul, integral_positive_quadratic_tail_kernel hθ0 ht₀] at hmono
  exact hmono.trans_eq (by ring)

theorem terminalWeightedExcess_eq_zero_of_unit_prefix {v : ℝ → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hv : ∀ᵐ t ∂volume.restrict (Icc 0 θ), v t ≤ 1) :
    terminalWeightedExcess v θ = 0 := by
  refine (intervalIntegral.integral_congr_ae_restrict (g := fun _ => 0) ?_).trans (by simp)
  rw [uIoc_of_le hθ]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hv] with t ht
  simp [max_eq_right (sub_nonpos.2 ht)]

/-- The rational angular cut uses two exact cosine double-angle
identities and the universal quadratic cosine lower bound. -/
theorem terminal_cos_rational_cut : (37 / 50 : ℝ) < Real.cos (147 / 200) := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := (147 / 800 : ℝ))
  have h2 := Real.cos_two_mul (147 / 800 : ℝ)
  have h3 := Real.cos_two_mul (147 / 400 : ℝ)
  norm_num at h1 h2 h3
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)]

/-- The exact allowance from the late-tail envelope, for the complementary cotangent range. The
excess prefix is shorter than `7/40`, and the cosines of the prefix end and of `α` exceed `2/3`
and `3/25`. -/
theorem terminalWeightedExcess_lt_allowance_of_late_tail
    {v : ℝ → ℝ} {C T α : ℝ}
    (hCT : 0 ≤ C - T) (hCT1 : C - T ≤ 37 / 50)
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hk : (1 / 8 : ℝ) ≤ terminalSlope α)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan (Real.arcsin (C - T)) * Real.cos t - Real.sin t))
        volume 0 (Real.arcsin (C - T)))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.arcsin (C - T))),
      max (v t - 1) 0 ≤ (19 / 25 : ℝ) *
        max (t - (Real.pi / 2 - 91 / 100)) 0) :
    terminalWeightedExcess v (Real.arcsin (C - T)) <
      (39 / 4400 : ℝ) * Real.cos α := by
  have hq : (2 / 3 : ℝ) < Real.cos (Real.arcsin (C - T)) := by
    rw [Real.cos_arcsin, Real.lt_sqrt (by norm_num)]
    nlinarith only [hCT, hCT1]
  -- The excess starts at `π/2 - 91/100`, so the prefix has length less than `7/40`.
  have hℓ : max (Real.arcsin (C - T) - (Real.pi / 2 - 91 / 100)) 0 < 7 / 40 := by
    refine max_lt ?_ (by norm_num)
    have := (Real.arcsin_lt_iff_lt_sin' (x := C - T) (y := Real.pi / 2 - 147 / 200)
      ⟨by linarith [Real.pi_gt_three], by linarith⟩).2
      (by rw [Real.sin_pi_div_two_sub]; linarith [terminal_cos_rational_cut])
    linarith
  have hc : (3 / 25 : ℝ) < Real.cos α := by
    obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
    rw [terminalSlope, le_div_iff₀ hs] at hk
    nlinarith only [hk, hs, hc, Real.sin_sq_add_cos_sq α]
  refine (terminalWeightedExcess_le_cubic (t₀ := Real.pi / 2 - 91 / 100) (K := (19 / 25 : ℝ))
    (Real.arcsin_nonneg.mpr hCT) (Real.arcsin_lt_pi_div_two.mpr (by linarith))
    (by linarith [Real.pi_gt_three]) (by norm_num) hint hbound).trans_lt ?_
  have hpow := pow_lt_pow_left₀ hℓ (le_max_right _ _) (by norm_num : 3 ≠ 0)
  rw [div_lt_iff₀ (by positivity)]
  linarith only [hpow, hc, hq, mul_pos (sub_pos.2 hc) (sub_pos.2 hq)]

end AmbidextrousSofa
