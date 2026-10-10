import AmbidextrousSofa.Analysis.TerminalThreeSupports

/-!
# The exact weighted cubic payment for a late companion excess

The weighted error in the proper-terminal comparison is an ordinary
integral of the positive curvature excess. Its trigonometric kernel is
nonnegative before the selected prefix endpoint. A linear late-tail
envelope therefore pays a cubic amount, with all clipping retained.

The numerical allowance is proved by exact rational inequalities. The
cosine cut at `147/200` follows from the elementary quadratic cosine
bound and two double-angle identities. The result does not assert the
late-tail envelope for an actual maximizer; that source-dynamics
obligation remains separate from this analytic payment.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def terminalWeightedExcess (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in 0..θ, max (v t - 1) 0 *
    (Real.tan θ * Real.cos t - Real.sin t)

theorem integral_quadratic_tail_kernel (a b : ℝ) :
    (∫ t in a..b, (t - a) * (b - t)) = (b - a) ^ 3 / 6 := by
  have hd (x : ℝ) :
      HasDerivAt (fun t : ℝ => (b - a) * (t - a) ^ 2 / 2 - (t - a) ^ 3 / 3)
        ((x - a) * (b - x)) x := by
    have hx := (hasDerivAt_id x).sub_const a
    convert ((((hx.pow 2).const_mul (b - a)).div_const 2).sub
      ((hx.pow 3).div_const 3)) using 1 <;> norm_num <;> ring
  have hc : Continuous (fun t : ℝ => (t - a) * (b - t)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hc.intervalIntegrable a b)
  calc
    _ = ((b - a) * (b - a) ^ 2 / 2 - (b - a) ^ 3 / 3) -
        ((b - a) * (a - a) ^ 2 / 2 - (a - a) ^ 3 / 3) := hi
    _ = _ := by ring

/-- The positive part makes the formula valid even when the excess has
not begun before the prefix ends. -/
theorem integral_positive_quadratic_tail_kernel {θ t₀ : ℝ}
    (hθ : 0 ≤ θ) (ht₀ : 0 ≤ t₀) :
    (∫ t in 0..θ, max (t - t₀) 0 * (θ - t)) =
      (max (θ - t₀) 0) ^ 3 / 6 := by
  have hc : Continuous (fun t : ℝ => max (t - t₀) 0 * (θ - t)) := by fun_prop
  by_cases hθt : θ ≤ t₀
  · have hz : (∫ t in 0..θ, max (t - t₀) 0 * (θ - t)) = 0 := by
      calc
        _ = ∫ _t in 0..θ, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le hθ]
          intro t ht
          rw [max_eq_right (by linarith [ht.2] : t - t₀ ≤ 0), zero_mul]
        _ = 0 := by simp
    rw [hz, max_eq_right (sub_nonpos.mpr hθt)]
    norm_num
  · have htθ : t₀ ≤ θ := le_of_not_ge hθt
    have hleft : (∫ t in 0..t₀, max (t - t₀) 0 * (θ - t)) = 0 := by
      calc
        _ = ∫ _t in 0..t₀, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [uIcc_of_le ht₀]
          intro t ht
          rw [max_eq_right (sub_nonpos.mpr ht.2), zero_mul]
        _ = 0 := by simp
    have hright : (∫ t in t₀..θ, max (t - t₀) 0 * (θ - t)) =
        ∫ t in t₀..θ, (t - t₀) * (θ - t) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le htθ]
      intro t ht
      rw [max_eq_left (sub_nonneg.mpr ht.1)]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 t₀) (hc.intervalIntegrable t₀ θ),
      hleft, hright, zero_add, integral_quadratic_tail_kernel,
      max_eq_left (sub_nonneg.mpr htθ)]

theorem terminal_weight_kernel_eq {θ t : ℝ} (hcos : Real.cos θ ≠ 0) :
    Real.tan θ * Real.cos t - Real.sin t =
      Real.sin (θ - t) / Real.cos θ := by
  rw [Real.tan_eq_sin_div_cos, Real.sin_sub]
  field_simp [hcos] <;> ring

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

/-- The analytic part of MP's cubic payment. The envelope is an
almost-everywhere density estimate, and no continuity of `v` is needed. -/
theorem terminalWeightedExcess_le_cubic {v : ℝ → ℝ} {θ t₀ K : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) (ht₀ : 0 ≤ t₀) (hK : 0 ≤ K)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan θ * Real.cos t - Real.sin t)) volume 0 θ)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 θ),
      max (v t - 1) 0 ≤ K * max (t - t₀) 0) :
    terminalWeightedExcess v θ ≤ K * (max (θ - t₀) 0) ^ 3 / (6 * Real.cos θ) := by
  have hg : Continuous (fun t : ℝ => K / Real.cos θ *
      (max (t - t₀) 0 * (θ - t))) := by fun_prop
  have hmono := intervalIntegral.integral_mono_ae_restrict hθ0 hint
    (hg.intervalIntegrable 0 θ) (show (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan θ * Real.cos t - Real.sin t)) ≤ᵐ[volume.restrict (Icc 0 θ)]
        (fun t : ℝ => K / Real.cos θ * (max (t - t₀) 0 * (θ - t))) from by
      filter_upwards [hbound, ae_restrict_mem measurableSet_Icc] with t ht htm
      obtain ⟨hk0, hk1⟩ := terminal_weight_kernel_bounds hθ0 hθL htm
      calc
        _ ≤ (K * max (t - t₀) 0) *
            (Real.tan θ * Real.cos t - Real.sin t) :=
          mul_le_mul_of_nonneg_right ht hk0
        _ ≤ (K * max (t - t₀) 0) * ((θ - t) / Real.cos θ) :=
          mul_le_mul_of_nonneg_left hk1 (mul_nonneg hK (le_max_right _ _))
        _ = _ := by ring)
  rw [intervalIntegral.integral_const_mul,
    integral_positive_quadratic_tail_kernel hθ0 ht₀] at hmono
  unfold terminalWeightedExcess
  convert hmono using 1 <;> ring

theorem terminalWeightedExcess_eq_zero_of_unit_prefix {v : ℝ → ℝ} {θ : ℝ}
    (hθ : 0 ≤ θ) (hv : ∀ᵐ t ∂volume.restrict (Icc 0 θ), v t ≤ 1) :
    terminalWeightedExcess v θ = 0 := by
  have heq : (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan θ * Real.cos t - Real.sin t)) =ᵐ[volume.restrict (Ioc 0 θ)]
        (fun _t : ℝ => 0) := by
    have hv' := hv.filter_mono
      (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    filter_upwards [hv'] with t ht
    rw [max_eq_right (by linarith : v t - 1 ≤ 0), zero_mul]
  unfold terminalWeightedExcess
  rw [← uIoc_of_le hθ] at heq
  rw [intervalIntegral.integral_congr_ae_restrict heq]
  simp

/-- The rational angular cut uses two exact cosine double-angle
identities and the universal quadratic cosine lower bound. -/
theorem terminal_cos_rational_cut : (37 / 50 : ℝ) < Real.cos (147 / 200) := by
  have hquarter : (1258391 / 1280000 : ℝ) ≤ Real.cos (147 / 800) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := (147 / 800 : ℝ))
    norm_num at h ⊢
    exact h
  have hquarterSq := mul_nonneg (sub_nonneg.mpr hquarter)
    (show 0 ≤ Real.cos (147 / 800) + 1258391 / 1280000 by linarith)
  have hhalfEq := Real.cos_two_mul (147 / 800 : ℝ)
  rw [show 2 * (147 / 800 : ℝ) = 147 / 400 by norm_num] at hhalfEq
  have hhalf : (933 / 1000 : ℝ) < Real.cos (147 / 400) := by
    nlinarith only [hquarterSq, hhalfEq]
  have hhalfSq := mul_pos (sub_pos.mpr hhalf)
    (show 0 < Real.cos (147 / 400) + 933 / 1000 by linarith)
  have hfullEq := Real.cos_two_mul (147 / 400 : ℝ)
  rw [show 2 * (147 / 400 : ℝ) = 147 / 200 by norm_num] at hfullEq
  nlinarith only [hhalfSq, hfullEq]

theorem terminal_prefix_cos_and_length {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ ≤ Real.pi / 2)
    (hsin : Real.sin θ ≤ 37 / 50) :
    (2 / 3 : ℝ) < Real.cos θ ∧
      max (θ - (Real.pi / 2 - 91 / 100)) 0 < (7 / 40 : ℝ) := by
  have hs0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0
    (by linarith [Real.pi_pos])
  have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hθL⟩
  have hsSq := mul_nonneg (sub_nonneg.mpr hsin)
    (show 0 ≤ 37 / 50 + Real.sin θ by positivity)
  have hcos : (2 / 3 : ℝ) < Real.cos θ := by
    by_contra h
    have hcSq := (sq_le_sq₀ hc0 (by norm_num : (0 : ℝ) ≤ 2 / 3)).2 (le_of_not_gt h)
    nlinarith only [hsSq, hcSq, Real.sin_sq_add_cos_sq θ]
  have hcut : θ < Real.pi / 2 - 147 / 200 := by
    by_contra h
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (x := Real.pi / 2 - θ) (y := (147 / 200 : ℝ))
      (by linarith) (by linarith [Real.pi_gt_three]) (by linarith)
    rw [Real.cos_pi_div_two_sub] at h
    linarith [terminal_cos_rational_cut]
  exact ⟨hcos, max_lt (by linarith) (by norm_num)⟩

theorem terminal_arcsin_prefix_cos_and_length {C T : ℝ}
    (hCT : 0 ≤ C - T) (hCT1 : C - T ≤ 37 / 50) :
    (2 / 3 : ℝ) < Real.cos (Real.arcsin (C - T)) ∧
      max (Real.arcsin (C - T) - (Real.pi / 2 - 91 / 100)) 0 < (7 / 40 : ℝ) := by
  apply terminal_prefix_cos_and_length (Real.arcsin_nonneg.mpr hCT)
    (Real.arcsin_le_pi_div_two _)
  rw [Real.sin_arcsin (by linarith) (by linarith)]
  exact hCT1

theorem proper_terminal_cos_gt_three_twenty_fifths {α : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hk : (1 / 8 : ℝ) ≤ terminalSlope α) : (3 / 25 : ℝ) < Real.cos α := by
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hsc : Real.sin α ≤ 8 * Real.cos α := by
    have h := (le_div_iff₀ hs).mp hk
    change 1 / 8 * Real.sin α ≤ Real.cos α at h
    linarith
  have hsq := mul_nonneg (sub_nonneg.mpr hsc)
    (show 0 ≤ 8 * Real.cos α + Real.sin α by positivity)
  by_contra h
  have hcSq := (sq_le_sq₀ hc.le (by norm_num : (0 : ℝ) ≤ 3 / 25)).2 (le_of_not_gt h)
  nlinarith only [hsq, hcSq, Real.sin_sq_add_cos_sq α]

theorem terminal_cubic_rational_allowance {q ℓ c : ℝ}
    (hq : (2 / 3 : ℝ) < q) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ < 7 / 40)
    (hc : (3 / 25 : ℝ) < c) :
    (19 / 25 : ℝ) * ℓ ^ 3 / (6 * q) < (39 / 4400 : ℝ) * c := by
  have hq0 : 0 < q := by linarith
  have hpay : (19 / 25 : ℝ) * ℓ ^ 3 / (6 * q) ≤ (19 / 100 : ℝ) * ℓ ^ 3 := by
    apply (div_le_iff₀ (by positivity : 0 < 6 * q)).mpr
    nlinarith [mul_nonneg (show 0 ≤ q - 2 / 3 by linarith) (pow_nonneg hℓ0 3)]
  have hpow : ℓ ^ 3 < (7 / 40 : ℝ) ^ 3 :=
    pow_lt_pow_left₀ hℓ1 hℓ0 (by norm_num)
  calc
    _ ≤ (19 / 100 : ℝ) * ℓ ^ 3 := hpay
    _ < (6517 / 6400000 : ℝ) := by nlinarith only [hpow]
    _ < (117 / 110000 : ℝ) := by norm_num
    _ < (39 / 4400 : ℝ) * c := by nlinarith only [hc]

/-- MP's exact allowance from AC's late-tail envelope, for the
complementary cotangent range. -/
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
  obtain ⟨hcos, hlength⟩ := terminal_arcsin_prefix_cos_and_length hCT hCT1
  have hθ0 := Real.arcsin_nonneg.mpr hCT
  have hθL : Real.arcsin (C - T) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr (by linarith)
  have hc := proper_terminal_cos_gt_three_twenty_fifths hα0 hαL hk
  exact (terminalWeightedExcess_le_cubic
    (t₀ := Real.pi / 2 - 91 / 100) (K := (19 / 25 : ℝ)) hθ0 hθL
    (by linarith [Real.pi_gt_three]) (by norm_num) hint hbound).trans_lt
      (terminal_cubic_rational_allowance hcos (le_max_right _ _) hlength hc)

end AmbidextrousSofa
