module

public import AmbidextrousSofa.Analysis.TerminalThreeSupports
public import AmbidextrousSofa.Analysis.TerminalCircleEndpoints
public import AmbidextrousSofa.Analysis.ProperExcessBudget
public import AmbidextrousSofa.Analysis.TiltedLateExcessScalar

@[expose] public section

/-!
# The exact weighted cubic payment for a late companion excess

The weighted error in the proper-terminal comparison is an ordinary
integral of the positive curvature excess. Its trigonometric kernel is
nonnegative before the selected prefix endpoint. A linear late-tail
envelope therefore pays a cubic amount, with all clipping retained.

The overlap is proportional to terminal slope, so its cubic moment
pays the terminal cosine margin throughout the slope range. The same
quadratic half-angle cosine bound supplies the prefix cut.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

open Analysis

def terminalWeightedExcess (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in 0..θ, max (v t - 1) 0 *
    (Real.tan θ * Real.cos t - Real.sin t)

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
    ← Analysis.integral_quadratic_tail_kernel]
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

/-- One angularly scaled cubic payment covers the entire terminal-slope range. -/
theorem terminalWeightedExcess_lt_allowance_of_angular_budget
    {v : ℝ → ℝ} {C T α : ℝ}
    (hCT : 0 ≤ C - T) (hCT1 : C - T ≤ 37 / 50)
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hk1 : terminalSlope α ≤ 3 / 8)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan (Real.arcsin (C - T)) * Real.cos t - Real.sin t))
        volume 0 (Real.arcsin (C - T)))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.arcsin (C - T))),
      max (v t - 1) 0 ≤ (4 / 5 : ℝ) *
        max (t - (Real.pi / 2 - properAngularDeadline (terminalSlope α))) 0) :
    terminalWeightedExcess v (Real.arcsin (C - T)) < terminalCircleGap * Real.cos α := by
  have hk0 := terminalSlope_pos hα0 hαL
  obtain ⟨hs, hc⟩ := sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  have hcs : terminalSlope α * Real.sin α = Real.cos α := div_mul_cancel₀ _ hs.ne'
  have hc1 := mul_le_mul_of_nonneg_right hk1 hs.le
  rw [hcs] at hc1
  have hsin := terminalCircleSineLower_le_of_slope hc.le hs
    (Real.cos_sq_add_sin_sq α) hc1
  have hcSlope : terminalCircleSineLower * terminalSlope α ≤ Real.cos α := by
    linarith only [hcs, mul_le_mul_of_nonneg_left hsin hk0.le]
  have hq : (2 / 3 : ℝ) < Real.cos (Real.arcsin (C - T)) := by
    rw [Real.cos_arcsin, Real.lt_sqrt (by norm_num)]
    nlinarith only [hCT, hCT1]
  have hcut := eleven_fifteenths_lt_arccos_of_le (by linarith only [hCT]) hCT1
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hcut
  have hℓ : max (Real.arcsin (C - T) -
      (Real.pi / 2 - properAngularDeadline (terminalSlope α))) 0 ≤ (2 / 3) * terminalSlope α := by
    apply max_le
    · dsimp [properAngularDeadline]; linarith only [hcut]
    · positivity
  refine (terminalWeightedExcess_le_cubic (K := (4 / 5 : ℝ))
    (Real.arcsin_nonneg.mpr hCT) (Real.arcsin_lt_pi_div_two.mpr (by linarith only [hCT1]))
    (by dsimp [properAngularDeadline]; linarith only [hk1, Real.pi_gt_three])
    (by norm_num) hint hbound).trans_lt ?_
  have hpow := pow_le_pow_left₀ (le_max_right _ _) hℓ 3
  have hcube : terminalSlope α ^ 3 ≤ (9 / 64) * terminalSlope α := by
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0.le hk1 2) hk0.le]
  have hprod := mul_le_mul hcSlope hq.le (by positivity : (0 : ℝ) ≤ (2 / 3)) hc.le
  rw [div_lt_iff₀ (by positivity)]
  have hcert : (4 / 5 : ℝ) * (2 / 3) ^ 3 * (3 / 8) ^ 2 <
      terminalCircleGap * (6 * (2 / 3) * terminalCircleSineLower) := by
    have h := terminalCircleGap_gt_cubicPrice
    unfold terminalCubicPrice at h
    exact (div_lt_iff₀ (by have hp := terminalCircleSineLower_pos; positivity)).mp h
  have hpriced := mul_lt_mul_of_pos_right hcert hk0
  have hproduct := mul_le_mul_of_nonneg_left hprod terminalCircleGap_pos.le
  nlinarith only [hpow, hcube, hproduct, hpriced]

end AmbidextrousSofa
