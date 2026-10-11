module

public import AmbidextrousSofa.Analysis.TerminalCubicPayment
public import AmbidextrousSofa.Analysis.CircleAverage

@[expose] public section

/-!
# The weighted companion moment

A nonnegative integrable curvature density controls the vertical moment
at a localized companion-wall maximum. The horizontal moment fixes its
displacement. Only curvature excess before the shorter angle
`arcsin (C - T_L)` is charged: after that angle the comparison kernel is
nonnegative, so nonnegative curvature gives the required upper bound.

These are analytic integral theorems. The actual companion support must
still supply its density, both moment identities, and the localization
of a positive wall maximum. No score inequality is assumed here.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem intervalIntegrable_terminal_positive_excess {v : ℝ → ℝ} {a b : ℝ}
    (hv : IntervalIntegrable v volume a b) :
    IntervalIntegrable (fun r : ℝ => max (v r - 1) 0) volume a b :=
  have h := hv.sub (intervalIntegrable_const (c := (1 : ℝ)))
  ⟨Integrable.pos_part h.1, Integrable.pos_part h.2⟩

theorem terminalWeightedExcess_intervalIntegrable {v : ℝ → ℝ} {θ : ℝ}
    (hv : IntervalIntegrable v volume 0 θ) :
    IntervalIntegrable (fun r : ℝ => max (v r - 1) 0 *
      (Real.tan θ * Real.cos r - Real.sin r)) volume 0 θ :=
  (intervalIntegrable_terminal_positive_excess hv).mul_continuousOn (by fun_prop)

theorem terminalWeightedExcess_nonneg {v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) :
    0 ≤ terminalWeightedExcess v θ :=
  intervalIntegral.integral_nonneg hθ0 fun _ hr =>
    mul_nonneg (le_max_right _ _) (terminal_weight_kernel_bounds hθ0 hθL hr).1

/-- Before the prefix endpoint, the whole signed moment is paid by
the positive curvature excess on the complete prefix. -/
theorem terminal_companion_prefix_moment_le {v : ℝ → ℝ} {θ t : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2)
    (ht0 : 0 ≤ t) (htθ : t ≤ θ)
    (hv : IntervalIntegrable v volume 0 θ) :
    (∫ r in 0..t, (1 - v r) * (Real.sin r - Real.tan θ * Real.cos r)) ≤
      terminalWeightedExcess v θ := by
  have hsub : uIcc 0 t ⊆ uIcc 0 θ := by
    rw [uIcc_of_le ht0, uIcc_of_le hθ0]
    exact Icc_subset_Icc le_rfl htθ
  have he := terminalWeightedExcess_intervalIntegrable hv
  refine (intervalIntegral.integral_mono_on ht0
    ((intervalIntegrable_const.sub hv).mul_continuousOn (by fun_prop) |>.mono_set hsub)
    (he.mono_set hsub) fun r hr => ?_).trans
    (intervalIntegral.integral_mono_interval le_rfl ht0 htθ ?_ he)
  · linarith [mul_le_mul_of_nonneg_right (le_max_left (v r - 1) 0)
      (terminal_weight_kernel_bounds hθ0 hθL ⟨hr.1, hr.2.trans htθ⟩).1]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (le_max_right _ _) (terminal_weight_kernel_bounds hθ0 hθL ⟨hr.1.le, hr.2⟩).1

/-- The trigonometric form of MP.14--16. The suffix comparison is
extended to `β`, where its cosine and sine moments are exact. -/
theorem terminal_weighted_companion_moment_trig
    {v : ℝ → ℝ} {θ β t : ℝ}
    (hθ0 : 0 ≤ θ) (hθβ : θ ≤ β) (hβL : β < Real.pi / 2)
    (ht0 : 0 ≤ t) (htβ : t ≤ β)
    (hv : IntervalIntegrable v volume 0 β)
    (hv0 : ∀ᵐ r ∂volume.restrict (Icc 0 β), 0 ≤ v r)
    (hhorizontal : (∫ r in 0..t, (1 - v r) * Real.cos r) =
      Real.sin β - Real.sin θ) :
    (∫ r in 0..t, (1 - v r) * Real.sin r) ≤
      Real.cos θ - Real.cos β + terminalWeightedExcess v θ := by
  have hθL : θ < Real.pi / 2 := hθβ.trans_lt hβL
  -- The kernel `k` is nonnegative after `θ`.
  let k : ℝ → ℝ := fun r => Real.sin r - Real.tan θ * Real.cos r
  have hkc : Continuous k := by fun_prop
  have hk0 {r : ℝ} (h1 : θ ≤ r) (h2 : r ≤ β) : 0 ≤ k r := by
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθL⟩
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.2 h1) (by linarith [Real.pi_pos])
    rw [Real.sin_sub] at hs
    simp only [k, Real.tan_eq_sin_div_cos]
    rw [div_mul_eq_mul_div, sub_nonneg, div_le_iff₀ hc]
    linarith
  have hsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ β) : uIcc a b ⊆ uIcc 0 β := by
    rw [uIcc_of_le hab, uIcc_of_le (hθ0.trans hθβ)]
    exact Icc_subset_Icc ha hb
  have hvone : IntervalIntegrable (fun r => 1 - v r) volume 0 β := intervalIntegrable_const.sub hv
  have hfi := hvone.mul_continuousOn hkc.continuousOn
  have hvθ := hv.mono_set (hsub le_rfl hθ0 hθβ)
  -- The signed moment is paid by the prefix excess and the tail of `k`.
  have hbound : (∫ r in 0..t, (1 - v r) * k r) ≤
      terminalWeightedExcess v θ + ∫ r in θ..β, k r := by
    have hktail : 0 ≤ᵐ[volume.restrict (Ioc θ β)] k := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hk0 hr.1.le hr.2
    rcases le_total t θ with htθ | hθt
    · linarith [terminal_companion_prefix_moment_le hθ0 hθL ht0 htθ hvθ,
        intervalIntegral.integral_nonneg (μ := volume) hθβ fun r hr => hk0 hr.1 hr.2]
    have hlate : (∫ r in θ..t, (1 - v r) * k r) ≤ ∫ r in θ..t, k r := by
      refine intervalIntegral.integral_mono_ae_restrict hθt
        (hfi.mono_set (hsub hθ0 hθt htβ)) (hkc.intervalIntegrable θ t) ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hθ0 htβ) hv0,
        ae_restrict_mem measurableSet_Icc] with r hvr hr
      nlinarith [hk0 hr.1 (hr.2.trans htβ)]
    linarith [terminal_companion_prefix_moment_le hθ0 hθL hθ0 le_rfl hvθ,
      intervalIntegral.integral_add_adjacent_intervals (hfi.mono_set (hsub le_rfl hθ0 hθβ))
        (hfi.mono_set (hsub hθ0 hθt htβ)),
      intervalIntegral.integral_mono_interval le_rfl hθt htβ hktail (hkc.intervalIntegrable θ β)]
  have hvt := hvone.mono_set (hsub le_rfl ht0 htβ)
  have hmoment : (∫ r in 0..t, (1 - v r) * k r) = (∫ r in 0..t, (1 - v r) * Real.sin r) -
      Real.tan θ * (Real.sin β - Real.sin θ) := by
    rw [← hhorizontal, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hvt.mul_continuousOn Real.continuous_sin.continuousOn)
        ((hvt.mul_continuousOn Real.continuous_cos.continuousOn).const_mul _)]
    exact intervalIntegral.integral_congr fun r _ => by simp only [k]; ring
  have htail : (∫ r in θ..β, k r) = Real.cos θ - Real.cos β -
      Real.tan θ * (Real.sin β - Real.sin θ) := by
    simp [k, intervalIntegral.integral_sub, integral_sin, integral_cos]
  linarith

theorem terminal_weighted_companion_height_bound
    {v : ℝ → ℝ} {A B t Y h : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hB : B < 1)
    (ht0 : 0 ≤ t) (htB : t ≤ Real.arcsin B)
    (hv : IntervalIntegrable v volume 0 (Real.arcsin B))
    (hv0 : ∀ᵐ r ∂volume.restrict (Icc 0 (Real.arcsin B)), 0 ≤ v r)
    (hhorizontal : (∫ r in 0..t, (1 - v r) * Real.cos r) = B - A)
    (hh : 0 ≤ h) (hvertical : Y + h = ∫ r in 0..t, (1 - v r) * Real.sin r) :
    max Y 0 ≤ circleHeight A - circleHeight B +
      terminalWeightedExcess v (Real.arcsin A) := by
  -- The circle-height form of the localized companion comparison: the horizontal
  -- moment is the actual displacement `B - A`.
  have hmoment := terminal_weighted_companion_moment_trig (Real.arcsin_nonneg.mpr hA.le)
    (Real.arcsin_le_arcsin hAB) (Real.arcsin_lt_pi_div_two.mpr hB) ht0 htB hv hv0 (by
      rwa [Real.sin_arcsin (by linarith) hB.le, Real.sin_arcsin (by linarith) (hAB.trans hB.le)])
  rw [Real.cos_arcsin, Real.cos_arcsin, ← circleHeight, ← circleHeight] at hmoment
  have hcircle := circleHeight_antitoneOn ⟨hA, hAB.trans_lt hB⟩ ⟨hA.trans_le hAB, hB⟩ hAB
  have he := terminalWeightedExcess_nonneg (v := v) (Real.arcsin_nonneg.mpr hA.le)
    (Real.arcsin_lt_pi_div_two.mpr (hAB.trans_lt hB))
  exact max_le (by linarith) (by linarith)

end AmbidextrousSofa
