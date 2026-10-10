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
    IntervalIntegrable (fun r : ℝ => max (v r - 1) 0) volume a b := by
  have hsub := hv.sub (intervalIntegrable_const (c := (1 : ℝ)))
  have hi := (hsub.add hsub.abs).div_const 2
  refine hi.congr ?_
  intro r _hr
  by_cases hvr : 0 ≤ v r - 1
  · rw [abs_of_nonneg hvr, max_eq_left hvr]
    ring
  · have hvr' : v r - 1 ≤ 0 := le_of_not_ge hvr
    rw [abs_of_nonpos hvr', max_eq_right hvr']
    ring

theorem terminalWeightedExcess_intervalIntegrable {v : ℝ → ℝ} {θ : ℝ}
    (hv : IntervalIntegrable v volume 0 θ) :
    IntervalIntegrable (fun r : ℝ => max (v r - 1) 0 *
      (Real.tan θ * Real.cos r - Real.sin r)) volume 0 θ :=
  (intervalIntegrable_terminal_positive_excess hv).mul_continuousOn (by fun_prop)

theorem terminalWeightedExcess_nonneg {v : ℝ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2) :
    0 ≤ terminalWeightedExcess v θ := by
  apply intervalIntegral.integral_nonneg hθ0
  intro r hr
  exact mul_nonneg (le_max_right _ _) (terminal_weight_kernel_bounds hθ0 hθL hr).1

theorem terminal_companion_kernel_nonneg_after {θ r : ℝ}
    (hθ0 : 0 ≤ θ) (hθL : θ < Real.pi / 2)
    (hθr : θ ≤ r) (hrL : r ≤ Real.pi / 2) :
    0 ≤ Real.sin r - Real.tan θ * Real.cos r := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hθL⟩
  have heq : Real.sin r - Real.tan θ * Real.cos r =
      Real.sin (r - θ) / Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub]
    field_simp [hc.ne'] <;> ring
  rw [heq]
  exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
    (sub_nonneg.mpr hθr) (by linarith [Real.pi_pos])) hc.le

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
  have hf : IntervalIntegrable (fun r : ℝ =>
      (1 - v r) * (Real.sin r - Real.tan θ * Real.cos r)) volume 0 θ :=
    ((intervalIntegrable_const (c := (1 : ℝ))).sub hv).mul_continuousOn (by fun_prop)
  have he := terminalWeightedExcess_intervalIntegrable hv
  have hpre := intervalIntegral.integral_mono_on ht0 (hf.mono_set hsub)
    (he.mono_set hsub) (show ∀ r ∈ Icc 0 t,
      (1 - v r) * (Real.sin r - Real.tan θ * Real.cos r) ≤
        max (v r - 1) 0 * (Real.tan θ * Real.cos r - Real.sin r) from by
      intro r hr
      have hk := (terminal_weight_kernel_bounds hθ0 hθL
        ⟨hr.1, hr.2.trans htθ⟩).1
      calc
        _ = (v r - 1) * (Real.tan θ * Real.cos r - Real.sin r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hk)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 θ)]
      (fun r : ℝ => max (v r - 1) 0 *
        (Real.tan θ * Real.cos r - Real.sin r)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact mul_nonneg (le_max_right _ _)
      (terminal_weight_kernel_bounds hθ0 hθL ⟨hr.1.le, hr.2⟩).1
  exact hpre.trans (intervalIntegral.integral_mono_interval
    (a := 0) (b := t) (c := 0) (d := θ) le_rfl ht0 htθ hnonneg he)

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
  have hβ0 : 0 ≤ β := hθ0.trans hθβ
  have hθL : θ < Real.pi / 2 := hθβ.trans_lt hβL
  let k : ℝ → ℝ := fun r => Real.sin r - Real.tan θ * Real.cos r
  let f : ℝ → ℝ := fun r => (1 - v r) * k r
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hfi : IntervalIntegrable f volume 0 β :=
    ((intervalIntegrable_const (c := (1 : ℝ))).sub hv).mul_continuousOn hkc.continuousOn
  have hrestrict (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ β) :
      uIcc a b ⊆ uIcc 0 β := by
    rw [uIcc_of_le hab, uIcc_of_le hβ0]
    exact Icc_subset_Icc ha hb
  have hvθ := hv.mono_set (hrestrict 0 θ le_rfl hθ0 hθβ)
  have hktail : 0 ≤ᵐ[volume.restrict (Ioc θ β)] k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact terminal_companion_kernel_nonneg_after hθ0 hθL hr.1.le (hr.2.trans hβL.le)
  have htail0 : 0 ≤ ∫ r in θ..β, k r := by
    apply intervalIntegral.integral_nonneg hθβ
    intro r hr
    exact terminal_companion_kernel_nonneg_after hθ0 hθL hr.1 (hr.2.trans hβL.le)
  have hbound : (∫ r in 0..t, f r) ≤
      terminalWeightedExcess v θ + ∫ r in θ..β, k r := by
    by_cases htθ : t ≤ θ
    · have hpre : (∫ r in 0..t, f r) ≤ terminalWeightedExcess v θ :=
        terminal_companion_prefix_moment_le hθ0 hθL ht0 htθ hvθ
      linarith
    · have hθt : θ ≤ t := le_of_not_ge htθ
      have hpre : (∫ r in 0..θ, f r) ≤ terminalWeightedExcess v θ :=
        terminal_companion_prefix_moment_le hθ0 hθL hθ0 le_rfl hvθ
      have hv0' := hv0.filter_mono (ae_mono (Measure.restrict_mono
        (Icc_subset_Icc hθ0 htβ) le_rfl))
      have hlate : (∫ r in θ..t, f r) ≤ ∫ r in θ..t, k r := by
        apply intervalIntegral.integral_mono_ae_restrict hθt
          (hfi.mono_set (hrestrict θ t hθ0 hθt htβ)) (hkc.intervalIntegrable θ t)
        filter_upwards [hv0', ae_restrict_mem measurableSet_Icc] with r hvr hr
        have hk : 0 ≤ k r := terminal_companion_kernel_nonneg_after hθ0 hθL
          hr.1 (hr.2.trans (htβ.trans hβL.le))
        dsimp [f]
        nlinarith [mul_nonneg hvr hk]
      have hextend := intervalIntegral.integral_mono_interval
        (a := θ) (b := t) (c := θ) (d := β) le_rfl hθt htβ hktail
          (hkc.intervalIntegrable θ β)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hfi.mono_set (hrestrict 0 θ le_rfl hθ0 hθβ))
        (hfi.mono_set (hrestrict θ t hθ0 hθt htβ))
      linarith
  have hvone : IntervalIntegrable (fun r : ℝ => 1 - v r) volume 0 t :=
    ((intervalIntegrable_const (c := (1 : ℝ))).sub hv).mono_set
      (hrestrict 0 t le_rfl ht0 htβ)
  have hvertical := hvone.mul_continuousOn Real.continuous_sin.continuousOn
  have hhorizontalInt := hvone.mul_continuousOn Real.continuous_cos.continuousOn
  have hmoment : (∫ r in 0..t, f r) =
      (∫ r in 0..t, (1 - v r) * Real.sin r) -
        Real.tan θ * (Real.sin β - Real.sin θ) := by
    calc
      _ = ∫ r in 0..t, ((1 - v r) * Real.sin r -
          Real.tan θ * ((1 - v r) * Real.cos r)) := by
        apply intervalIntegral.integral_congr
        intro r _hr
        dsimp [f, k]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hvertical (hhorizontalInt.const_mul (Real.tan θ)),
          intervalIntegral.integral_const_mul, hhorizontal]
  have htail : (∫ r in θ..β, k r) = Real.cos θ - Real.cos β -
      Real.tan θ * (Real.sin β - Real.sin θ) := by
    dsimp [k]
    rw [intervalIntegral.integral_sub (Real.continuous_sin.intervalIntegrable θ β)
      ((Real.continuous_cos.intervalIntegrable θ β).const_mul (Real.tan θ)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sin,
      intervalIntegral.integral_cos]
  linarith only [hbound, hmoment, htail]

/-- The circle-height form of the localized companion comparison.
The horizontal moment is the actual displacement `B - A`. -/
theorem terminal_weighted_companion_moment {v : ℝ → ℝ} {A B t : ℝ}
    (hA : 0 < A) (hAB : A ≤ B) (hB : B < 1)
    (ht0 : 0 ≤ t) (htB : t ≤ Real.arcsin B)
    (hv : IntervalIntegrable v volume 0 (Real.arcsin B))
    (hv0 : ∀ᵐ r ∂volume.restrict (Icc 0 (Real.arcsin B)), 0 ≤ v r)
    (hhorizontal : (∫ r in 0..t, (1 - v r) * Real.cos r) = B - A) :
    (∫ r in 0..t, (1 - v r) * Real.sin r) ≤
      circleHeight A - circleHeight B + terminalWeightedExcess v (Real.arcsin A) := by
  have hsinA := Real.sin_arcsin (by linarith : -1 ≤ A) (hAB.trans hB.le)
  have hsinB := Real.sin_arcsin (by linarith : -1 ≤ B) hB.le
  have hhorizontal' : (∫ r in 0..t, (1 - v r) * Real.cos r) =
      Real.sin (Real.arcsin B) - Real.sin (Real.arcsin A) := by
    rwa [hsinB, hsinA]
  have h := terminal_weighted_companion_moment_trig
    (Real.arcsin_nonneg.mpr hA.le) (Real.arcsin_le_arcsin hAB)
    (Real.arcsin_lt_pi_div_two.mpr hB) ht0 htB hv hv0 hhorizontal'
  simpa only [Real.cos_arcsin, circleHeight] using h

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
  have hmoment := terminal_weighted_companion_moment hA hAB hB ht0 htB hv hv0 hhorizontal
  have hcircle := circleHeight_antitoneOn ⟨hA, hAB.trans_lt hB⟩
    ⟨hA.trans_le hAB, hB⟩ hAB
  have he := terminalWeightedExcess_nonneg (v := v) (Real.arcsin_nonneg.mpr hA.le)
    (Real.arcsin_lt_pi_div_two.mpr (hAB.trans_lt hB))
  exact max_le (by linarith) (by linarith)

end AmbidextrousSofa
