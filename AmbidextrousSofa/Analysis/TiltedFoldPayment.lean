import AmbidextrousSofa.Analysis.TiltedHarmonicMoments

/-!
# Paying the complete companion-fold loss

The initial floor interval contributes its exact weighted momentum
moment. Before the right window every remaining contribution is
nonnegative. Later negative contributions are paid by the actual
right-window deficit mass. The floor crossing and right-window entry
are not assumed to occur in either order.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

/-- On the right window, the actual sine moment pays the entire
nonnegative deficit mass with the exact factor `1 / sin β`. -/
theorem firstUnit_right_window_mass_le_div_sin
    {r : ℝ → ℝ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβL : β ≤ Real.pi / 2) (hβsin : 0 < Real.sin β)
    (hr : IntervalIntegrable r volume β (Real.pi / 2))
    (hr0 : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), 0 ≤ r t) :
    (∫ t in β..(Real.pi / 2), r t) ≤
      (∫ t in β..(Real.pi / 2), r t * Real.sin t) / Real.sin β := by
  have hrs := hr.mul_continuousOn Real.continuous_sin.continuousOn
  have hpoint : (fun t => Real.sin β * r t) ≤ᵐ[
      volume.restrict (Icc β (Real.pi / 2))] (fun t => r t * Real.sin t) := by
    filter_upwards [hr0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    have hsin : Real.sin β ≤ Real.sin t :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) ht.2 ht.1
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsin hrt
  have hi := intervalIntegral.integral_mono_ae_restrict hβL
    (hr.const_mul (Real.sin β)) hrs hpoint
  rw [intervalIntegral.integral_const_mul] at hi
  apply (le_div_iff₀ hβsin).2
  simpa only [mul_comm] using hi

theorem intervalIntegrable_firstUnitLossDensity
    {q v δ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hv : IntervalIntegrable v volume a b)
    (hδm : AEStronglyMeasurable δ (volume.restrict (Icc a b)))
    (hδ : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ δ t ∧ δ t ≤ 1) :
    IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume a b := by
  have hw : IntervalIntegrable (fun t => (q t + 1) * (1 - v t)) volume a b :=
    ((intervalIntegrable_const (c := (1 : ℝ))).sub hv).continuousOn_mul
      (hq.continuousOn.add continuousOn_const)
  have hw' := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).1 hw
  have hdm : AEStronglyMeasurable (fun t => 1 - δ t) (volume.restrict (Icc a b)) :=
    aestronglyMeasurable_const.sub hδm
  have hdb : ∀ᵐ t ∂volume.restrict (Icc a b), ‖1 - δ t‖ ≤ (1 : ℝ) := by
    filter_upwards [hδ] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
    linarith [ht.1]
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
  simpa only [firstUnitLossDensity] using hw'.mul_bdd hdm hdb

/-- A tail with nonnegative loss before `β` and a density payment after
`β` is paid by the whole `β..L` budget, even if `γ > β`. -/
theorem intervalIntegral_tail_paid
    {D r : ℝ → ℝ} {γ β η L k : ℝ}
    (hγη : γ ≤ η) (hβη : β ≤ η) (hηL : η ≤ L) (hk : 0 ≤ k)
    (hD : IntervalIntegrable D volume γ η)
    (hr : IntervalIntegrable r volume β L)
    (hr0 : ∀ᵐ t ∂volume.restrict (Icc β L), 0 ≤ r t)
    (hbefore : ∀ᵐ t ∂volume.restrict (Icc γ η), t ≤ β → 0 ≤ D t)
    (hafter : ∀ᵐ t ∂volume.restrict (Icc γ η), β ≤ t → -k * r t ≤ D t) :
    -k * (∫ t in β..L, r t) ≤ ∫ t in γ..η, D t := by
  have hβL := hβη.trans hηL
  have hr0' : ∀ᵐ t ∂volume.restrict (Ioc β L), 0 ≤ r t :=
    hr0.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  by_cases hγβ : γ ≤ β
  · have hDγβ := hD.mono_set (show uIcc γ β ⊆ uIcc γ η by
      simpa only [uIcc_of_le hγβ, uIcc_of_le hγη] using
        (Icc_subset_Icc (le_refl γ) hβη))
    have hDβη := hD.mono_set (show uIcc β η ⊆ uIcc γ η by
      simpa only [uIcc_of_le hβη, uIcc_of_le hγη] using
        (Icc_subset_Icc hγβ (le_refl η)))
    have hrβη := hr.mono_set (show uIcc β η ⊆ uIcc β L by
      simpa only [uIcc_of_le hβη, uIcc_of_le hβL] using
        (Icc_subset_Icc (le_refl β) hηL))
    have hgood : 0 ≤ ∫ t in γ..β, D t := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hγβ
      filter_upwards [ae_restrict_Icc_subinterval le_rfl hβη hbefore,
        ae_restrict_mem measurableSet_Icc] with t ht hmem
      exact ht hmem.2
    have hpaid : -k * (∫ t in β..η, r t) ≤ ∫ t in β..η, D t := by
      have hi := intervalIntegral.integral_mono_ae_restrict hβη
        (hrβη.const_mul (-k)) hDβη
        (show (fun t => -k * r t) ≤ᵐ[volume.restrict (Icc β η)] D from by
          filter_upwards [ae_restrict_Icc_subinterval hγβ le_rfl hafter,
            ae_restrict_mem measurableSet_Icc] with t ht hmem
          exact ht hmem.1)
      simpa only [intervalIntegral.integral_const_mul] using hi
    have hmass := intervalIntegral.integral_mono_interval le_rfl hβη hηL hr0' hr
    have hsum := intervalIntegral.integral_add_adjacent_intervals hDγβ hDβη
    nlinarith [mul_le_mul_of_nonneg_left hmass hk]
  · have hβγ : β ≤ γ := (lt_of_not_ge hγβ).le
    have hrγη := hr.mono_set (show uIcc γ η ⊆ uIcc β L by
      simpa only [uIcc_of_le hγη, uIcc_of_le hβL] using
        (Icc_subset_Icc hβγ hηL))
    have hpaid : -k * (∫ t in γ..η, r t) ≤ ∫ t in γ..η, D t := by
      have hi := intervalIntegral.integral_mono_ae_restrict hγη
        (hrγη.const_mul (-k)) hD
        (show (fun t => -k * r t) ≤ᵐ[volume.restrict (Icc γ η)] D from by
          filter_upwards [hafter, ae_restrict_mem measurableSet_Icc] with t ht hmem
          exact ht (hβγ.trans hmem.1))
      simpa only [intervalIntegral.integral_const_mul] using hi
    have hmass := intervalIntegral.integral_mono_interval hβγ hγη hηL hr0' hr
    nlinarith [mul_le_mul_of_nonneg_left hmass hk]

/-- The pointwise fold estimate needs the upper momentum bound only
at actual bad points. Nonbad pieces are favorable. -/
theorem firstUnit_lossDensity_lower_bound_of_bad
    {q v δ u : ℝ}
    (hq0 : -1 ≤ q) (hbad : 1 < v → q ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hu : u ≤ 1)
    (hfold : max (v - 1) 0 ≤ (1 - u) / 4) :
    -(5 / 16) * (1 - u) ≤ firstUnitLossDensity q v δ := by
  by_cases hv : v ≤ 1
  · have hgood : 0 ≤ firstUnitLossDensity q v δ :=
      mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hv))
        (sub_nonneg.mpr hδ1)
    nlinarith
  · exact firstUnit_lossDensity_lower_bound hq0 (hbad (lt_of_not_ge hv))
      hδ0 hδ1 hu hfold

/-- GF's complete loss is the exact first-floor moment, up to a
payment from the literal right-window deficit mass. -/
theorem firstUnit_loss_integral_lower_bound
    {q u v δ : ℝ → ℝ} {γ β η L : ℝ}
    (hγ0 : 0 ≤ γ) (hγη : γ ≤ η) (hβ0 : 0 ≤ β)
    (hβη : β ≤ η) (hηL : η ≤ L)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume 0 η)
    (hu : IntervalIntegrable u volume β L)
    (hfloor : ∀ᵐ t ∂volume.restrict (Icc 0 γ), δ t = 0)
    (hq0 : ∀ᵐ t ∂volume.restrict (Icc 0 η), -1 ≤ q t)
    (hδ : ∀ᵐ t ∂volume.restrict (Icc 0 η), 0 ≤ δ t ∧ δ t ≤ 1)
    (hvbefore : ∀ᵐ t ∂volume.restrict (Icc 0 β), v t ≤ 1)
    (hbad : ∀ᵐ t ∂volume.restrict (Icc 0 η), 1 < v t → q t ≤ 1 / 4)
    (hunit : ∀ᵐ t ∂volume.restrict (Icc 0 L), u t ≤ 1)
    (hfold : ∀ᵐ t ∂volume.restrict (Icc 0 L), max (v t - 1) 0 ≤ (1 - u t) / 4) :
    (∫ t in 0..γ, (q t + 1) * (1 - v t)) -
      5 / 16 * (∫ t in β..L, 1 - u t) ≤
        ∫ t in 0..η, firstUnitLossDensity (q t) (v t) (δ t) := by
  have h0η : 0 ≤ η := hγ0.trans hγη
  have hD0γ := hD.mono_set (show uIcc 0 γ ⊆ uIcc 0 η by
    simpa only [uIcc_of_le hγ0, uIcc_of_le h0η] using
      (Icc_subset_Icc (le_refl (0 : ℝ)) hγη))
  have hDγη := hD.mono_set (show uIcc γ η ⊆ uIcc 0 η by
    simpa only [uIcc_of_le hγη, uIcc_of_le h0η] using
      (Icc_subset_Icc hγ0 (le_refl η)))
  have hr : IntervalIntegrable (fun t => 1 - u t) volume β L :=
    (intervalIntegrable_const (c := (1 : ℝ))).sub hu
  have hr0 : ∀ᵐ t ∂volume.restrict (Icc β L), 0 ≤ 1 - u t := by
    filter_upwards [ae_restrict_Icc_subinterval hβ0 le_rfl hunit] with t ht
    exact sub_nonneg.mpr ht
  have hbefore : ∀ᵐ t ∂volume.restrict (Icc γ η), t ≤ β →
      0 ≤ firstUnitLossDensity (q t) (v t) (δ t) := by
    have hvbefore' := (ae_restrict_iff' measurableSet_Icc).1 hvbefore
    filter_upwards [ae_restrict_Icc_subinterval hγ0 le_rfl hq0,
      ae_restrict_Icc_subinterval hγ0 le_rfl hδ,
      ae_restrict_of_ae hvbefore', ae_restrict_mem measurableSet_Icc] with t hqt hdt hvt ht
    intro htβ
    have hv1 := hvt ⟨hγ0.trans ht.1, htβ⟩
    exact mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hv1))
      (sub_nonneg.mpr hdt.2)
  have hafter : ∀ᵐ t ∂volume.restrict (Icc γ η), β ≤ t →
      -(5 / 16) * (1 - u t) ≤ firstUnitLossDensity (q t) (v t) (δ t) := by
    filter_upwards [ae_restrict_Icc_subinterval hγ0 le_rfl hq0,
      ae_restrict_Icc_subinterval hγ0 le_rfl hbad,
      ae_restrict_Icc_subinterval hγ0 le_rfl hδ,
      ae_restrict_Icc_subinterval hγ0 hηL hunit,
      ae_restrict_Icc_subinterval hγ0 hηL hfold] with t hqt hbt hdt hut hft
    intro htβ
    exact firstUnit_lossDensity_lower_bound_of_bad hqt hbt hdt.1 hdt.2 hut hft
  have hpaid := intervalIntegral_tail_paid hγη hβη hηL (by norm_num : (0 : ℝ) ≤ 5 / 16)
    hDγη hr hr0 hbefore hafter
  have hfloor_eq : (∫ t in 0..γ, firstUnitLossDensity (q t) (v t) (δ t)) =
      ∫ t in 0..γ, (q t + 1) * (1 - v t) := by
    apply intervalIntegral.integral_congr_ae
    have hfloor' := (ae_restrict_iff' measurableSet_Icc).1 hfloor
    filter_upwards [hfloor'] with t ht hmem
    have hmem' : t ∈ Icc 0 γ := by
      simpa only [uIcc_of_le hγ0] using (Ioc_subset_Icc_self hmem)
    simp only [firstUnitLossDensity, ht hmem', sub_zero, mul_one]
  have hsum := intervalIntegral.integral_add_adjacent_intervals hD0γ hDγη
  rw [hfloor_eq] at hsum
  linarith

end AmbidextrousSofa.Analysis
