module

public import AmbidextrousSofa.Analysis.TiltedHarmonicMoments

@[expose] public section

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

theorem intervalIntegrable_firstUnitLossDensity
    {q v δ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hv : IntervalIntegrable v volume a b)
    (hδm : AEStronglyMeasurable δ (volume.restrict (Icc a b)))
    (hδ : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ δ t ∧ δ t ≤ 1) :
    IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume a b := by
  have hw : IntervalIntegrable (fun t => (q t + 1) * (1 - v t)) volume a b :=
    (intervalIntegrable_const.sub hv).continuousOn_mul (hq.continuousOn.add continuousOn_const)
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hw ⊢
  refine hw.mul_bdd (c := 1) (aestronglyMeasurable_const.sub hδm) ?_
  filter_upwards [hδ] with t ht
  exact abs_le.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩

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
  have hr0' := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hr0
  rcases le_total γ β with hγβ | hβγ
  · have hDγβ := hD.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le hγβ hβη))
    have hDβη := hD.mono_set (uIcc_subset_uIcc_right (mem_uIcc_of_le hγβ hβη))
    have hgood : 0 ≤ ∫ t in γ..β, D t := by
      refine intervalIntegral.integral_nonneg_of_ae_restrict hγβ ?_
      filter_upwards [ae_restrict_Icc_subinterval le_rfl hβη hbefore,
        ae_restrict_mem measurableSet_Icc] with t ht hmem using ht hmem.2
    have hpaid := intervalIntegral.integral_mono_ae_restrict hβη
      ((hr.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le hβη hηL))).const_mul (-k)) hDβη <| by
        filter_upwards [ae_restrict_Icc_subinterval hγβ le_rfl hafter,
          ae_restrict_mem measurableSet_Icc] with t ht hmem using ht hmem.1
    rw [intervalIntegral.integral_const_mul] at hpaid
    linarith [intervalIntegral.integral_add_adjacent_intervals hDγβ hDβη,
      mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_interval le_rfl hβη hηL hr0' hr) hk]
  · have hrγη := hr.mono_set (uIcc_subset_uIcc (mem_uIcc_of_le hβγ (hγη.trans hηL))
      (mem_uIcc_of_le (hβγ.trans hγη) hηL))
    have hpaid := intervalIntegral.integral_mono_ae_restrict hγη (hrγη.const_mul (-k)) hD <| by
      filter_upwards [hafter, ae_restrict_mem measurableSet_Icc] with t ht hmem
        using ht (hβγ.trans hmem.1)
    rw [intervalIntegral.integral_const_mul] at hpaid
    linarith [mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_interval hβγ hγη hηL hr0' hr) hk]

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
  have hD0γ := hD.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le hγ0 hγη))
  have hDγη := hD.mono_set (uIcc_subset_uIcc_right (mem_uIcc_of_le hγ0 hγη))
  -- the loss density is nonnegative wherever the companion density is at most one
  have hpos : ∀ᵐ t ∂volume.restrict (Icc γ η),
      v t ≤ 1 → 0 ≤ firstUnitLossDensity (q t) (v t) (δ t) := by
    filter_upwards [ae_restrict_Icc_subinterval hγ0 le_rfl hq0,
      ae_restrict_Icc_subinterval hγ0 le_rfl hδ] with t hqt hdt hv
    exact mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.2 hv)) (sub_nonneg.2 hdt.2)
  have hpaid := intervalIntegral_tail_paid hγη hβη hηL (by norm_num : (0 : ℝ) ≤ 5 / 16) hDγη
    (intervalIntegrable_const.sub hu)
    ((ae_restrict_Icc_subinterval hβ0 le_rfl hunit).mono fun t ht => sub_nonneg.2 ht)
    (by
      filter_upwards [hpos, ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Icc).1 hvbefore),
        ae_restrict_mem measurableSet_Icc] with t hp hv ht htβ
        using hp (hv ⟨hγ0.trans ht.1, htβ⟩))
    (by
      filter_upwards [hpos, ae_restrict_Icc_subinterval hγ0 le_rfl hq0,
        ae_restrict_Icc_subinterval hγ0 le_rfl hbad, ae_restrict_Icc_subinterval hγ0 le_rfl hδ,
        ae_restrict_Icc_subinterval hγ0 hηL hunit,
        ae_restrict_Icc_subinterval hγ0 hηL hfold] with t hp hqt hbt hdt hut hft _
      rcases le_or_gt (v t) 1 with hv | hv
      · linarith [hp hv]
      · exact firstUnit_lossDensity_lower_bound hqt (hbt hv) hdt.1 hdt.2 hut hft)
  have hfloor_eq : (∫ t in 0..γ, firstUnitLossDensity (q t) (v t) (δ t)) =
      ∫ t in 0..γ, (q t + 1) * (1 - v t) := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le hγ0]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hfloor] with t ht
    simp [firstUnitLossDensity, ht]
  linarith [intervalIntegral.integral_add_adjacent_intervals hD0γ hDγη]

end AmbidextrousSofa.Analysis
