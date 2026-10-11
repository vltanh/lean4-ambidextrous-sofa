module

public import AmbidextrousSofa.Analysis.TiltedFoldPayment

@[expose] public section

/-!
# The first-unit contradiction from raw analytic data

This theorem takes the actual momentum ODE, four fractional source
equations, endpoint traces, and four displacement moments as explicit
premises. It derives the harmonic identities, the complete fold payment,
and the final strict scalar contradiction. Constructing these premises
from a tilted maximizing cap is a separate geometric task; no universal
cap or original-body conclusion is asserted here.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

/-- Raw first-unit data are inconsistent. Every curvature, occupation, floor,
and endpoint hypothesis is stated explicitly rather than bundled as a
sharp-value or maximizing-cap certificate. -/
theorem firstUnit_raw_momentum_data_impossible
    {p q u v δ χ : ℝ → ℝ} {α β γ η C T S h z eR eL : ℝ}
    (h0α : 0 ≤ α) (hαβ : α ≤ β) (hβη : β ≤ η) (hηL : η ≤ Real.pi / 2)
    (hγ0 : 0 ≤ γ) (hγη : γ ≤ η)
    (hp : AbsolutelyContinuousOnInterval p 0 (Real.pi / 2))
    (hq : AbsolutelyContinuousOnInterval q 0 (Real.pi / 2))
    (hu : IntervalIntegrable u volume 0 (Real.pi / 2))
    (hv : IntervalIntegrable v volume 0 (Real.pi / 2))
    (hδm : AEStronglyMeasurable δ (volume.restrict (Icc 0 η)))
    (hδ : ∀ᵐ t ∂volume.restrict (Icc 0 η), 0 ≤ δ t ∧ δ t ≤ 1)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hfirst : ∀ᵐ t ∂volume.restrict (Icc 0 α),
      u t = 0 ∧ v t = (1 - v t) * δ t)
    (hcharged : ∀ᵐ t ∂volume.restrict (Icc α β),
      u t = (1 - u t) + q t ∧ v t = (1 - v t) * δ t - p t)
    (hcore : ∀ᵐ t ∂volume.restrict (Icc β η),
      u t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t)
    (hχ : ∀ᵐ t ∂volume.restrict (Icc β η), χ t ≤ 1 ∧ (χ t = 1 ∨ p t + q t ≤ 0))
    (hfinal : ∀ᵐ t ∂volume.restrict (Icc η (Real.pi / 2)), u t = 0 ∧ v t = 0)
    (hpα : p α = 0) (hqη : q η = 0)
    (hunit : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)), 0 ≤ u t ∧ u t ≤ 1)
    (hfloor : ∀ᵐ t ∂volume.restrict (Icc 0 γ), δ t = 0)
    (hvfloor : ∀ᵐ t ∂volume.restrict (Icc 0 γ), v t ≤ 1)
    (hvbefore : ∀ᵐ t ∂volume.restrict (Icc 0 β), v t ≤ 1)
    (hqnonneg : ∀ᵐ t ∂volume.restrict (Icc 0 η), -1 ≤ q t)
    (hbad : ∀ᵐ t ∂volume.restrict (Icc 0 η), 1 < v t → q t ≤ 1 / 4)
    (hfold : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)),
      max (v t - 1) 0 ≤ (1 - u t) / 4)
    (hp0 : p 0 = eR + h) (hq0 : q 0 = 3 * C - 1)
    (hpL : p (Real.pi / 2) = 1 - 3 * C - T) (hqL : q (Real.pi / 2) = -eL)
    (hR : eR = 1 / 2 + h / 4 + 3 * z / 4)
    (hL : eL = 1 / 2 - 3 * h / 4 - z / 4)
    (hS : (∫ t in 0..γ, (1 - v t) * Real.cos t) = S)
    (hh : (∫ t in 0..γ, (1 - v t) * Real.sin t) = h)
    (hT : (∫ t in β..(Real.pi / 2), (1 - u t) * Real.sin t) = T)
    (hz : (∫ t in β..(Real.pi / 2), (1 - u t) * Real.cos t) = z)
    (hC : 1 / 2 < C) (hTpos : 0 < T) (hST : T ≤ S) (hSone : S ≤ 1) (hTC : T ≤ C)
    (hhz : h + z ≤ 2) (hβsin : 3 / 5 ≤ Real.sin β) : False := by
  have hβ0 : 0 ≤ β := h0α.trans hαβ
  have h0η : 0 ≤ η := hβ0.trans hβη
  have hβL : β ≤ Real.pi / 2 := hβη.trans hηL
  have hγL : γ ≤ Real.pi / 2 := hγη.trans hηL
  have hsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
      uIcc a b ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le ha (hab.trans hb)) (mem_uIcc_of_le (ha.trans hab) hb)
  have hB := hsub hβ0 hβL le_rfl
  have hΓ := hsub le_rfl hγ0 hγL
  have hrB : IntervalIntegrable (fun t => 1 - u t) volume β (Real.pi / 2) :=
    intervalIntegrable_const.sub (hu.mono_set hB)
  have hrB0 : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), 0 ≤ 1 - u t :=
    (ae_restrict_Icc_subinterval hβ0 le_rfl hunit).mono fun t ht => sub_nonneg.2 ht.2
  have hrD0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ 1 - v t :=
    hvfloor.mono fun t ht => sub_nonneg.2 ht
  have hD := intervalIntegrable_firstUnitLossDensity h0η (hq.mono (hsub le_rfl h0η hηL))
    (hv.mono_set (hsub le_rfl h0η hηL)) hδm hδ
  have henergy := firstUnit_momentum_energy_balance h0α hαβ hβη hηL hp hq
    (hrB.continuousOn_mul (continuousOn_const.sub (hp.mono hB).continuousOn)) hD
    hode hfirst hcharged hcore hχ hfinal hpα hqη
  have hpaid := firstUnit_loss_integral_lower_bound hγ0 hγη hβ0 hβη hηL hD (hu.mono_set hB)
    hfloor hqnonneg hδ hvbefore hbad (hunit.mono fun t ht => ht.2) hfold
  rw [hpL, hqL, hp0, hq0] at henergy
  have hIB := firstUnit_right_harmonic_moment hβL (hp.mono hB) (hq.mono hB) (hu.mono_set hB)
    (hv.mono_set hB) (ae_restrict_Icc_subinterval hβ0 le_rfl hode) hpL hqL hT hz
  have hID := firstUnit_initial_harmonic_moment hγ0 (hp.mono hΓ) (hq.mono hΓ) (hu.mono_set hΓ)
    (hv.mono_set hΓ) (ae_restrict_Icc_subinterval le_rfl hγL hode) hp0 hq0 hS hh
  have hbalance := firstUnit_balance_after_endpoint_substitution
    (P := 5 / 16 * ∫ t in β..(Real.pi / 2), 1 - u t) hR hL hIB hID (by linarith)
  have hvbound : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), v t ≤ 5 / 4 := by
    filter_upwards [ae_restrict_Icc_subinterval hβ0 le_rfl hfold,
      ae_restrict_Icc_subinterval hβ0 le_rfl hunit] with t hft hut
    linarith [(le_max_left _ _).trans hft, hut.1]
  have hRB := firstUnitRightRemainder_le hβ0 hβL hβsin hrB (hv.mono_set hB) hrB0 hvbound
  have hRD := firstUnitLeftRemainder_nonneg hγ0 hγL hrD0
    (ae_restrict_Icc_subinterval le_rfl hγL (hunit.mono fun t ht => ht.1))
  obtain ⟨-, hmass, hzT⟩ := firstUnit_right_window_moment_bounds hβ0 hβL hβsin hrB hrB0
  rw [hT] at hRB hmass hzT
  rw [hz] at hzT
  have hh0 : 0 ≤ h := hh ▸ intervalIntegral.integral_nonneg_of_ae_restrict hγ0 (by
    filter_upwards [hrD0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    exact mul_nonneg hrt (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2])))
  have hz0 : 0 ≤ z := hz ▸ intervalIntegral.integral_nonneg_of_ae_restrict hβL (by
    filter_upwards [hrB0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    exact mul_nonneg hrt (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [ht.1]) ht.2))
  exact firstUnit_terminal_contradiction hC hTpos hST hSone hTC hh0 hz0 hhz
    hzT hRB hRD (by linarith) hbalance

end AmbidextrousSofa.Analysis
