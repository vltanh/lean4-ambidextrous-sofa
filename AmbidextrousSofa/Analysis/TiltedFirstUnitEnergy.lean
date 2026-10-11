module

public import AmbidextrousSofa.Analysis.TiltedInitialEnergy

@[expose] public section

/-!
# The first-unit momentum energy with a companion fold defect

The four sector estimates below are integrations of the actual momentum
ODE and the fractional exposed-source equalities. Their gluing retains
the entire companion loss, including its negative part where the
companion density exceeds one. The final scalar contradiction separately
records the endpoint pressure, harmonic moment, and fold-budget inputs.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa.Analysis

def momentumQuadraticEnergy (a b k p q : ℝ) : ℝ :=
  (p - a) ^ 2 + (q - b) ^ 2 + k

def firstUnitInitialEnergy (p q : ℝ) : ℝ :=
  momentumQuadraticEnergy (1 / 2) (-1) (3 / 4) p q

def firstUnitCoreEnergy (p q : ℝ) : ℝ := momentumQuadraticEnergy 1 (-1) 0 p q

def firstUnitFinalEnergy (p q : ℝ) : ℝ :=
  momentumQuadraticEnergy 1 (-1 / 2) (3 / 4) p q

def firstUnitGainDensity (p u : ℝ) : ℝ := (1 - p) * (1 - u)

def firstUnitLossDensity (q v δ : ℝ) : ℝ := (q + 1) * (1 - v) * (1 - δ)

theorem absolutelyContinuousOnInterval_momentumQuadraticEnergy
    {p q : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (A B K : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => momentumQuadraticEnergy A B K (p t) (q t)) a b := by
  have hp' := hp.fun_sub (absolutelyContinuousOnInterval_const_real A a b)
  have hq' := hq.fun_sub (absolutelyContinuousOnInterval_const_real B a b)
  simpa only [momentumQuadraticEnergy, pow_two] using ((hp'.fun_mul hp').fun_add
    (hq'.fun_mul hq')).fun_add (absolutelyContinuousOnInterval_const_real K a b)

theorem hasDerivAt_momentumQuadraticEnergy
    {p q : ℝ → ℝ} {p' q' t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) (A B K : ℝ) :
    HasDerivAt (fun s => momentumQuadraticEnergy A B K (p s) (q s))
      (2 * (p t - A) * p' + 2 * (q t - B) * q') t := by
  apply ((((hp.sub_const A).pow 2).add ((hq.sub_const B).pow 2)).add_const K).congr_deriv
  ring

/-- Integration of a quadratic momentum energy along the momentum ODE, given an almost-everywhere
bound on its derivative. -/
theorem momentumQuadraticEnergy_sub_le {p q u v F : ℝ → ℝ} {a b A B K : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b) (hq : AbsolutelyContinuousOnInterval q a b)
    (hF : IntervalIntegrable F volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hle : ∀ᵐ t ∂volume.restrict (Icc a b),
      2 * (p t - A) * (u t - 1 - q t) + 2 * (q t - B) * (v t - 1 + p t) ≤ F t) :
    momentumQuadraticEnergy A B K (p b) (q b) - momentumQuadraticEnergy A B K (p a) (q a) ≤
      ∫ t in a..b, F t := by
  have hE := absolutelyContinuousOnInterval_momentumQuadraticEnergy hp hq A B K
  rw [← hE.integral_deriv_eq_sub]
  refine intervalIntegral.integral_mono_ae_restrict hab hE.intervalIntegrable_deriv hF ?_
  filter_upwards [hode, hle] with t ht hle
  rwa [(hasDerivAt_momentumQuadraticEnergy ht.1 ht.2 A B K).deriv]

theorem ae_restrict_Icc_subinterval {P : ℝ → Prop} {a b c d : ℝ}
    (hac : a ≤ c) (hdb : d ≤ b)
    (h : ∀ᵐ t ∂volume.restrict (Icc a b), P t) :
    ∀ᵐ t ∂volume.restrict (Icc c d), P t :=
  ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hac hdb) h

theorem firstUnitInitialEnergy_eq_core_at_zero (q : ℝ) :
    firstUnitInitialEnergy 0 q = firstUnitCoreEnergy 0 q := by
  unfold firstUnitInitialEnergy firstUnitCoreEnergy momentumQuadraticEnergy; ring

theorem firstUnitCoreEnergy_eq_final_at_zero (p : ℝ) :
    firstUnitCoreEnergy p 0 = firstUnitFinalEnergy p 0 := by
  unfold firstUnitCoreEnergy firstUnitFinalEnergy momentumQuadraticEnergy; ring

theorem firstUnit_initial_sector_energy
    {p q u v δ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Icc a b),
      u t = 0 ∧ v t = (1 - v t) * δ t) :
    firstUnitInitialEnergy (p b) (q b) - firstUnitInitialEnergy (p a) (q a) ≤
      -(∫ t in a..b, firstUnitLossDensity (q t) (v t) (δ t)) := by
  rw [← intervalIntegral.integral_neg]
  refine momentumQuadraticEnergy_sub_le hab hp hq hD.neg hode ?_
  filter_upwards [hsource] with t ⟨hu, hv⟩
  unfold firstUnitLossDensity
  linear_combination (2 * p t - 1) * hu + (q t + 1) * hv

theorem firstUnit_charged_core_energy
    {p q u v δ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Icc a b),
      u t = (1 - u t) + q t ∧ v t = (1 - v t) * δ t - p t) :
    firstUnitCoreEnergy (p b) (q b) - firstUnitCoreEnergy (p a) (q a) ≤
      -(∫ t in a..b, firstUnitLossDensity (q t) (v t) (δ t)) := by
  rw [← intervalIntegral.integral_neg]
  refine momentumQuadraticEnergy_sub_le hab hp hq hD.neg hode ?_
  filter_upwards [hsource] with t ⟨hu, hv⟩
  unfold firstUnitLossDensity
  linear_combination (p t - 1) * hu + (q t + 1) * hv

theorem firstUnit_uncharged_core_energy
    {p q u v δ χ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hG : IntervalIntegrable (fun t => firstUnitGainDensity (p t) (u t)) volume a b)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Icc a b),
      u t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t)
    (hχ : ∀ᵐ t ∂volume.restrict (Icc a b), χ t ≤ 1 ∧ (χ t = 1 ∨ p t + q t ≤ 0)) :
    firstUnitCoreEnergy (p b) (q b) - firstUnitCoreEnergy (p a) (q a) ≤
      (∫ t in a..b, firstUnitGainDensity (p t) (u t)) -
        ∫ t in a..b, firstUnitLossDensity (q t) (v t) (δ t) := by
  rw [← intervalIntegral.integral_sub hG hD]
  refine momentumQuadraticEnergy_sub_le hab hp hq (hG.sub hD) hode ?_
  filter_upwards [hsource, hχ] with t ⟨hu, hv⟩ ⟨hχ1, hχ⟩
  have hres : (1 - χ t) * (p t + q t) ≤ 0 := by
    rcases hχ with h | h
    · simp [h]
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hχ1) h
  unfold firstUnitGainDensity firstUnitLossDensity
  linear_combination (p t - 1) * hu + (q t + 1) * hv + hres

theorem firstUnit_final_sector_energy
    {p q u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hG : IntervalIntegrable (fun t => firstUnitGainDensity (p t) (u t)) volume a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Icc a b), u t = 0 ∧ v t = 0) :
    firstUnitFinalEnergy (p b) (q b) - firstUnitFinalEnergy (p a) (q a) ≤
      ∫ t in a..b, firstUnitGainDensity (p t) (u t) := by
  refine momentumQuadraticEnergy_sub_le hab hp hq hG hode ?_
  filter_upwards [hsource] with t ⟨hu, hv⟩
  unfold firstUnitGainDensity
  linear_combination (p t - 1) * hu + (2 * q t + 1) * hv

/-- Four actual source sectors glue at `p α=0` and `q η=0`. The
companion loss is integrated through every fold up to `η`. -/
theorem firstUnit_momentum_energy_balance
    {p q u v δ χ : ℝ → ℝ} {α β η L : ℝ}
    (h0α : 0 ≤ α) (hαβ : α ≤ β) (hβη : β ≤ η) (hηL : η ≤ L)
    (hp : AbsolutelyContinuousOnInterval p 0 L)
    (hq : AbsolutelyContinuousOnInterval q 0 L)
    (hG : IntervalIntegrable (fun t => firstUnitGainDensity (p t) (u t)) volume β L)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume 0 η)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hfirst : ∀ᵐ t ∂volume.restrict (Icc 0 α),
      u t = 0 ∧ v t = (1 - v t) * δ t)
    (hcharged : ∀ᵐ t ∂volume.restrict (Icc α β),
      u t = (1 - u t) + q t ∧ v t = (1 - v t) * δ t - p t)
    (hcore : ∀ᵐ t ∂volume.restrict (Icc β η),
      u t = q t * χ t ∧ v t = (1 - v t) * δ t - p t * χ t)
    (hχ : ∀ᵐ t ∂volume.restrict (Icc β η), χ t ≤ 1 ∧ (χ t = 1 ∨ p t + q t ≤ 0))
    (hfinal : ∀ᵐ t ∂volume.restrict (Icc η L), u t = 0 ∧ v t = 0)
    (hpα : p α = 0) (hqη : q η = 0) :
    firstUnitFinalEnergy (p L) (q L) - firstUnitInitialEnergy (p 0) (q 0) ≤
      (∫ t in β..L, firstUnitGainDensity (p t) (u t)) -
        ∫ t in 0..η, firstUnitLossDensity (q t) (v t) (δ t) := by
  have h0β := h0α.trans hαβ
  have h0η := h0β.trans hβη
  have hβL := hβη.trans hηL
  have hαL := hαβ.trans hβL
  have hsub {a b c d : ℝ} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d) : uIcc a b ⊆ uIcc c d :=
    uIcc_subset_uIcc (mem_uIcc_of_le hca (hab.trans hbd)) (mem_uIcc_of_le (hca.trans hab) hbd)
  have hD1 := hD.mono_set (hsub le_rfl h0α (hαβ.trans hβη))
  have hD2 := hD.mono_set (hsub h0α hαβ hβη)
  have hD3 := hD.mono_set (hsub h0β hβη le_rfl)
  have hG1 := hG.mono_set (hsub le_rfl hβη hηL)
  have hG2 := hG.mono_set (hsub hβη hηL le_rfl)
  have h1 := firstUnit_initial_sector_energy h0α (hp.mono (hsub le_rfl h0α hαL))
    (hq.mono (hsub le_rfl h0α hαL)) hD1 (ae_restrict_Icc_subinterval le_rfl hαL hode) hfirst
  have h2 := firstUnit_charged_core_energy hαβ (hp.mono (hsub h0α hαβ hβL))
    (hq.mono (hsub h0α hαβ hβL)) hD2 (ae_restrict_Icc_subinterval h0α hβL hode) hcharged
  have h3 := firstUnit_uncharged_core_energy hβη (hp.mono (hsub h0β hβη hηL))
    (hq.mono (hsub h0β hβη hηL)) hG1 hD3 (ae_restrict_Icc_subinterval h0β hηL hode) hcore hχ
  have h4 := firstUnit_final_sector_energy hηL (hp.mono (hsub h0η hηL le_rfl))
    (hq.mono (hsub h0η hηL le_rfl)) hG2 (ae_restrict_Icc_subinterval h0η le_rfl hode) hfinal
  rw [hpα] at h1 h2
  rw [hqη] at h3 h4
  linarith [firstUnitInitialEnergy_eq_core_at_zero (q α),
    firstUnitCoreEnergy_eq_final_at_zero (p η), intervalIntegral.integral_add_adjacent_intervals
      hD1 hD2, intervalIntegral.integral_add_adjacent_intervals (hD1.trans hD2) hD3,
    intervalIntegral.integral_add_adjacent_intervals hG1 hG2]

/-- Negative companion loss is paid by the actual fold excess. -/
theorem firstUnit_lossDensity_lower_bound {q v δ u : ℝ}
    (hq0 : -1 ≤ q) (hq1 : q ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hu : u ≤ 1)
    (hfold : max (v - 1) 0 ≤ (1 - u) / 4) :
    -(5 / 16) * (1 - u) ≤ firstUnitLossDensity q v δ := by
  have hv := (le_max_left _ _).trans hfold
  have hq : 0 ≤ q + 1 := by linarith
  unfold firstUnitLossDensity
  rcases le_total v 1 with h | h
  · linarith [mul_nonneg (mul_nonneg hq (sub_nonneg.2 h)) (sub_nonneg.2 hδ1)]
  · linarith [mul_nonneg (mul_nonneg hq hδ0) (sub_nonneg.2 h),
      mul_nonneg (by linarith : 0 ≤ 1 / 4 - q) (sub_nonneg.2 h)]

theorem firstUnit_foldPayment_le {T s : ℝ} (hT : 0 ≤ T) (hs : 3 / 5 ≤ s) :
    5 * T / (16 * s) ≤ 25 / 48 * T := by
  rw [div_le_iff₀ (by positivity)]
  linarith [mul_nonneg hT (show 0 ≤ s - 3 / 5 by linarith)]

/-- The exact algebra preceding GF's scalar estimate. `IB` and `ID`
are ordinary weighted momentum integrals; their hypotheses state the
harmonic reconstructions with the actual convolution remainders. -/
theorem firstUnit_balance_after_endpoint_substitution
    {C T S h z eR eL IB ID RB RD P : ℝ}
    (hR : eR = 1 / 2 + h / 4 + 3 * z / 4)
    (hL : eL = 1 / 2 - 3 * h / 4 - z / 4)
    (hIB : IB = 3 * C * T + T ^ 2 / 2 + eL * z - z ^ 2 / 2 + RB)
    (hID : ID = 3 * C * S - S ^ 2 / 2 + eR * h + h ^ 2 / 2 + RD)
    (henergy : firstUnitFinalEnergy (1 - 3 * C - T) (-eL) -
      firstUnitInitialEnergy (eR + h) (3 * C - 1) ≤ IB - ID + P) :
    6 * C * T ≤ (z - h) * (2 - h - z) / 4 + RB - RD +
      (S - T) * ((S + T) / 2 - 3 * C) + P := by
  subst hR hL hIB hID
  unfold firstUnitFinalEnergy firstUnitInitialEnergy momentumQuadraticEnergy at henergy
  linarith

/-- The nonsharp scalar endpoint of GF. Its premises are the
first-floor displacement bounds and the three independently paid
moment budgets. The numerical contradiction has a fixed rational gap. -/
theorem firstUnit_terminal_contradiction
    {C T S h z RB RD P : ℝ}
    (hC : 1 / 2 < C) (hT : 0 < T) (hST : T ≤ S) (hS : S ≤ 1) (hTC : T ≤ C)
    (hh : 0 ≤ h) (hz : 0 ≤ z) (hhz : h + z ≤ 2)
    (hzT : z ≤ 4 / 3 * T) (hRB : RB ≤ 5 / 6 * T) (hRD : 0 ≤ RD)
    (hP : P ≤ 25 / 48 * T)
    (hbalance : 6 * C * T ≤ (z - h) * (2 - h - z) / 4 + RB - RD +
      (S - T) * ((S + T) / 2 - 3 * C) + P) : False := by
  have _ := hTC -- not needed by the proof; it stays in the statement for the callers
  linarith [mul_nonneg (sub_nonneg.2 hST) (by linarith : 0 ≤ 3 * C - (S + T) / 2), sq_nonneg z,
    mul_nonneg hh (by linarith : 0 ≤ 2 - h), mul_pos (by linarith : 0 < C - 1 / 2) hT]

end AmbidextrousSofa.Analysis
