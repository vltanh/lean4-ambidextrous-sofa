import AmbidextrousSofa.Analysis.TiltedInitialEnergy

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
  have hp' := hp.sub (absolutelyContinuousOnInterval_const_real A a b)
  have hq' := hq.sub (absolutelyContinuousOnInterval_const_real B a b)
  simpa only [momentumQuadraticEnergy, pow_two, Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using
    ((hp'.mul hp').add (hq'.mul hq')).add
      (absolutelyContinuousOnInterval_const_real K a b)

theorem hasDerivAt_momentumQuadraticEnergy
    {p q : ℝ → ℝ} {p' q' t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) (A B K : ℝ) :
    HasDerivAt (fun s => momentumQuadraticEnergy A B K (p s) (q s))
      (2 * (p t - A) * p' + 2 * (q t - B) * q') t := by
  apply ((((hp.sub_const A).pow 2).add ((hq.sub_const B).pow 2)).add_const K).congr_deriv
  ring

theorem ac_sub_le_intervalIntegral_of_ae_deriv_le
    {E F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hE : AbsolutelyContinuousOnInterval E a b)
    (hF : IntervalIntegrable F volume a b)
    (hbound : deriv E ≤ᵐ[volume.restrict (Icc a b)] F) :
    E b - E a ≤ ∫ t in a..b, F t := by
  have hi := intervalIntegral.integral_mono_ae_restrict hab
    hE.intervalIntegrable_deriv hF hbound
  rwa [hE.integral_deriv_eq_sub] at hi

theorem ae_restrict_Icc_subinterval {P : ℝ → Prop} {a b c d : ℝ}
    (hac : a ≤ c) (hdb : d ≤ b)
    (h : ∀ᵐ t ∂volume.restrict (Icc a b), P t) :
    ∀ᵐ t ∂volume.restrict (Icc c d), P t :=
  h.filter_mono (ae_mono (Measure.restrict_mono (Icc_subset_Icc hac hdb) le_rfl))

theorem firstUnitInitialEnergy_eq_core_at_zero (q : ℝ) :
    firstUnitInitialEnergy 0 q = firstUnitCoreEnergy 0 q := by
  unfold firstUnitInitialEnergy firstUnitCoreEnergy momentumQuadraticEnergy
  ring

theorem firstUnitCoreEnergy_eq_final_at_zero (p : ℝ) :
    firstUnitCoreEnergy p 0 = firstUnitFinalEnergy p 0 := by
  unfold firstUnitCoreEnergy firstUnitFinalEnergy momentumQuadraticEnergy
  ring

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
  have hbound : firstUnitInitialEnergy (p b) (q b) - firstUnitInitialEnergy (p a) (q a) ≤
      ∫ t in a..b, -firstUnitLossDensity (q t) (v t) (δ t) := by
    apply ac_sub_le_intervalIntegral_of_ae_deriv_le hab
      (absolutelyContinuousOnInterval_momentumQuadraticEnergy hp hq _ _ _) hD.neg
    filter_upwards [hode, hsource] with t ht hs
    have hd := hasDerivAt_momentumQuadraticEnergy ht.1 ht.2 (1 / 2) (-1) (3 / 4)
    change deriv (fun s => momentumQuadraticEnergy (1 / 2) (-1) (3 / 4) (p s) (q s)) t ≤ _
    rw [hd.deriv, hs.1]
    have hm := congrArg (fun x : ℝ => (q t + 1) * x) hs.2
    unfold firstUnitLossDensity
    nlinarith
  simpa only [intervalIntegral.integral_neg] using hbound

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
  have hbound : firstUnitCoreEnergy (p b) (q b) - firstUnitCoreEnergy (p a) (q a) ≤
      ∫ t in a..b, -firstUnitLossDensity (q t) (v t) (δ t) := by
    apply ac_sub_le_intervalIntegral_of_ae_deriv_le hab
      (absolutelyContinuousOnInterval_momentumQuadraticEnergy hp hq _ _ _) hD.neg
    filter_upwards [hode, hsource] with t ht hs
    have hd := hasDerivAt_momentumQuadraticEnergy ht.1 ht.2 1 (-1) 0
    change deriv (fun s => momentumQuadraticEnergy 1 (-1) 0 (p s) (q s)) t ≤ _
    rw [hd.deriv]
    have hm := congrArg (fun x : ℝ => (p t - 1) * x) hs.1
    have hn := congrArg (fun x : ℝ => (q t + 1) * x) hs.2
    unfold firstUnitLossDensity
    nlinarith
  simpa only [intervalIntegral.integral_neg] using hbound

theorem firstUnit_fractional_core_residual {p q u v δ χ : ℝ}
    (hu : u = q * χ) (hv : v = (1 - v) * δ - p * χ) :
    2 * (p - 1) * (u - 1 - q) + 2 * (q + 1) * (v - 1 + p) -
      (firstUnitGainDensity p u - firstUnitLossDensity q v δ) =
        (1 - χ) * (p + q) := by
  have hm := congrArg (fun x : ℝ => (p - 1) * x) hu
  have hn := congrArg (fun x : ℝ => (q + 1) * x) hv
  unfold firstUnitGainDensity firstUnitLossDensity
  nlinarith

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
  have hbound : firstUnitCoreEnergy (p b) (q b) - firstUnitCoreEnergy (p a) (q a) ≤
      ∫ t in a..b, firstUnitGainDensity (p t) (u t) -
        firstUnitLossDensity (q t) (v t) (δ t) := by
    apply ac_sub_le_intervalIntegral_of_ae_deriv_le hab
      (absolutelyContinuousOnInterval_momentumQuadraticEnergy hp hq _ _ _) (hG.sub hD)
    filter_upwards [hode, hsource, hχ] with t ht hs hc
    have hd := hasDerivAt_momentumQuadraticEnergy ht.1 ht.2 1 (-1) 0
    change deriv (fun s => momentumQuadraticEnergy 1 (-1) 0 (p s) (q s)) t ≤ _
    rw [hd.deriv]
    have hr := firstUnit_fractional_core_residual hs.1 hs.2
    have hnonpos : (1 - χ t) * (p t + q t) ≤ 0 := by
      rcases hc.2 with heq | hsum
      · rw [heq]; norm_num
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc.1) hsum
    linarith
  simpa only [intervalIntegral.integral_sub hG hD] using hbound

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
  apply ac_sub_le_intervalIntegral_of_ae_deriv_le hab
    (absolutelyContinuousOnInterval_momentumQuadraticEnergy hp hq _ _ _) hG
  filter_upwards [hode, hsource] with t ht hs
  have hd := hasDerivAt_momentumQuadraticEnergy ht.1 ht.2 1 (-1 / 2) (3 / 4)
  change deriv (fun s => momentumQuadraticEnergy 1 (-1 / 2) (3 / 4) (p s) (q s)) t ≤ _
  rw [hd.deriv]
  unfold firstUnitGainDensity
  rw [hs.1, hs.2]
  nlinarith

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
  have h0β : 0 ≤ β := h0α.trans hαβ
  have h0η : 0 ≤ η := h0β.trans hβη
  have h0L : 0 ≤ L := h0η.trans hηL
  have hαη : α ≤ η := hαβ.trans hβη
  have hαL : α ≤ L := hαη.trans hηL
  have hβL : β ≤ L := hβη.trans hηL
  have hsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
      uIcc a b ⊆ uIcc 0 L := by
    simpa only [uIcc_of_le hab, uIcc_of_le h0L] using (Icc_subset_Icc ha hb)
  have hD0α := hD.mono_set (show uIcc 0 α ⊆ uIcc 0 η by
    simpa only [uIcc_of_le h0α, uIcc_of_le h0η] using
      (Icc_subset_Icc (le_refl (0 : ℝ)) hαη))
  have hDαβ := hD.mono_set (show uIcc α β ⊆ uIcc 0 η by
    simpa only [uIcc_of_le hαβ, uIcc_of_le h0η] using (Icc_subset_Icc h0α hβη))
  have hDβη := hD.mono_set (show uIcc β η ⊆ uIcc 0 η by
    simpa only [uIcc_of_le hβη, uIcc_of_le h0η] using (Icc_subset_Icc h0β (le_refl η)))
  have hGβη := hG.mono_set (show uIcc β η ⊆ uIcc β L by
    simpa only [uIcc_of_le hβη, uIcc_of_le hβL] using (Icc_subset_Icc (le_refl β) hηL))
  have hGηL := hG.mono_set (show uIcc η L ⊆ uIcc β L by
    simpa only [uIcc_of_le hηL, uIcc_of_le hβL] using (Icc_subset_Icc hβη (le_refl L)))
  have h1 := firstUnit_initial_sector_energy h0α
    (hp.mono (hsub 0 α le_rfl h0α hαL)) (hq.mono (hsub 0 α le_rfl h0α hαL))
    hD0α (ae_restrict_Icc_subinterval le_rfl hαL hode) hfirst
  have h2 := firstUnit_charged_core_energy hαβ
    (hp.mono (hsub α β h0α hαβ hβL)) (hq.mono (hsub α β h0α hαβ hβL))
    hDαβ (ae_restrict_Icc_subinterval h0α hβL hode) hcharged
  have h3 := firstUnit_uncharged_core_energy hβη
    (hp.mono (hsub β η h0β hβη hηL)) (hq.mono (hsub β η h0β hβη hηL))
    hGβη hDβη (ae_restrict_Icc_subinterval h0β hηL hode) hcore hχ
  have h4 := firstUnit_final_sector_energy hηL
    (hp.mono (hsub η L h0η hηL le_rfl)) (hq.mono (hsub η L h0η hηL le_rfl))
    hGηL (ae_restrict_Icc_subinterval h0η le_rfl hode) hfinal
  have hglueα : firstUnitInitialEnergy (p α) (q α) = firstUnitCoreEnergy (p α) (q α) := by
    rw [hpα, firstUnitInitialEnergy_eq_core_at_zero]
  have hglueη : firstUnitCoreEnergy (p η) (q η) = firstUnitFinalEnergy (p η) (q η) := by
    rw [hqη, firstUnitCoreEnergy_eq_final_at_zero]
  have hDsum : (∫ t in 0..α, firstUnitLossDensity (q t) (v t) (δ t)) +
      (∫ t in α..β, firstUnitLossDensity (q t) (v t) (δ t)) +
      (∫ t in β..η, firstUnitLossDensity (q t) (v t) (δ t)) =
        ∫ t in 0..η, firstUnitLossDensity (q t) (v t) (δ t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hD0α hDαβ,
      intervalIntegral.integral_add_adjacent_intervals (hD0α.trans hDαβ) hDβη]
  have hGsum := intervalIntegral.integral_add_adjacent_intervals hGβη hGηL
  rw [hglueα] at h1
  rw [hglueη] at h3
  linarith

/-- The terminal polynomial is calculated from the actual momentum
traces and the two endpoint pressure laws. -/
theorem firstUnit_endpoint_energy_difference {C T h z eR eL : ℝ}
    (hR : eR = 1 / 2 + h / 4 + 3 * z / 4)
    (hL : eL = 1 / 2 - 3 * h / 4 - z / 4) :
    firstUnitFinalEnergy (1 - 3 * C - T) (-eL) -
      firstUnitInitialEnergy (eR + h) (3 * C - 1) =
        6 * C * T + T ^ 2 - (h + z) * (h + z / 2) := by
  rw [hR, hL]
  unfold firstUnitFinalEnergy firstUnitInitialEnergy momentumQuadraticEnergy
  ring

/-- Negative companion loss is paid by the actual fold excess. -/
theorem firstUnit_lossDensity_lower_bound {q v δ u : ℝ}
    (hq0 : -1 ≤ q) (hq1 : q ≤ 1 / 4)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hu : u ≤ 1)
    (hfold : max (v - 1) 0 ≤ (1 - u) / 4) :
    -(5 / 16) * (1 - u) ≤ firstUnitLossDensity q v δ := by
  by_cases hv : v ≤ 1
  · have hn : 0 ≤ firstUnitLossDensity q v δ :=
      mul_nonneg (mul_nonneg (by linarith) (sub_nonneg.mpr hv))
        (sub_nonneg.mpr hδ1)
    have hu0 : 0 ≤ 1 - u := sub_nonneg.mpr hu
    linarith
  · have hv0 : 0 ≤ v - 1 := by linarith
    have hfold' : v - 1 ≤ (1 - u) / 4 := (le_max_left _ _).trans hfold
    have hqd : (q + 1) * (1 - δ) ≤ 5 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left
        (show 1 - δ ≤ 1 by linarith) (show 0 ≤ q + 1 by linarith)
      nlinarith
    have hprod := mul_le_mul_of_nonneg_right hqd hv0
    unfold firstUnitLossDensity
    nlinarith

theorem firstUnit_foldPayment_le {T s : ℝ} (hT : 0 ≤ T) (hs : 3 / 5 ≤ s) :
    5 * T / (16 * s) ≤ 25 / 48 * T := by
  apply (div_le_iff₀ (by linarith : 0 < 16 * s)).2
  nlinarith [mul_nonneg hT (show 0 ≤ s - 3 / 5 by linarith)]

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
  rw [firstUnit_endpoint_energy_difference hR hL, hIB, hID, hR, hL] at henergy
  nlinarith

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
  have hdisplace : (S - T) * ((S + T) / 2 - 3 * C) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hST) (by linarith)
  have hendpoint : (z - h) * (2 - h - z) / 4 ≤ z / 2 := by
    have hprod := mul_nonneg hh (show 0 ≤ 2 - h - z by linarith)
    nlinarith [sq_nonneg z, mul_nonneg hh hz]
  have hlarge : 3 * T < 6 * C * T := by nlinarith [mul_pos (by linarith : 0 < C - 1 / 2) hT]
  linarith

end AmbidextrousSofa.Analysis
