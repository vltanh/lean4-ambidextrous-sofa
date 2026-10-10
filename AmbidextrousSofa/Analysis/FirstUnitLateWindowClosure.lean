module

public import AmbidextrousSofa.Analysis.TiltedFirstUnitClosure
public import AmbidextrousSofa.Measure.SupportAreaAC

@[expose] public section

/-!
# The companion-unit contradiction with either window order

The charged first tangent may cross the middle endpoint after the second
momentum has become negative. On that intervening interval the actual
source equations are `u = 1/2, v = 0`, and the final quadratic energy is
constant. This extra sector joins the same endpoint energy and harmonic
moments as the ordinary ordering. No assumption that `β ≤ η` is needed.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa.Analysis

theorem firstUnit_final_charged_sector_energy_eq
    {p q u v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hode : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Icc a b), u t = 1 / 2 ∧ v t = 0) :
    firstUnitFinalEnergy (p b) (q b) = firstUnitFinalEnergy (p a) (q a) := by
  let E : ℝ → ℝ := fun t => firstUnitFinalEnergy (p t) (q t)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    absolutelyContinuousOnInterval_momentumQuadraticEnergy hp hq 1 (-1 / 2) (3 / 4)
  have hEd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt E 0 t := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hode,
      ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hsource] with t hd hs
    apply (hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1 / 2) (3 / 4)).congr_deriv
    rw [hs.1, hs.2]
    ring
  have hFTC := integral_eq_sub_of_ac_of_ae_hasDerivAt hab hE hEd
  rw [intervalIntegral.integral_zero] at hFTC
  change 0 = firstUnitFinalEnergy (p b) (q b) - firstUnitFinalEnergy (p a) (q a) at hFTC
  linarith only [hFTC]

/-- The minimum and maximum endpoints specify the actual two possible
orders. The collapsed extra intervals have zero measure. -/
theorem firstUnit_unit_companion_energy_balance
    {p q u v δ : ℝ → ℝ} {α β η L : ℝ}
    (h0α : 0 ≤ α) (hαβ : α ≤ β) (hαη : α ≤ η) (hβL : β ≤ L) (hηL : η ≤ L)
    (hp : AbsolutelyContinuousOnInterval p 0 L)
    (hq : AbsolutelyContinuousOnInterval q 0 L)
    (hG : IntervalIntegrable (fun t => firstUnitGainDensity (p t) (u t)) volume β L)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume 0 η)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 L),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hfirst : ∀ᵐ t ∂volume.restrict (Icc 0 α), u t = 0 ∧ v t = (1 - v t) * δ t)
    (hcharged : ∀ᵐ t ∂volume.restrict (Icc α (min β η)),
      u t = (1 - u t) + q t ∧ v t = (1 - v t) * δ t - p t)
    (hcore : ∀ᵐ t ∂volume.restrict (Icc (min β η) η),
      u t = q t ∧ v t = (1 - v t) * δ t - p t)
    (hlate : ∀ᵐ t ∂volume.restrict (Icc η (max β η)), u t = 1 / 2 ∧ v t = 0)
    (hfinal : ∀ᵐ t ∂volume.restrict (Icc (max β η) L), u t = 0 ∧ v t = 0)
    (hpα : p α = 0) (hqη : q η = 0) :
    firstUnitFinalEnergy (p L) (q L) - firstUnitInitialEnergy (p 0) (q 0) ≤
      (∫ t in β..L, firstUnitGainDensity (p t) (u t)) -
        ∫ t in 0..η, firstUnitLossDensity (q t) (v t) (δ t) := by
  by_cases hβη : β ≤ η
  · apply firstUnit_momentum_energy_balance (χ := fun _ => 1)
      h0α hαβ hβη hηL hp hq hG hD hode hfirst
    · simpa only [min_eq_left hβη] using hcharged
    · simpa only [min_eq_left hβη, mul_one] using hcore
    · exact Filter.Eventually.of_forall (fun _ => ⟨le_rfl, Or.inl rfl⟩)
    · simpa only [max_eq_right hβη] using hfinal
    · exact hpα
    · exact hqη
  · have hηβ : η ≤ β := (lt_of_not_ge hβη).le
    have h0η : 0 ≤ η := h0α.trans hαη
    have h0β : 0 ≤ β := h0α.trans hαβ
    have h0L : 0 ≤ L := h0β.trans hβL
    have hsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
        uIcc a b ⊆ uIcc 0 L := by
      simpa only [uIcc_of_le hab, uIcc_of_le h0L] using Icc_subset_Icc ha hb
    have hD0α := hD.mono_set (show uIcc 0 α ⊆ uIcc 0 η by
      simpa only [uIcc_of_le h0α, uIcc_of_le h0η] using Icc_subset_Icc le_rfl hαη)
    have hDαη := hD.mono_set (show uIcc α η ⊆ uIcc 0 η by
      simpa only [uIcc_of_le hαη, uIcc_of_le h0η] using Icc_subset_Icc h0α le_rfl)
    have h1 := firstUnit_initial_sector_energy h0α
      (hp.mono (hsub 0 α le_rfl h0α (hαη.trans hηL)))
      (hq.mono (hsub 0 α le_rfl h0α (hαη.trans hηL))) hD0α
      (ae_restrict_Icc_subinterval le_rfl (hαη.trans hηL) hode) hfirst
    have h2 := firstUnit_charged_core_energy hαη
      (hp.mono (hsub α η h0α hαη hηL)) (hq.mono (hsub α η h0α hαη hηL)) hDαη
      (ae_restrict_Icc_subinterval h0α hηL hode)
      (by simpa only [min_eq_right hηβ] using hcharged)
    have hflat := firstUnit_final_charged_sector_energy_eq hηβ
      (hp.mono (hsub η β h0η hηβ hβL)) (hq.mono (hsub η β h0η hηβ hβL))
      (ae_restrict_Icc_subinterval h0η hβL hode)
      (by simpa only [max_eq_left hηβ] using hlate)
    have h3 := firstUnit_final_sector_energy hβL
      (hp.mono (hsub β L h0β hβL le_rfl)) (hq.mono (hsub β L h0β hβL le_rfl)) hG
      (ae_restrict_Icc_subinterval h0β le_rfl hode)
      (by simpa only [max_eq_left hηβ] using hfinal)
    have hglueα : firstUnitInitialEnergy (p α) (q α) = firstUnitCoreEnergy (p α) (q α) := by
      rw [hpα, firstUnitInitialEnergy_eq_core_at_zero]
    have hglueη : firstUnitCoreEnergy (p η) (q η) = firstUnitFinalEnergy (p η) (q η) := by
      rw [hqη, firstUnitCoreEnergy_eq_final_at_zero]
    have hsum := intervalIntegral.integral_add_adjacent_intervals hD0α hDαη
    rw [hglueα] at h1
    rw [hglueη] at h2
    linarith only [h1, h2, hflat, h3, hsum]

theorem firstUnit_loss_integral_lower_bound_of_companion_unit
    {q v δ : ℝ → ℝ} {γ η : ℝ} (hγ0 : 0 ≤ γ) (hγη : γ ≤ η)
    (hD : IntervalIntegrable (fun t => firstUnitLossDensity (q t) (v t) (δ t)) volume 0 η)
    (hfloor : ∀ᵐ t ∂volume.restrict (Icc 0 γ), δ t = 0)
    (hq0 : ∀ᵐ t ∂volume.restrict (Icc 0 η), -1 ≤ q t)
    (hv : ∀ᵐ t ∂volume.restrict (Icc 0 η), v t ≤ 1)
    (hδ : ∀ᵐ t ∂volume.restrict (Icc 0 η), δ t ≤ 1) :
    (∫ t in 0..γ, (q t + 1) * (1 - v t)) ≤
      ∫ t in 0..η, firstUnitLossDensity (q t) (v t) (δ t) := by
  have hnonneg : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) η),
      0 ≤ firstUnitLossDensity (q t) (v t) (δ t) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hq0,
      ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hv,
      ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hδ] with t hq hv hd
    exact mul_nonneg (mul_nonneg (by linarith only [hq]) (sub_nonneg.mpr hv))
      (sub_nonneg.mpr hd)
  have hmono := intervalIntegral.integral_mono_interval le_rfl hγ0 hγη hnonneg hD
  have hfloor_eq : (∫ t in 0..γ, firstUnitLossDensity (q t) (v t) (δ t)) =
      ∫ t in 0..γ, (q t + 1) * (1 - v t) := by
    apply intervalIntegral.integral_congr_ae
    have hfloor' := (ae_restrict_iff' measurableSet_Icc).mp hfloor
    filter_upwards [hfloor'] with t ht hmem
    have hmem' : t ∈ Icc 0 γ := by
      simpa only [min_eq_left hγ0, max_eq_right hγ0] using Ioc_subset_Icc_self hmem
    simp only [firstUnitLossDensity, ht hmem', sub_zero, mul_one]
  rwa [hfloor_eq] at hmono

/-- Raw companion-unit data are inconsistent for either order of the
middle tangent crossing and the second momentum zero. The exact source
equations and four geometric moments remain explicit analytic inputs;
the actual geometric application constructs them separately. -/
theorem firstUnit_unit_companion_raw_data_impossible
    {p q u v δ : ℝ → ℝ} {α β γ η C T S h z eR eL : ℝ}
    (h0α : 0 ≤ α) (hαβ : α ≤ β) (hαη : α ≤ η)
    (hβL : β ≤ Real.pi / 2) (hηL : η ≤ Real.pi / 2)
    (hγ0 : 0 ≤ γ) (hγη : γ ≤ η)
    (hp : AbsolutelyContinuousOnInterval p 0 (Real.pi / 2))
    (hq : AbsolutelyContinuousOnInterval q 0 (Real.pi / 2))
    (hu : IntervalIntegrable u volume 0 (Real.pi / 2))
    (hv : IntervalIntegrable v volume 0 (Real.pi / 2))
    (hδm : AEStronglyMeasurable δ (volume.restrict (Icc 0 η)))
    (hδ : ∀ᵐ t ∂volume.restrict (Icc 0 η), 0 ≤ δ t ∧ δ t ≤ 1)
    (hode : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hfirst : ∀ᵐ t ∂volume.restrict (Icc 0 α), u t = 0 ∧ v t = (1 - v t) * δ t)
    (hcharged : ∀ᵐ t ∂volume.restrict (Icc α (min β η)),
      u t = (1 - u t) + q t ∧ v t = (1 - v t) * δ t - p t)
    (hcore : ∀ᵐ t ∂volume.restrict (Icc (min β η) η),
      u t = q t ∧ v t = (1 - v t) * δ t - p t)
    (hlate : ∀ᵐ t ∂volume.restrict (Icc η (max β η)), u t = 1 / 2 ∧ v t = 0)
    (hfinal : ∀ᵐ t ∂volume.restrict (Icc (max β η) (Real.pi / 2)), u t = 0 ∧ v t = 0)
    (hpα : p α = 0) (hqη : q η = 0)
    (hunit : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)), 0 ≤ u t ∧ u t ≤ 1)
    (hcompanion : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)), v t ≤ 1)
    (hfloor : ∀ᵐ t ∂volume.restrict (Icc 0 γ), δ t = 0)
    (hqnonneg : ∀ᵐ t ∂volume.restrict (Icc 0 η), -1 ≤ q t)
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
  have h0η : 0 ≤ η := h0α.trans hαη
  have hγL : γ ≤ Real.pi / 2 := hγη.trans hηL
  have h0L : 0 ≤ Real.pi / 2 := hβ0.trans hβL
  have hsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
      uIcc a b ⊆ uIcc 0 (Real.pi / 2) := by
    simpa only [uIcc_of_le hab, uIcc_of_le h0L] using Icc_subset_Icc ha hb
  have hpβ := hp.mono (hsub β (Real.pi / 2) hβ0 hβL le_rfl)
  have hqβ := hq.mono (hsub β (Real.pi / 2) hβ0 hβL le_rfl)
  have huβ := hu.mono_set (hsub β (Real.pi / 2) hβ0 hβL le_rfl)
  have hvβ := hv.mono_set (hsub β (Real.pi / 2) hβ0 hβL le_rfl)
  have hpγ := hp.mono (hsub 0 γ le_rfl hγ0 hγL)
  have hqγ := hq.mono (hsub 0 γ le_rfl hγ0 hγL)
  have huγ := hu.mono_set (hsub 0 γ le_rfl hγ0 hγL)
  have hvγ := hv.mono_set (hsub 0 γ le_rfl hγ0 hγL)
  have hrB : IntervalIntegrable (fun t => 1 - u t) volume β (Real.pi / 2) :=
    (intervalIntegrable_const (c := (1 : ℝ))).sub huβ
  have hrB0 : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), 0 ≤ 1 - u t := by
    filter_upwards [ae_restrict_Icc_subinterval hβ0 le_rfl hunit] with t ht
    exact sub_nonneg.mpr ht.2
  have hrD0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ 1 - v t := by
    filter_upwards [ae_restrict_Icc_subinterval le_rfl hγL hcompanion] with t ht
    exact sub_nonneg.mpr ht
  have hG : IntervalIntegrable (fun t => firstUnitGainDensity (p t) (u t))
      volume β (Real.pi / 2) :=
    hrB.continuousOn_mul (continuousOn_const.sub hpβ.continuousOn)
  have hD := intervalIntegrable_firstUnitLossDensity h0η
    (hq.mono (hsub 0 η le_rfl h0η hηL))
    (hv.mono_set (hsub 0 η le_rfl h0η hηL)) hδm hδ
  have henergy := firstUnit_unit_companion_energy_balance
    h0α hαβ hαη hβL hηL hp hq hG hD hode hfirst hcharged hcore hlate hfinal hpα hqη
  have hpaid := firstUnit_loss_integral_lower_bound_of_companion_unit hγ0 hγη hD
    hfloor hqnonneg (ae_restrict_Icc_subinterval le_rfl hηL hcompanion)
    (hδ.mono (fun _ ht => ht.2))
  rw [hpL, hqL, hp0, hq0] at henergy
  have henergyPaid : firstUnitFinalEnergy (1 - 3 * C - T) (-eL) -
      firstUnitInitialEnergy (eR + h) (3 * C - 1) ≤
        (∫ t in β..(Real.pi / 2), firstUnitGainDensity (p t) (u t)) -
          (∫ t in 0..γ, (q t + 1) * (1 - v t)) + (0 : ℝ) := by
    linarith only [henergy, hpaid]
  have hIB := firstUnit_right_harmonic_moment hβL hpβ hqβ huβ hvβ
    (ae_restrict_Icc_subinterval hβ0 le_rfl hode) hpL hqL hT hz
  have hID := firstUnit_initial_harmonic_moment hγ0 hpγ hqγ huγ hvγ
    (ae_restrict_Icc_subinterval le_rfl hγL hode) hp0 hq0 hS hh
  have hbalance := firstUnit_balance_after_endpoint_substitution hR hL hIB hID henergyPaid
  have hvbound : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), v t ≤ 5 / 4 := by
    filter_upwards [ae_restrict_Icc_subinterval hβ0 le_rfl hcompanion] with t ht
    linarith only [ht]
  have hRB := firstUnitRightRemainder_le hβ0 hβL hβsin hrB hvβ hrB0 hvbound
  rw [hT] at hRB
  have hRD := firstUnitLeftRemainder_nonneg hγ0 hγL hrD0
    (ae_restrict_Icc_subinterval le_rfl hγL (hunit.mono (fun _ ht => ht.1)))
  have hmoment := firstUnit_right_window_moment_bounds hβ0 hβL hβsin hrB hrB0
  have hzT := hmoment.2.2
  rw [hz, hT] at hzT
  have hh0 : 0 ≤ h := by
    rw [← hh]
    apply intervalIntegral.integral_nonneg_of_ae_restrict hγ0
    filter_upwards [hrD0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    exact mul_nonneg hrt (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (by linarith only [ht.2, hγL, Real.pi_pos]))
  have hz0 : 0 ≤ z := by
    rw [← hz]
    apply intervalIntegral.integral_nonneg_of_ae_restrict hβL
    filter_upwards [hrB0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    exact mul_nonneg hrt (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith only [ht.1, hβ0, Real.pi_pos]) ht.2)
  exact firstUnit_terminal_contradiction hC hTpos hST hSone hTC hh0 hz0 hhz hzT hRB hRD
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 25 / 48) hTpos.le) hbalance

end AmbidextrousSofa.Analysis
