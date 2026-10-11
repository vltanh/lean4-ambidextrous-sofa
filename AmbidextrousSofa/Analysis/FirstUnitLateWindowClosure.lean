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
  rcases le_or_gt β η with hβη | hηβ
  · apply firstUnit_momentum_energy_balance (χ := fun _ => 1)
      h0α hαβ hβη hηL hp hq hG hD hode hfirst
    · simpa only [min_eq_left hβη] using hcharged
    · simpa only [min_eq_left hβη, mul_one] using hcore
    · exact .of_forall fun _ => ⟨le_rfl, .inl rfl⟩
    · simpa only [max_eq_right hβη] using hfinal
    · exact hpα
    · exact hqη
  -- Otherwise the late window `[η, β]` joins the final sector with constant energy.
  have h0η := h0α.trans hαη
  have h0β := h0α.trans hαβ
  have hsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) : uIcc a b ⊆ uIcc 0 L :=
    uIcc_subset_uIcc (mem_uIcc_of_le ha (hab.trans hb)) (mem_uIcc_of_le (ha.trans hab) hb)
  have hD0α := hD.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le h0α hαη))
  have hDαη := hD.mono_set (uIcc_subset_uIcc_right (mem_uIcc_of_le h0α hαη))
  have h1 := firstUnit_initial_sector_energy h0α (hp.mono (hsub le_rfl h0α (hαη.trans hηL)))
    (hq.mono (hsub le_rfl h0α (hαη.trans hηL))) hD0α
    (ae_restrict_Icc_subinterval le_rfl (hαη.trans hηL) hode) hfirst
  have h2 := firstUnit_charged_core_energy hαη (hp.mono (hsub h0α hαη hηL))
    (hq.mono (hsub h0α hαη hηL)) hDαη (ae_restrict_Icc_subinterval h0α hηL hode)
    (by simpa only [min_eq_right hηβ.le] using hcharged)
  have hflat : firstUnitFinalEnergy (p β) (q β) = firstUnitFinalEnergy (p η) (q η) := by
    have h := integral_eq_sub_of_ac_of_ae_hasDerivAt (D := fun _ => 0) hηβ.le
      (absolutelyContinuousOnInterval_momentumQuadraticEnergy (hp.mono (hsub h0η hηβ.le hβL))
        (hq.mono (hsub h0η hηβ.le hβL)) 1 (-1 / 2) (3 / 4)) (by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
            (Ioo_subset_Icc_self.trans (Icc_subset_Icc h0η hβL)) hode,
          ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self
            (max_eq_left hηβ.le ▸ hlate)] with t hd hs
        apply (hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1 / 2) (3 / 4)).congr_deriv
        rw [hs.1, hs.2]
        ring)
    rw [intervalIntegral.integral_zero] at h
    exact sub_eq_zero.mp h.symm
  have h3 := firstUnit_final_sector_energy hβL (hp.mono (hsub h0β hβL le_rfl))
    (hq.mono (hsub h0β hβL le_rfl)) hG (ae_restrict_Icc_subinterval h0β le_rfl hode)
    (by simpa only [max_eq_left hηβ.le] using hfinal)
  rw [hpα, firstUnitInitialEnergy_eq_core_at_zero] at h1
  rw [hpα, hqη, firstUnitCoreEnergy_eq_final_at_zero] at h2
  rw [hqη] at hflat
  linarith only [h1, h2, hflat, h3, intervalIntegral.integral_add_adjacent_intervals hD0α hDαη]

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
  have hγL : γ ≤ Real.pi / 2 := hγη.trans hηL
  have hsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
      uIcc a b ⊆ uIcc 0 (Real.pi / 2) :=
    uIcc_subset_uIcc (mem_uIcc_of_le ha (hab.trans hb)) (mem_uIcc_of_le (ha.trans hab) hb)
  have hB := hsub hβ0 hβL le_rfl
  have hΓ := hsub le_rfl hγ0 hγL
  have hrB : IntervalIntegrable (fun t => 1 - u t) volume β (Real.pi / 2) :=
    intervalIntegrable_const.sub (hu.mono_set hB)
  have hrB0 : ∀ᵐ t ∂volume.restrict (Icc β (Real.pi / 2)), 0 ≤ 1 - u t :=
    (ae_restrict_Icc_subinterval hβ0 le_rfl hunit).mono fun _ ht => sub_nonneg.mpr ht.2
  have hrD0 : ∀ᵐ t ∂volume.restrict (Icc 0 γ), 0 ≤ 1 - v t :=
    (ae_restrict_Icc_subinterval le_rfl hγL hcompanion).mono fun _ ht => sub_nonneg.mpr ht
  have hD := intervalIntegrable_firstUnitLossDensity (h0α.trans hαη)
    (hq.mono (hsub le_rfl (h0α.trans hαη) hηL))
    (hv.mono_set (hsub le_rfl (h0α.trans hαη) hηL)) hδm hδ
  have henergy := firstUnit_unit_companion_energy_balance h0α hαβ hαη hβL hηL hp hq
    (hrB.continuousOn_mul (continuousOn_const.sub (hp.mono hB).continuousOn)) hD hode hfirst
    hcharged hcore hlate hfinal hpα hqη
  -- The loss over `[0, η]` pays at least its floor part over `[0, γ]`.
  have hpaid : (∫ t in 0..γ, (q t + 1) * (1 - v t)) ≤
      ∫ t in 0..η, firstUnitLossDensity (q t) (v t) (δ t) := by
    have hfloor_eq : (∫ t in 0..γ, firstUnitLossDensity (q t) (v t) (δ t)) =
        ∫ t in 0..γ, (q t + 1) * (1 - v t) :=
      intervalIntegral.integral_congr_ae_restrict ((ae_restrict_of_ae_restrict_of_subset
        (uIoc_subset_uIcc.trans (uIcc_of_le hγ0).subset) hfloor).mono fun t ht => by
          simp [firstUnitLossDensity, ht])
    refine hfloor_eq ▸ intervalIntegral.integral_mono_interval le_rfl hγ0 hγη ?_ hD
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (hqnonneg.and ((ae_restrict_Icc_subinterval le_rfl hηL hcompanion).and hδ))]
      with t ⟨hq, hv, hd⟩
    exact mul_nonneg (mul_nonneg (by linarith only [hq]) (sub_nonneg.mpr hv)) (sub_nonneg.mpr hd.2)
  rw [hpL, hqL, hp0, hq0] at henergy
  have hbalance := firstUnit_balance_after_endpoint_substitution (P := 0) hR hL
    (firstUnit_right_harmonic_moment hβL (hp.mono hB) (hq.mono hB) (hu.mono_set hB)
      (hv.mono_set hB) (ae_restrict_Icc_subinterval hβ0 le_rfl hode) hpL hqL hT hz)
    (firstUnit_initial_harmonic_moment hγ0 (hp.mono hΓ) (hq.mono hΓ) (hu.mono_set hΓ)
      (hv.mono_set hΓ) (ae_restrict_Icc_subinterval le_rfl hγL hode) hp0 hq0 hS hh)
    (by linarith only [henergy, hpaid])
  have hRB := firstUnitRightRemainder_le hβ0 hβL hβsin hrB (hv.mono_set hB) hrB0
    ((ae_restrict_Icc_subinterval hβ0 le_rfl hcompanion).mono fun _ ht => by linarith only [ht])
  have hzT := (firstUnit_right_window_moment_bounds hβ0 hβL hβsin hrB hrB0).2.2
  rw [hT] at hRB
  rw [hz, hT] at hzT
  have hh0 : 0 ≤ h := hh ▸ intervalIntegral.integral_nonneg_of_ae_restrict hγ0 (by
    filter_upwards [hrD0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    exact mul_nonneg hrt (Real.sin_nonneg_of_nonneg_of_le_pi ht.1
      (by linarith only [ht.2, hγL, Real.pi_pos])))
  have hz0 : 0 ≤ z := hz ▸ intervalIntegral.integral_nonneg_of_ae_restrict hβL (by
    filter_upwards [hrB0, ae_restrict_mem measurableSet_Icc] with t hrt ht
    exact mul_nonneg hrt (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith only [ht.1, hβ0, Real.pi_pos]) ht.2))
  exact firstUnit_terminal_contradiction hC hTpos hST hSone hTC hh0 hz0 hhz hzT hRB
    (firstUnitLeftRemainder_nonneg hγ0 hγL hrD0
      (ae_restrict_Icc_subinterval le_rfl hγL (hunit.mono fun _ ht => ht.1)))
    (by linarith only [hTpos]) hbalance

end AmbidextrousSofa.Analysis
