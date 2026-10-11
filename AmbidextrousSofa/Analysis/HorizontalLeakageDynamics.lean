module

public import AmbidextrousSofa.Analysis.CornerEndpointEnergy
public import AmbidextrousSofa.Analysis.HorizontalLeakageIntegral
public import AmbidextrousSofa.Analysis.RampCutIntegral
public import Mathlib.Topology.Piecewise

@[expose] public section

/-!
# Initial crossing and quadratic decay for the horizontal corner

These are ordinary absolutely continuous ODE implications of the actual
source laws. The first crossing is constructed from a literal level set
and a one-sided endpoint limit. No curvature-phase decomposition is
assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem exists_first_level_crossing_of_right_limit
    {f : ℝ → ℝ} {L b c f0 : ℝ}
    (hf : ∀ t ∈ Ioo (0 : ℝ) L, ContinuousAt f t)
    (hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 f0))
    (hf0 : c < f0) (hb : b ∈ Ioo (0 : ℝ) L) (hfb : f b ≤ c) :
    ∃ t ∈ Ioc (0 : ℝ) b, f t = c ∧ ∀ s ∈ Ioo (0 : ℝ) t, c < f s := by
  have hpos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) b \ {0}) : 0 < t :=
    lt_of_le_of_ne ht.1.1 (Ne.symm ht.2)
  have hcont : ContinuousOn (Function.update f 0 f0) (Icc (0 : ℝ) b) :=
    continuousOn_update_iff.mpr
      ⟨fun t ht => (hf t ⟨hpos ht, ht.1.2.trans_lt hb.2⟩).continuousWithinAt,
        fun _ => hlim.mono_left (nhdsWithin_mono _ fun _ => hpos)⟩
  obtain ⟨t, ht, hft, hbefore⟩ := exists_first_level_crossing hb.1 hcont
    (by simpa using hf0) (by simpa [hb.1.ne'] using hfb)
  refine ⟨t, ht, by simpa [ht.1.ne'] using hft, fun s hs => ?_⟩
  simpa [hs.1.ne'] using hbefore s ⟨hs.1.le, hs.2⟩

theorem absolutelyContinuousOnInterval_quadratic_upper_bound
    {f d : ℝ → ℝ} {a b c k x : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hab : a ≤ b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt f (d t) t ∧ d t ≤ c + k * (t - a))
    (hx : x ∈ Icc a b) :
    f x ≤ f a + c * (x - a) + k * (x - a) ^ 2 / 2 := by
  have hax := hf.mono (uIcc_subset_uIcc_left (uIcc_of_le hab ▸ hx))
  have hi := intervalIntegral.integral_mono_ae_restrict hx.1 hax.intervalIntegrable_deriv
    ((show Continuous (fun t : ℝ => c + k * (t - a)) by fun_prop).intervalIntegrable _ _) (by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hx.2) hd]
        with t ht using ht.1.deriv.trans_le ht.2)
  rw [hax.integral_deriv_eq_sub, integral_affine_scalar] at hi
  linarith

/-- Local support calculus and source inequalities on one open quarter. -/
structure HorizontalCornerDynamics (p q u v : ℝ → ℝ) (L : ℝ) : Prop where
  continuous : ∀ t ∈ Ioo (0 : ℝ) L, ContinuousAt p t ∧ ContinuousAt q t
  ac : ∀ {a b : ℝ}, 0 < a → a ≤ b → b < L →
    AbsolutelyContinuousOnInterval p a b ∧ AbsolutelyContinuousOnInterval q a b
  ode : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
    HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t
  source : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
    u t ≤ sourceKappa (q t) ∧ v t ≤ sourceKappa (p t)
  companion_nonneg : ∀ t, 0 ≤ v t
  arms : ∀ t, p t ≤ 1 ∧ -1 ≤ q t
  shadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
    0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2

namespace HorizontalCornerDynamics

variable {p q u v : ℝ → ℝ} {L : ℝ}

theorem ae_unit_after_first_eq_one (D : HorizontalCornerDynamics p q u v L)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) L) (hqb : q b = 1) :
    ∀ᵐ t ∂volume.restrict (Ioo b L), u t ≤ 1 := by
  have hstart : clippedCornerEnergy p q b ≤ 17 / 4 := by
    rw [clippedCornerEnergy, hqb]
    nlinarith [le_max_right (p b) 0, max_le (D.arms b).1 zero_le_one]
  refine ae_restrict_of_local_intervals isOpen_Ioo fun t ht => ?_
  obtain ⟨d, htd, hdL⟩ := exists_between ht.2
  have hbd : b ≤ d := ht.1.le.trans htd.le
  have hI : Ioo b d ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo hb.1.le hdL.le
  have hac := D.ac hb.1 hbd hdL
  exact ⟨b, d, ⟨ht.1, htd⟩, ae_curvature_le_one_of_cornerEnergy hac.1 hac.2 hbd hstart
    (ae_restrict_of_ae_restrict_of_subset hI D.ode) (Eventually.of_forall D.arms)
    (ae_restrict_of_ae_restrict_of_subset hI D.source)
    (ae_restrict_of_ae_restrict_of_subset hI D.shadow)⟩

theorem energy_le_max_endpoint (D : HorizontalCornerDynamics p q u v L)
    {C e t : ℝ} (he : 0 ≤ e)
    (hplim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 e))
    (hqlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)))
    (ht : t ∈ Ioo (0 : ℝ) L) :
    clippedCornerEnergy p q t ≤ max (17 / 4) ((e - 1 / 2) ^ 2 + 9 * C ^ 2) := by
  have hE := (((hplim.max (tendsto_const_nhds (x := (0 : ℝ)))).sub_const (1 / 2)).pow 2).add
    ((hqlim.add_const 1).pow 2)
  rw [max_eq_left he, show (3 * C - 1 + 1) ^ 2 = 9 * C ^ 2 by ring] at hE
  refine ge_of_tendsto (tendsto_const_nhds.max hE) ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with a ha
  have hI : Ioo a t ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo ha.1.le ht.2.le
  have hac := D.ac ha.1 ha.2.le ht.2
  exact clippedCornerEnergy_le_max_initial hac.1 hac.2 ha.2.le
    (ae_restrict_of_ae_restrict_of_subset hI D.ode) (Eventually.of_forall D.arms)
    ((ae_restrict_of_ae_restrict_of_subset hI D.source).mono (fun _ h => h.2))
    (ae_restrict_of_ae_restrict_of_subset hI D.shadow) ⟨ha.2.le, le_rfl⟩

theorem crossing_first_bound (D : HorizontalCornerDynamics p q u v L)
    {C e ε A : ℝ} (he : 0 ≤ e) (hε : 0 ≤ ε)
    (hplim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 e))
    (hqlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)))
    (henergy : 9 * C ^ 2 - e * (1 - e) ≤ (2 + ε) ^ 2)
    (hA : A ∈ Ioo (0 : ℝ) L) (hpA : p A = 0) : q A ≤ 1 + ε := by
  have hE := (D.energy_le_max_endpoint he hplim hqlim hA).trans
    (max_le (c := 1 / 4 + (2 + ε) ^ 2) (by nlinarith) (by nlinarith))
  rw [clippedCornerEnergy, hpA, max_self] at hE
  have := (sq_le_sq₀ (by linarith [(D.arms A).2]) (by linarith)).mp
    (show (q A + 1) ^ 2 ≤ (2 + ε) ^ 2 by linarith)
  linarith

theorem second_lower_before_crossing (D : HorizontalCornerDynamics p q u v L)
    {C A t : ℝ}
    (hqlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)))
    (hAL : A < L) (hp : ∀ s ∈ Ioo (0 : ℝ) A, 0 < p s)
    (ht : t ∈ Ioc (0 : ℝ) A) : 3 * C - 1 - t ≤ q t := by
  have ha : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto (by simpa using hqlim.sub ((tendsto_const_nhds (x := t)).sub ha)) ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with a ha
  have h := absolutelyContinuousOnInterval_linear_lower_bound (d := fun s => v s - 1 + p s)
    (k := -1) (D.ac ha.1 ha.2.le (ht.2.trans_lt hAL)).2 ha.2.le ?_ ⟨ha.2.le, le_rfl⟩
  · linarith
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo ha.1.le (ht.2.trans hAL.le)) D.ode] with s hs hd
  have hps := hp s ⟨ha.1.trans hs.1, hs.2.trans_le ht.2⟩
  exact ⟨hd.2, by linarith [D.companion_nonneg s]⟩

theorem first_quadratic_before_crossing (D : HorizontalCornerDynamics p q u v L)
    {C e A t : ℝ}
    (hplim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 e))
    (hqlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)))
    (hAL : A < L) (hp : ∀ s ∈ Ioo (0 : ℝ) A, 0 < p s)
    (hq : ∀ s ∈ Ioo (0 : ℝ) A, 1 < q s)
    (ht : t ∈ Ioc (0 : ℝ) A) : p t ≤ e - 3 * C * t + t ^ 2 / 2 := by
  have ha : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim := (hplim.sub (((tendsto_const_nhds (x := t)).sub ha).const_mul (3 * C))).add
    (((tendsto_const_nhds (x := t ^ 2)).sub (ha.pow 2)).div_const 2)
  refine ge_of_tendsto (by simpa using hlim) ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with a ha
  have hI : Ioo a t ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo ha.1.le (ht.2.trans hAL.le)
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound (d := fun s => u s - 1 - q s)
    (c := -3 * C + a) (k := 1) (D.ac ha.1 ha.2.le (ht.2.trans_lt hAL)).1 ha.2.le ?_
    ⟨ha.2.le, le_rfl⟩
  · linarith
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset hI D.ode,
    ae_restrict_of_ae_restrict_of_subset hI D.shadow] with s hs hd hshadow
  have hsA : s ∈ Ioo (0 : ℝ) A := ⟨ha.1.trans hs.1, hs.2.trans_le ht.2⟩
  exact ⟨hd.1, by linarith [(hshadow (hp s hsA) (by linarith [hq s hsA])).1,
    D.second_lower_before_crossing hqlim hAL hp ⟨hsA.1, hsA.2.le⟩]⟩

theorem first_linear_decrease (D : HorizontalCornerDynamics p q u v L)
    {A b t : ℝ} (hA : 0 < A) (hAb : A ≤ b) (hbL : b < L)
    (hq : ∀ s ∈ Ioo A b, 1 < q s)
    (ht : t ∈ Icc A b) : p t ≤ p A - (t - A) := by
  have hI : Ioo A b ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo hA.le hbL.le
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound (d := fun s => u s - 1 - q s)
    (c := -1) (k := 0) (D.ac hA hAb hbL).1 hAb ?_ ht
  · linarith
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset hI D.ode,
    ae_restrict_of_ae_restrict_of_subset hI D.source] with s hs hd hk
  have hu := hk.1
  rw [sourceKappa_eq_self_of_one_le (hq s hs).le] at hu
  exact ⟨hd.1, by linarith⟩

theorem second_quadratic_after_crossing (D : HorizontalCornerDynamics p q u v L)
    {A b t : ℝ} (hA : 0 < A) (hAb : A ≤ b) (hbL : b < L)
    (hpA : p A = 0) (hq : ∀ s ∈ Ioo A b, 1 < q s)
    (ht : t ∈ Icc A b) (ht1 : t ≤ A + 1) :
    q t ≤ q A - (t - A) / 2 - (t - A) ^ 2 / 4 := by
  have hI : Ioo A t ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo hA.le (ht.2.trans hbL.le)
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound (d := fun s => v s - 1 + p s)
    (c := -1 / 2) (k := -1 / 2) (D.ac hA ht.1 (ht.2.trans_lt hbL)).2 ht.1 ?_ ⟨ht.1, le_rfl⟩
  · linarith
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset hI D.ode,
    ae_restrict_of_ae_restrict_of_subset hI D.source] with s hs hd hk
  have hps := D.first_linear_decrease hA hAb hbL hq ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hv := hk.2
  rw [sourceKappa, abs_of_nonpos (by linarith [hs.1])] at hv
  have hmax : max (-p s) ((-p s + 1) / 2) ≤ 1 - p s - (1 + (s - A)) / 2 := by
    apply max_le <;> linarith [hs.2]
  exact ⟨hd.2, by linarith⟩

end HorizontalCornerDynamics

end AmbidextrousSofa
