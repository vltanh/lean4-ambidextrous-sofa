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

The corner dynamics are stated on an arbitrary closed arc, whose initial
endpoint may be a post-impulse trace. The clipped energy prevents any later
excess after the second momentum has reached one. The horizontal corner
restricts to these dynamics on every closed arc inside the open quarter.
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
    ((show Continuous (fun t : ℝ => k * t + (c - k * a)) by fun_prop).intervalIntegrable _ _) (by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hx.2) hd]
        with t ht using ht.1.deriv.trans_le (ht.2.trans_eq (by ring)))
  rw [hax.integral_deriv_eq_sub, integral_affine] at hi
  linarith

/-- Corner dynamics on a closed arc `[a, b]`; the initial endpoint may be a post-impulse
trace. -/
structure CornerArcDynamics (p q u v : ℝ → ℝ) (a b : ℝ) : Prop where
  ordered : a ≤ b
  first_ac : AbsolutelyContinuousOnInterval p a b
  second_ac : AbsolutelyContinuousOnInterval q a b
  ode : ∀ᵐ t ∂volume.restrict (Ioo a b),
    HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t
  source : ∀ᵐ t ∂volume.restrict (Ioo a b),
    u t ≤ sourceKappa (q t) ∧ v t ≤ sourceKappa (p t)
  companion_nonneg : ∀ᵐ t ∂volume.restrict (Ioo a b), 0 ≤ v t
  lower_arm : ∀ t ∈ Icc a b, -1 ≤ q t
  first_arm_or_zero : ∀ᵐ t ∂volume.restrict (Ioo a b),
    p t ≤ 1 ∨ u t = 0 ∧ v t = 0
  shadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
    0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

theorem restrict (D : CornerArcDynamics p q u v a b)
    {c d : ℝ} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    CornerArcDynamics p q u v c d := by
  obtain ⟨hab, hp, hq, hode, hsrc, hv, hlow, harm, hsh⟩ := D
  have hI : uIcc c d ⊆ uIcc a b := by
    rw [uIcc_of_le hcd, uIcc_of_le hab]; exact Icc_subset_Icc hac hdb
  refine ⟨hcd, hp.mono hI, hq.mono hI, ?_, ?_, ?_,
    fun t ht => hlow t ⟨hac.trans ht.1, ht.2.trans hdb⟩, ?_, ?_⟩ <;>
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hac hdb) (by assumption)

theorem continuousOn (D : CornerArcDynamics p q u v a b) :
    ContinuousOn p (Icc a b) ∧ ContinuousOn q (Icc a b) :=
  uIcc_of_le D.ordered ▸ ⟨D.first_ac.continuousOn, D.second_ac.continuousOn⟩

theorem energy_le_max_initial (D : CornerArcDynamics p q u v a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) :=
  clippedCornerEnergy_le_max_of_zero_source_alternative D.first_ac D.second_ac D.ordered D.ode
    ((ae_restrict_mem measurableSet_Ioo).mono fun s hs => D.lower_arm s (Ioo_subset_Icc_self hs))
    (D.source.mono fun _ h => h.2) D.shadow D.first_arm_or_zero ht

theorem initial_energy_le_threshold (D : CornerArcDynamics p q u v a b)
    (hpa : p a ≤ 1) (hqa : q a ≤ 1) : clippedCornerEnergy p q a ≤ 17 / 4 := by
  have := D.lower_arm a ⟨le_rfl, D.ordered⟩
  unfold clippedCornerEnergy
  nlinarith [le_max_right (p a) 0, max_le hpa zero_le_one]

theorem ae_unit_of_initial_energy
    (D : CornerArcDynamics p q u v a b)
    (hstart : clippedCornerEnergy p q a ≤ 17 / 4) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, D.shadow] with t ht hk hs
  exact curvature_le_one_of_clippedCornerEnergy (D.lower_arm t (Ioo_subset_Icc_self ht)) hk.1
    (fun hp hq => (hs hp hq).1)
    ((D.energy_le_max_initial (Ioo_subset_Icc_self ht)).trans (max_le le_rfl hstart))

theorem ae_unit_of_second_le_one
    (D : CornerArcDynamics p q u v a b) (hpa : p a ≤ 1) (hqa : q a ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1 :=
  D.ae_unit_of_initial_energy (D.initial_energy_le_threshold hpa hqa)

/-- Any time with energy above the unit-curvature threshold has stayed
strictly above `q = 1` throughout its preceding closed interval. -/
theorem second_gt_one_on_prefix_of_energy_gt
    (D : CornerArcDynamics p q u v a b) {t : ℝ} (ht : t ∈ Icc a b)
    (hfirst : ∀ s ∈ Icc a b, p s ≤ 1)
    (henergy : 17 / 4 < clippedCornerEnergy p q t) :
    ∀ s ∈ Icc a t, 1 < q s := fun s hs => lt_of_not_ge fun hq =>
  have hD := D.restrict hs.1 hs.2 ht.2
  henergy.not_ge ((hD.energy_le_max_initial ⟨hs.2, le_rfl⟩).trans
    (max_le le_rfl (hD.initial_energy_le_threshold (hfirst s ⟨hs.1, hs.2.trans ht.2⟩) hq)))

theorem second_bound_of_energy_at_nonpositive_first
    (D : CornerArcDynamics p q u v a b) {ε t : ℝ}
    (hε : 0 ≤ ε)
    (hstart : clippedCornerEnergy p q a ≤ 1 / 4 + (2 + ε) ^ 2)
    (ht : t ∈ Icc a b) (hpt : p t ≤ 0) : q t ≤ 1 + ε := by
  have hE := (D.energy_le_max_initial ht).trans (max_le (by nlinarith) hstart)
  rw [clippedCornerEnergy, max_eq_right hpt] at hE
  nlinarith [D.lower_arm t ht]

theorem first_quadratic_before_crossing
    (D : CornerArcDynamics p q u v a b) {d e t : ℝ}
    (hpa : p a ≤ e - d * a + a ^ 2 / 2) (hqa : d - 1 - a ≤ q a)
    (hp : ∀ s ∈ Ioo a b, 0 < p s) (hq : ∀ s ∈ Ioo a b, 0 < q s)
    (ht : t ∈ Icc a b) : p t ≤ e - d * t + t ^ 2 / 2 := by
  -- Before `p` vanishes, `q` decreases at unit rate at most.
  have hlow (s : ℝ) (hs : s ∈ Icc a b) : d - 1 - s ≤ q s := by
    have := absolutelyContinuousOnInterval_linear_lower_bound (d := fun s => v s - 1 + p s)
      (k := -1) D.second_ac D.ordered (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.companion_nonneg]
          with s hs hd hv using ⟨hd.2, by linarith [hp s hs]⟩) hs
    linarith
  have := absolutelyContinuousOnInterval_quadratic_upper_bound (d := fun s => u s - 1 - q s)
    (c := -d + a) (k := 1) D.first_ac D.ordered (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.shadow] with s hs hd hsh
      exact ⟨hd.1, by linarith [(hsh (hp s hs) (hq s hs)).1, hlow s (Ioo_subset_Icc_self hs)]⟩) ht
  linarith

theorem first_quadratic_from_initial
    (D : CornerArcDynamics p q u v a b)
    (hp : ∀ s ∈ Ioo a b, 0 < p s) (hq : ∀ s ∈ Ioo a b, 0 < q s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    p t ≤ p a - (q a + 1) * (t - a) + (t - a) ^ 2 / 2 := by
  linarith [D.first_quadratic_before_crossing (d := q a + 1 + a)
    (e := p a + (q a + 1) * a + a ^ 2 / 2) (by linarith) (by linarith) hp hq ht]

theorem first_linear_decrease (D : CornerArcDynamics p q u v a b)
    (hq : ∀ s ∈ Ioo a b, 1 < q s) {t : ℝ} (ht : t ∈ Icc a b) :
    p t ≤ p a - (t - a) := by
  have := absolutelyContinuousOnInterval_quadratic_upper_bound (d := fun s => u s - 1 - q s)
    (c := -1) (k := 0) D.first_ac D.ordered (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source] with s hs hd hk
      exact ⟨hd.1, by linarith [sourceKappa_eq_self_of_one_le (hq s hs).le ▸ hk.1]⟩) ht
  linarith

/-- At a first downward crossing of `q = 1`, the first arm bound is
forced even when the preceding surrogate only had an arm-or-zero
alternative. If `p b > 1`, the first momentum was larger throughout
the prefix, and nonnegative second source makes `q` increase there. -/
theorem first_le_one_at_second_downcrossing
    (D : CornerArcDynamics p q u v a b) (hqa : 1 < q a) (hqb : q b = 1)
    (hq : ∀ s ∈ Ioo a b, 1 < q s) : p b ≤ 1 := by
  by_contra! hpb
  have := absolutelyContinuousOnInterval_linear_lower_bound (d := fun s => v s - 1 + p s)
    (k := p b - 1) D.second_ac D.ordered (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.companion_nonneg]
        with s hs hd hv
      refine ⟨hd.2, ?_⟩
      linarith [(D.restrict hs.1.le hs.2.le le_rfl).first_linear_decrease
        (fun t ht => hq t ⟨hs.1.trans ht.1, ht.2⟩) ⟨hs.2.le, le_rfl⟩, hs.2]) ⟨D.ordered, le_rfl⟩
  linarith [mul_nonneg (sub_nonneg.mpr hpb.le) (sub_nonneg.mpr D.ordered)]

/-- The initial first momentum may already be nonpositive when this
regular arc starts, as it can be immediately after a terminal impulse. -/
theorem second_quadratic_after_nonpositive_first
    (D : CornerArcDynamics p q u v a b) (hpa : p a ≤ 0)
    (hq : ∀ s ∈ Ioo a b, 1 < q s) {t : ℝ} (ht : t ∈ Icc a b)
    (ht1 : t ≤ a + 1) :
    q t ≤ q a - (t - a) / 2 - (t - a) ^ 2 / 4 := by
  have hD := D.restrict le_rfl ht.1 ht.2
  have := absolutelyContinuousOnInterval_quadratic_upper_bound (d := fun s => v s - 1 + p s)
    (c := -1 / 2) (k := -1 / 2) hD.second_ac ht.1 (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hD.ode, hD.source.mono fun _ h => h.2]
        with s hs hd hk
      have hps := D.first_linear_decrease hq ⟨hs.1.le, hs.2.le.trans ht.2⟩
      rw [sourceKappa, abs_of_nonpos (by linarith [hs.1])] at hk
      refine ⟨hd.2, ?_⟩
      linarith [hk.trans (max_le (by linarith [hs.2]) (by linarith) :
        max (-p s) ((-p s + 1) / 2) ≤ 1 / 2 - p s - (s - a) / 2)]) ⟨ht.1, le_rfl⟩
  linarith

end CornerArcDynamics

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

/-- On every closed arc inside the open quarter the dynamics are corner dynamics. -/
theorem arc (D : HorizontalCornerDynamics p q u v L) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbL : b < L) : CornerArcDynamics p q u v a b :=
  have hI : Ioo a b ⊆ Ioo (0 : ℝ) L := Ioo_subset_Ioo ha.le hbL.le
  ⟨hab, (D.ac ha hab hbL).1, (D.ac ha hab hbL).2, ae_restrict_of_ae_restrict_of_subset hI D.ode,
    ae_restrict_of_ae_restrict_of_subset hI D.source, .of_forall fun t => D.companion_nonneg t,
    fun t _ => (D.arms t).2, .of_forall fun t => .inl (D.arms t).1,
    ae_restrict_of_ae_restrict_of_subset hI D.shadow⟩

theorem ae_unit_after_first_eq_one (D : HorizontalCornerDynamics p q u v L)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) L) (hqb : q b = 1) :
    ∀ᵐ t ∂volume.restrict (Ioo b L), u t ≤ 1 := by
  refine ae_restrict_of_local_intervals isOpen_Ioo fun t ht => ?_
  obtain ⟨d, htd, hdL⟩ := exists_between ht.2
  exact ⟨b, d, ⟨ht.1, htd⟩, (D.arc hb.1 (ht.1.le.trans htd.le) hdL).ae_unit_of_second_le_one
    (D.arms b).1 hqb.le⟩

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
  exact (D.arc ha.1 ha.2.le ht.2).energy_le_max_initial ⟨ha.2.le, le_rfl⟩

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

theorem first_quadratic_before_crossing (D : HorizontalCornerDynamics p q u v L)
    {C e A t : ℝ}
    (hplim : Tendsto p (𝓝[>] (0 : ℝ)) (𝓝 e))
    (hqlim : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 (3 * C - 1)))
    (hAL : A < L) (hp : ∀ s ∈ Ioo (0 : ℝ) A, 0 < p s)
    (hq : ∀ s ∈ Ioo (0 : ℝ) A, 1 < q s)
    (ht : t ∈ Ioc (0 : ℝ) A) : p t ≤ e - 3 * C * t + t ^ 2 / 2 := by
  have ha : Tendsto (fun a : ℝ => t - a) (𝓝[>] (0 : ℝ)) (𝓝 (t - 0)) :=
    tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hlim := (hplim.sub ((hqlim.add_const 1).mul ha)).add ((ha.pow 2).div_const 2)
  refine ge_of_tendsto (by simpa using hlim) ?_
  filter_upwards [Ioo_mem_nhdsGT ht.1] with a ha
  exact (D.arc ha.1 ha.2.le (ht.2.trans_lt hAL)).first_quadratic_from_initial
    (fun s hs => hp s ⟨ha.1.trans hs.1, hs.2.trans_le ht.2⟩)
    (fun s hs => zero_lt_one.trans (hq s ⟨ha.1.trans hs.1, hs.2.trans_le ht.2⟩)) ⟨ha.2.le, le_rfl⟩

theorem first_linear_decrease (D : HorizontalCornerDynamics p q u v L)
    {A b t : ℝ} (hA : 0 < A) (hAb : A ≤ b) (hbL : b < L)
    (hq : ∀ s ∈ Ioo A b, 1 < q s)
    (ht : t ∈ Icc A b) : p t ≤ p A - (t - A) :=
  (D.arc hA hAb hbL).first_linear_decrease hq ht

theorem second_quadratic_after_crossing (D : HorizontalCornerDynamics p q u v L)
    {A b t : ℝ} (hA : 0 < A) (hAb : A ≤ b) (hbL : b < L)
    (hpA : p A = 0) (hq : ∀ s ∈ Ioo A b, 1 < q s)
    (ht : t ∈ Icc A b) (ht1 : t ≤ A + 1) :
    q t ≤ q A - (t - A) / 2 - (t - A) ^ 2 / 4 :=
  (D.arc hA hAb hbL).second_quadratic_after_nonpositive_first hpA.le hq ht ht1

end HorizontalCornerDynamics

end AmbidextrousSofa
