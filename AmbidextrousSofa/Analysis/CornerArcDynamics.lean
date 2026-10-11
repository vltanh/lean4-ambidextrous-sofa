module

public import AmbidextrousSofa.Analysis.HorizontalLeakageDynamics
public import AmbidextrousSofa.Analysis.TiltedInitialCircle

@[expose] public section

/-!
# Corner dynamics on an arbitrary closed regular arc

The initial endpoint may be a post-impulse trace. All subsequent
equations are ordinary absolutely continuous equations. The clipped
energy prevents any later excess after the second momentum has reached
one. This replaces a decomposition into positive components by a
pointwise statement about the entire prefix of any remaining excess.
-/

open Set MeasureTheory

namespace AmbidextrousSofa

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

end AmbidextrousSofa
