module

public import AmbidextrousSofa.Analysis.HorizontalLeakageDynamics
public import AmbidextrousSofa.Analysis.TiltedEnergyBarrier

@[expose] public section

/-!
# Corner dynamics on an arbitrary closed regular arc

The initial endpoint may be a post-impulse trace. All subsequent
equations are ordinary absolutely continuous equations. The clipped
energy prevents any later excess after the second momentum has reached
one. This replaces a decomposition into positive components by a
pointwise statement about the entire prefix of any remaining excess.
-/

noncomputable section

open Set Filter MeasureTheory

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
  have hsub : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac hdb
  have hsubcc : uIcc c d ⊆ uIcc a b := by
    rw [uIcc_of_le hcd, uIcc_of_le D.ordered]
    exact Icc_subset_Icc hac hdb
  exact ⟨hcd, D.first_ac.mono hsubcc, D.second_ac.mono hsubcc,
    ae_restrict_of_ae_restrict_of_subset hsub D.ode,
    ae_restrict_of_ae_restrict_of_subset hsub D.source,
    ae_restrict_of_ae_restrict_of_subset hsub D.companion_nonneg,
    fun t ht => D.lower_arm t ⟨hac.trans ht.1, ht.2.trans hdb⟩,
    ae_restrict_of_ae_restrict_of_subset hsub D.first_arm_or_zero,
    ae_restrict_of_ae_restrict_of_subset hsub D.shadow⟩

theorem continuousOn (D : CornerArcDynamics p q u v a b) :
    ContinuousOn p (Icc a b) ∧ ContinuousOn q (Icc a b) := by
  constructor
  · simpa only [uIcc_of_le D.ordered] using D.first_ac.continuousOn
  · simpa only [uIcc_of_le D.ordered] using D.second_ac.continuousOn

theorem energy_le_max_initial (D : CornerArcDynamics p q u v a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) := by
  apply clippedCornerEnergy_le_max_of_zero_source_alternative
    D.first_ac D.second_ac D.ordered D.ode
    _ (D.source.mono (fun _ h => h.2)) D.shadow D.first_arm_or_zero ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact D.lower_arm s (Ioo_subset_Icc_self hs)

theorem energy_le_threshold_of_second_le_one
    (D : CornerArcDynamics p q u v a b) (hpa : p a ≤ 1) (hqa : q a ≤ 1)
    {t : ℝ} (ht : t ∈ Icc a b) : clippedCornerEnergy p q t ≤ 17 / 4 := by
  have hb := D.lower_arm a ⟨le_rfl, D.ordered⟩
  have hp0 : 0 ≤ max (p a) 0 := le_max_right _ _
  have hp1 : max (p a) 0 ≤ 1 := max_le hpa (by norm_num)
  have hstart : clippedCornerEnergy p q a ≤ 17 / 4 := by
    unfold clippedCornerEnergy
    nlinarith only [hqa, mul_nonneg hp0 (sub_nonneg.mpr hp1),
      mul_nonneg (show 0 ≤ q a + 1 by linarith only [hb]) (sub_nonneg.mpr hqa)]
  exact (D.energy_le_max_initial ht).trans_eq (max_eq_left hstart)

theorem ae_unit_of_initial_energy
    (D : CornerArcDynamics p q u v a b)
    (hstart : clippedCornerEnergy p q a ≤ 17 / 4) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, D.shadow] with t ht hk hs
  have hE := D.energy_le_max_initial (Ioo_subset_Icc_self ht)
  rw [max_eq_left hstart] at hE
  exact curvature_le_one_of_clippedCornerEnergy
    (D.lower_arm t (Ioo_subset_Icc_self ht)) hk.1 (fun hp hq => (hs hp hq).1) hE

theorem ae_unit_of_second_le_one
    (D : CornerArcDynamics p q u v a b) (hpa : p a ≤ 1) (hqa : q a ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, D.shadow] with t ht hk hs
  exact curvature_le_one_of_clippedCornerEnergy
    (D.lower_arm t (Ioo_subset_Icc_self ht)) hk.1 (fun hp hq => (hs hp hq).1)
    (D.energy_le_threshold_of_second_le_one hpa hqa (Ioo_subset_Icc_self ht))

/-- Any time with energy above the unit-curvature threshold has stayed
strictly above `q = 1` throughout its preceding closed interval. -/
theorem second_gt_one_on_prefix_of_energy_gt
    (D : CornerArcDynamics p q u v a b) {t : ℝ} (ht : t ∈ Icc a b)
    (hfirst : ∀ s ∈ Icc a b, p s ≤ 1)
    (henergy : 17 / 4 < clippedCornerEnergy p q t) :
    ∀ s ∈ Icc a t, 1 < q s := by
  intro s hs
  by_contra hnot
  have hD := D.restrict hs.1 hs.2 ht.2
  have hE := hD.energy_le_threshold_of_second_le_one
    (hfirst s ⟨hs.1, hs.2.trans ht.2⟩) (le_of_not_gt hnot)
    (show t ∈ Icc s t from ⟨hs.2, le_rfl⟩)
  exact (not_lt_of_ge hE) henergy

theorem second_bound_of_energy_at_nonpositive_first
    (D : CornerArcDynamics p q u v a b) {ε t : ℝ}
    (hε : 0 ≤ ε)
    (hstart : clippedCornerEnergy p q a ≤ 1 / 4 + (2 + ε) ^ 2)
    (ht : t ∈ Icc a b) (hpt : p t ≤ 0) : q t ≤ 1 + ε := by
  have hE := D.energy_le_max_initial ht
  have hmax : max (17 / 4) (clippedCornerEnergy p q a) ≤ 1 / 4 + (2 + ε) ^ 2 :=
    max_le (by nlinarith only [hε, sq_nonneg ε]) hstart
  unfold clippedCornerEnergy at hE
  rw [max_eq_right hpt] at hE
  have hsquare : (q t + 1) ^ 2 ≤ (2 + ε) ^ 2 := by linarith only [hE, hmax]
  have hbound := (sq_le_sq₀
    (show 0 ≤ q t + 1 by linarith only [D.lower_arm t ht])
    (show 0 ≤ 2 + ε by linarith only [hε])).mp hsquare
  linarith only [hbound]

theorem second_lower_before_first_crossing
    (D : CornerArcDynamics p q u v a b) {d t : ℝ}
    (hqa : d - 1 - a ≤ q a) (hp : ∀ s ∈ Ioo a b, 0 < p s)
    (ht : t ∈ Icc a b) : d - 1 - t ≤ q t := by
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a b),
      HasDerivAt q (v s - 1 + p s) s ∧ -1 ≤ v s - 1 + p s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.companion_nonneg]
      with s hs hd hv
    exact ⟨hd.2, by linarith only [hp s hs, hv]⟩
  have h := absolutelyContinuousOnInterval_linear_lower_bound
    D.second_ac D.ordered hd ht
  linarith only [h, hqa]

theorem first_quadratic_before_crossing
    (D : CornerArcDynamics p q u v a b) {d e t : ℝ}
    (hpa : p a ≤ e - d * a + a ^ 2 / 2) (hqa : d - 1 - a ≤ q a)
    (hp : ∀ s ∈ Ioo a b, 0 < p s) (hq : ∀ s ∈ Ioo a b, 0 < q s)
    (ht : t ∈ Icc a b) : p t ≤ e - d * t + t ^ 2 / 2 := by
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a b),
      HasDerivAt p (u s - 1 - q s) s ∧
        u s - 1 - q s ≤ (-d + a) + (1 : ℝ) * (s - a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.shadow] with s hs hd hshadow
    have hu := (hshadow (hp s hs) (hq s hs)).1
    have hlow := D.second_lower_before_first_crossing hqa hp (Ioo_subset_Icc_self hs)
    refine ⟨hd.1, ?_⟩
    rw [hu]
    linarith only [hlow]
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound D.first_ac D.ordered hd ht
  nlinarith only [h, hpa]

theorem first_quadratic_from_initial
    (D : CornerArcDynamics p q u v a b)
    (hp : ∀ s ∈ Ioo a b, 0 < p s) (hq : ∀ s ∈ Ioo a b, 0 < q s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    p t ≤ p a - (q a + 1) * (t - a) + (t - a) ^ 2 / 2 := by
  have h := D.first_quadratic_before_crossing
    (d := q a + 1 + a) (e := p a + (q a + 1) * a + a ^ 2 / 2)
    (by nlinarith) (by linarith) hp hq ht
  nlinarith only [h]

theorem first_linear_decrease (D : CornerArcDynamics p q u v a b)
    (hq : ∀ s ∈ Ioo a b, 1 < q s) {t : ℝ} (ht : t ∈ Icc a b) :
    p t ≤ p a - (t - a) := by
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a b),
      HasDerivAt p (u s - 1 - q s) s ∧
        u s - 1 - q s ≤ (-1 : ℝ) + (0 : ℝ) * (s - a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source] with s hs hd hk
    have hu := hk.1
    rw [sourceKappa_eq_self_of_one_le (hq s hs).le] at hu
    exact ⟨hd.1, by linarith only [hu]⟩
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound D.first_ac D.ordered hd ht
  linarith only [h]

/-- At a first downward crossing of `q = 1`, the first arm bound is
forced even when the preceding surrogate only had an arm-or-zero
alternative. If `p b > 1`, the first momentum was larger throughout
the prefix, and nonnegative second source makes `q` increase there. -/
theorem first_le_one_at_second_downcrossing
    (D : CornerArcDynamics p q u v a b) (hqa : 1 < q a) (hqb : q b = 1)
    (hq : ∀ s ∈ Ioo a b, 1 < q s) : p b ≤ 1 := by
  by_contra hnot
  have hpb : 1 < p b := lt_of_not_ge hnot
  have hp (s : ℝ) (hs : s ∈ Ioo a b) : p b ≤ p s := by
    have hD := D.restrict hs.1.le hs.2.le le_rfl
    have h := hD.first_linear_decrease
      (fun t ht => hq t ⟨hs.1.trans ht.1, ht.2⟩)
      (show b ∈ Icc s b from ⟨hs.2.le, le_rfl⟩)
    linarith only [h, hs.2]
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a b),
      HasDerivAt q (v s - 1 + p s) s ∧ p b - 1 ≤ v s - 1 + p s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.companion_nonneg]
      with s hs hd hv
    exact ⟨hd.2, by linarith only [hp s hs, hv]⟩
  have h := absolutelyContinuousOnInterval_linear_lower_bound D.second_ac D.ordered hd
    (show b ∈ Icc a b from ⟨D.ordered, le_rfl⟩)
  rw [hqb] at h
  nlinarith only [h, hqa,
    mul_nonneg (show 0 ≤ p b - 1 by linarith only [hpb]) (sub_nonneg.mpr D.ordered)]

/-- The initial first momentum may already be nonpositive when this
regular arc starts, as it can be immediately after a terminal impulse. -/
theorem second_quadratic_after_nonpositive_first
    (D : CornerArcDynamics p q u v a b) (hpa : p a ≤ 0)
    (hq : ∀ s ∈ Ioo a b, 1 < q s) {t : ℝ} (ht : t ∈ Icc a b)
    (ht1 : t ≤ a + 1) :
    q t ≤ q a - (t - a) / 2 - (t - a) ^ 2 / 4 := by
  have hp (s : ℝ) (hs : s ∈ Icc a b) : p s ≤ -(s - a) := by
    have h := D.first_linear_decrease hq hs
    linarith only [h, hpa]
  have hD := D.restrict le_rfl ht.1 ht.2
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a t),
      HasDerivAt q (v s - 1 + p s) s ∧
        v s - 1 + p s ≤ (-1 / 2 : ℝ) + (-1 / 2 : ℝ) * (s - a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hD.ode, hD.source] with s hs hd hk
    have hps := hp s ⟨hs.1.le, hs.2.le.trans ht.2⟩
    have hp0 : p s ≤ 0 := by linarith only [hps, hs.1]
    have hv := hk.2
    rw [sourceKappa, abs_of_nonpos hp0] at hv
    have hmax : max (-p s) ((-p s + 1) / 2) ≤
        1 - p s - (1 + (s - a)) / 2 := by
      apply max_le <;> linarith only [hps, hs.2, ht1]
    exact ⟨hd.2, by linarith only [hv, hmax]⟩
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound
    hD.second_ac ht.1 hd (show t ∈ Icc a t from ⟨ht.1, le_rfl⟩)
  nlinarith only [h]

end CornerArcDynamics

end AmbidextrousSofa
