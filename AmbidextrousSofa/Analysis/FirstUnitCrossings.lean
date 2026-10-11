module

public import AmbidextrousSofa.Analysis.CornerArcCrossing
public import AmbidextrousSofa.Analysis.TiltedFirstUnitEnergy

@[expose] public section

/-!
# Ordered corner signs and the first possible companion excess

The initial positive sector cannot leave through the second momentum:
its quadratic radius increases, while the arm bound makes such an exit
have radius at most two. After the first momentum zero, the two strict
sign sectors follow from the source bounds and the negative-sector
quadratic barrier. The first possible companion excess is consequently
an actual first crossing of `p = -1` on this one positive-`q` interval.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

structure StrictCornerSignPhases (p q : ℝ → ℝ) (L α η : ℝ) : Prop where
  first_mem : α ∈ Ioo (0 : ℝ) L
  second_mem : η ∈ Ioo α L
  first_zero : p α = 0
  second_zero : q η = 0
  initial_signs : ∀ t ∈ Ico (0 : ℝ) α, 0 < p t ∧ 0 < q t
  core_signs : ∀ t ∈ Ioo α η, p t < 0 ∧ 0 < q t
  final_signs : ∀ t ∈ Ioc η L, p t < 0 ∧ q t < 0
  second_at_first : 0 < q α
  first_at_second : p η < 0

theorem StrictCornerSignPhases.first_lt_of_first_neg
    {p q : ℝ → ℝ} {L α η t : ℝ} (hphase : StrictCornerSignPhases p q L α η)
    (ht : t ∈ Icc (0 : ℝ) L) (hp : p t < 0) : α < t := by
  by_contra! hnot
  rcases hnot.lt_or_eq with hlt | rfl
  · linarith [(hphase.initial_signs t ⟨ht.1, hlt⟩).1]
  · linarith [hphase.first_zero]

theorem StrictCornerSignPhases.first_neg {p q : ℝ → ℝ} {L α η t : ℝ}
    (hphase : StrictCornerSignPhases p q L α η) (ht : t ∈ Ioc α L) : p t < 0 := by
  obtain hlt | rfl | hgt := lt_trichotomy t η
  exacts [(hphase.core_signs t ⟨ht.1, hlt⟩).1, hphase.first_at_second,
    (hphase.final_signs t ⟨hgt, ht.2⟩).1]

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

theorem first_linear_decrease_of_nonneg_second
    (D : CornerArcDynamics p q u v a b)
    (hq : ∀ t ∈ Ioo a b, 0 ≤ q t) {t : ℝ} (ht : t ∈ Icc a b) :
    p t ≤ p a - (t - a) / 2 := by
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound (c := -1 / 2) (k := 0)
    (d := fun s => u s - 1 - q s) D.first_ac D.ordered (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source] with s hs hd hk
      exact ⟨hd.1, by linarith [hk.1.trans (sourceKappa_le_self_add_half (hq s hs))]⟩) ht
  linarith

theorem second_linear_decrease_of_nonpos_first
    (D : CornerArcDynamics p q u v a b)
    (hp : ∀ t ∈ Ioo a b, p t ≤ 0) {t : ℝ} (ht : t ∈ Icc a b) :
    q t ≤ q a - (t - a) / 2 := by
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound (c := -1 / 2) (k := 0)
    (d := fun s => v s - 1 + p s) D.second_ac D.ordered (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source] with s hs hd hk
      have hκ := sourceKappa_le_self_add_half (neg_nonneg.mpr (hp s hs))
      rw [sourceKappa_neg] at hκ
      exact ⟨hd.2, by linarith [hk.2]⟩) ht
  linarith

/-- A short initial arm exception is harmless: before it ends, the
second momentum can fall at speed at most one while the first remains
positive. Afterwards the quadratic arm argument excludes its first
zero. -/
theorem initial_positive_first_crossing
    {L δ : ℝ} (D : CornerArcDynamics p q u v 0 L) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hqδ : δ < q 0)
    (hfirst : ∀ t ∈ Icc δ L, p t ≤ 1)
    (hp0 : 0 < p 0) (hpL : p L < 0)
    (henergy : 2 < (p 0 - 1) ^ 2 + (q 0 + 1) ^ 2) :
    ∃ α ∈ Ioo (0 : ℝ) L, p α = 0 ∧
      (∀ t ∈ Ico (0 : ℝ) α, 0 < p t) ∧
      (∀ t ∈ Icc (0 : ℝ) α, 0 < q t) := by
  obtain ⟨α, hα, hpα, hpbefore⟩ :=
    exists_first_level_crossing hL D.continuousOn.1 hp0 hpL.le
  refine ⟨α, ⟨hα.1, hα.2.lt_of_ne (by rintro rfl; linarith)⟩, hpα, hpbefore,
    fun t ht => ?_⟩
  by_contra! hnot
  have hq0 : 0 < q 0 := hδ.trans_lt hqδ
  have ht0 : 0 < t := ht.1.lt_of_ne (by rintro rfl; linarith)
  obtain ⟨ξ, hξ, hqξ, hqbefore⟩ := exists_first_level_crossing ht0
    (D.continuousOn.2.mono (Icc_subset_Icc le_rfl (ht.2.trans hα.2))) hq0 hnot
  have hξL : ξ ≤ L := hξ.2.trans (ht.2.trans hα.2)
  have Dξ := D.restrict le_rfl hξ.1.le hξL
  have hpξ : 0 ≤ p ξ := by
    rcases (hξ.2.trans ht.2).eq_or_lt with rfl | hlt
    exacts [hpα.ge, (hpbefore ξ ⟨hξ.1.le, hlt⟩).le]
  have hpξbefore (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ξ) : 0 < p s :=
    hpbefore s ⟨hs.1.le, hs.2.trans_le (hξ.2.trans ht.2)⟩
  rcases le_or_gt ξ δ with hξδ | hξδ
  · -- Before `δ` the second momentum falls at speed at most one.
    have hlow := absolutelyContinuousOnInterval_linear_lower_bound (k := -1)
      (d := fun s => v s - 1 + p s) Dξ.second_ac hξ.1.le (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, Dξ.ode, Dξ.companion_nonneg]
          with s hs hd hv
        exact ⟨hd.2, by linarith [hpξbefore s hs]⟩) (right_mem_Icc.mpr hξ.1.le)
    linarith
  -- Afterwards the quadratic radius about `(1, -1)` increases, but it is at most two at `ξ`.
  have hE := absolutelyContinuousOnInterval_linear_lower_bound (k := 0)
    (Analysis.absolutelyContinuousOnInterval_momentumQuadraticEnergy
      Dξ.first_ac Dξ.second_ac 1 (-1) 0) hξ.1.le (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, Dξ.ode, Dξ.shadow,
        Dξ.companion_nonneg] with s hs hd hshadow hv
      have hqs := hqbefore s ⟨hs.1.le, hs.2⟩
      refine ⟨Analysis.hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1) 0, ?_⟩
      rw [(hshadow (hpξbefore s hs) hqs).1]
      linarith [mul_nonneg (show 0 ≤ q s + 1 by linarith) hv])
    (right_mem_Icc.mpr hξ.1.le)
  simp only [Analysis.momentumQuadraticEnergy, hqξ] at hE
  linarith [mul_nonneg hpξ (sub_nonneg.mpr (hfirst ξ ⟨hξδ.le, hξL⟩))]

/-- The negative sector cannot return through `p = 0`: its shifted
quadratic energy increases, but the lower arm bounds the energy of
that proposed exit. This includes the terminal endpoint. -/
theorem final_negative_sector
    {L η : ℝ} (D : CornerArcDynamics p q u v 0 L) (hη : η ∈ Ioo (0 : ℝ) L)
    (hpη : p η < 0) (hqη : q η = 0)
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      p t < 0 → q t < 0 → v t = 0 ∧ u t ≤ 1 / 2) :
    ∀ t ∈ Ioc η L, p t < 0 ∧ q t < 0 := by
  have hpnegative : ∀ t ∈ Icc η L, p t < 0 := by
    intro t ht
    by_contra! hnot
    obtain ⟨ξ, hξ, hpξ, hpbefore⟩ := exists_first_level_crossing
      (ht.1.lt_of_ne (by rintro rfl; linarith))
      (D.continuousOn.1.mono (Icc_subset_Icc hη.1.le ht.2)).neg (neg_pos.mpr hpη)
      (neg_nonpos.mpr hnot)
    have hξL : ξ ≤ L := hξ.2.trans ht.2
    have Dξ := D.restrict hη.1.le hξ.1.le hξL
    have hpbefore (s : ℝ) (hs : s ∈ Ioo η ξ) : p s < 0 :=
      neg_pos.mp (hpbefore s ⟨hs.1.le, hs.2⟩)
    have hqnegative (s : ℝ) (hs : s ∈ Ioc η ξ) : q s < 0 := by
      linarith [hs.1, Dξ.second_linear_decrease_of_nonpos_first
        (fun r hr => (hpbefore r hr).le) ⟨hs.1.le, hs.2⟩]
    -- The quadratic radius about `(1, -1/2)` increases up to the proposed exit `ξ`.
    have hE := absolutelyContinuousOnInterval_linear_lower_bound (k := 0)
      (Analysis.absolutelyContinuousOnInterval_momentumQuadraticEnergy
        Dξ.first_ac Dξ.second_ac 1 (-1 / 2) 0) hξ.1.le (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, Dξ.ode,
          ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hη.1.le hξL) hshadow]
          with s hs hd hshadow
        obtain ⟨hv, hu⟩ := hshadow (hpbefore s hs) (hqnegative s ⟨hs.1, hs.2.le⟩)
        refine ⟨Analysis.hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1 / 2) 0, ?_⟩
        rw [hv]
        linarith [mul_nonneg (show 0 ≤ 1 - p s by linarith [hpbefore s hs])
          (sub_nonneg.mpr hu)])
      (right_mem_Icc.mpr hξ.1.le)
    simp only [Analysis.momentumQuadraticEnergy, hqη, neg_eq_zero.mp hpξ] at hE
    have hqξ := D.lower_arm ξ ⟨by linarith [hξ.1, hη.1], hξL⟩
    linarith [mul_nonneg (show 0 ≤ q ξ + 1 by linarith)
      (neg_nonneg.mpr (hqnegative ξ ⟨hξ.1, le_rfl⟩).le),
      mul_pos (neg_pos.mpr hpη) (show 0 < 2 - p η by linarith)]
  intro t ht
  have hbound := (D.restrict hη.1.le hη.2.le le_rfl).second_linear_decrease_of_nonpos_first
    (fun s hs => (hpnegative s (Ioo_subset_Icc_self hs)).le) ⟨ht.1.le, ht.2⟩
  exact ⟨hpnegative t ⟨ht.1.le, ht.2⟩, by linarith [ht.1]⟩

theorem exists_strict_sign_phases {L δ : ℝ}
    (D : CornerArcDynamics p q u v 0 L) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hqδ : δ < q 0)
    (hfirst : ∀ t ∈ Icc δ L, p t ≤ 1)
    (hp0 : 0 < p 0) (hpL : p L < 0) (hqL : q L < 0)
    (henergy : 2 < (p 0 - 1) ^ 2 + (q 0 + 1) ^ 2)
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      p t < 0 → q t < 0 → v t = 0 ∧ u t ≤ 1 / 2) :
    ∃ α η, StrictCornerSignPhases p q L α η := by
  obtain ⟨α, hα, hpα, hpbefore, hqbefore⟩ :=
    D.initial_positive_first_crossing hL hδ hqδ hfirst hp0 hpL henergy
  have hqα := hqbefore α ⟨hα.1.le, le_rfl⟩
  obtain ⟨η, hη, hqη, hqcore⟩ := exists_first_level_crossing hα.2
    (D.continuousOn.2.mono (Icc_subset_Icc hα.1.le le_rfl)) hqα hqL.le
  have hηL : η < L := hη.2.lt_of_ne (by rintro rfl; linarith)
  have hpcore (t : ℝ) (ht : t ∈ Ioc α η) : p t < 0 := by
    linarith [ht.1, (D.restrict hα.1.le hη.1.le hη.2).first_linear_decrease_of_nonneg_second
      (fun s hs => (hqcore s ⟨hs.1.le, hs.2⟩).le) ⟨ht.1.le, ht.2⟩]
  have hpη := hpcore η ⟨hη.1, le_rfl⟩
  exact ⟨α, η, hα, ⟨hη.1, hηL⟩, hpα, hqη,
    fun t ht => ⟨hpbefore t ht, hqbefore t ⟨ht.1, ht.2.le⟩⟩,
    fun t ht => ⟨hpcore t ⟨ht.1, ht.2.le⟩, hqcore t ⟨ht.1.le, ht.2⟩⟩,
    D.final_negative_sector ⟨hα.1.trans hη.1, hηL⟩ hpη hqη hshadow, hqα, hpη⟩

/-- The level `q = 0` carries no hidden excess. Its derivative vanishes
almost everywhere there, whereas a first momentum below `-1` would
force a strictly negative second derivative by the sharp arm law. -/
theorem ae_companion_le_one_of_no_bad {a b : ℝ}
    (D : CornerArcDynamics p q u v a b)
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      p t < 0 → q t < 0 → v t = 0 ∧ u t ≤ 1 / 2)
    (hno : ∀ t ∈ Ioo a b, ¬ (p t < -1 ∧ 0 < q t)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source,
    D.first_arm_or_zero, hshadow, ae_restrict_of_ae (ae_deriv_eq_zero_on_level q 0)]
    with t ht hd hk harm hshadow hlevel
  obtain hpone | ⟨-, hv⟩ := harm
  · rcases le_or_gt (-1) (p t) with hplower | hpbad
    · exact hk.2.trans (sourceKappa_le_one_of_bounds hplower hpone)
    rcases (not_lt.mp fun hq => hno t ht ⟨hpbad, hq⟩).lt_or_eq with hqneg | hqzero
    · linarith [(hshadow (by linarith) hqneg).1]
    have hκ := sourceKappa_le_self_add_half (neg_nonneg.mpr (by linarith : p t ≤ 0))
    rw [sourceKappa_neg] at hκ
    linarith [hd.2.deriv ▸ hlevel hqzero, hk.2]
  · linarith

/-- Either the companion density is unit bounded, or its first possible
excess is reached through the literal first level `p = -1` on the one
positive second-momentum interval. -/
theorem first_bad_crossing_or_unit {L α η : ℝ}
    (D : CornerArcDynamics p q u v 0 L) (hphase : StrictCornerSignPhases p q L α η)
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      p t < 0 → q t < 0 → v t = 0 ∧ u t ≤ 1 / 2) :
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L), v t ≤ 1) ∨
      ∃ τ ∈ Ioo α η, p τ = -1 ∧ (∀ t ∈ Ico α τ, -1 < p t) ∧
        (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) := by
  by_cases hbad : ∃ t ∈ Ioo (0 : ℝ) L, p t < -1 ∧ 0 < q t
  swap
  · exact .inl (D.ae_companion_le_one_of_no_bad hshadow fun t ht h => hbad ⟨t, ht, h⟩)
  obtain ⟨t, ht, hpbad, hqbad⟩ := hbad
  have hαt := hphase.first_lt_of_first_neg ⟨ht.1.le, ht.2.le⟩ (by linarith)
  have htη : t < η := by
    by_contra! h
    rcases h.eq_or_lt with rfl | h
    · linarith [hphase.second_zero]
    · linarith [(hphase.final_signs t ⟨h, ht.2.le⟩).2]
  obtain ⟨τ, hτ, hpτ, hpfirst⟩ := exists_first_level_crossing hαt
    (D.continuousOn.1.mono (Icc_subset_Icc hphase.first_mem.1.le ht.2.le))
    (by linarith [hphase.first_zero]) hpbad.le
  have hτη : τ < η := hτ.2.trans_lt htη
  have hτL : τ ≤ L := hτη.le.trans hphase.second_mem.2.le
  refine .inr ⟨τ, ⟨hτ.1, hτη⟩, hpτ, hpfirst,
    (D.restrict le_rfl (hphase.first_mem.1.trans hτ.1).le hτL).ae_companion_le_one_of_no_bad
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hτL) hshadow)
      fun s hs h => ?_⟩
  rcases lt_or_ge s α with hsα | hαs
  · linarith [(hphase.initial_signs s ⟨hs.1.le, hsα⟩).1]
  · linarith [hpfirst s ⟨hαs, hs.2⟩]

theorem first_bad_future_bounds {L α η τ : ℝ}
    (D : CornerArcDynamics p q u v 0 L) (hphase : StrictCornerSignPhases p q L α η)
    (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1) :
    ∀ t ∈ Icc τ η,
      p t ≤ -1 - (t - τ) / 2 ∧ q t ≤ q τ - (t - τ) / 2 := by
  intro t ht
  have Dtail := D.restrict (hphase.first_mem.1.trans hτ.1).le hτ.2.le hphase.second_mem.2.le
  have hsign (s : ℝ) (hs : s ∈ Ioo τ η) := hphase.core_signs s ⟨hτ.1.trans hs.1, hs.2⟩
  exact ⟨hpτ ▸ Dtail.first_linear_decrease_of_nonneg_second (fun s hs => (hsign s hs).2.le) ht,
    Dtail.second_linear_decrease_of_nonpos_first (fun s hs => (hsign s hs).1.le) ht⟩

end CornerArcDynamics

end AmbidextrousSofa
