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

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

theorem first_linear_decrease_of_nonneg_second
    (D : CornerArcDynamics p q u v a b)
    (hq : ∀ t ∈ Ioo a b, 0 ≤ q t) {t : ℝ} (ht : t ∈ Icc a b) :
    p t ≤ p a - (t - a) / 2 := by
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a b),
      HasDerivAt p (u s - 1 - q s) s ∧
        u s - 1 - q s ≤ (-1 / 2 : ℝ) + 0 * (s - a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source] with s hs hd hk
    have hu := hk.1.trans (sourceKappa_le_self_add_half (hq s hs))
    exact ⟨hd.1, by linarith only [hu]⟩
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound
    D.first_ac D.ordered hd ht
  linarith only [h]

theorem second_linear_decrease_of_nonpos_first
    (D : CornerArcDynamics p q u v a b)
    (hp : ∀ t ∈ Ioo a b, p t ≤ 0) {t : ℝ} (ht : t ∈ Icc a b) :
    q t ≤ q a - (t - a) / 2 := by
  have hd : ∀ᵐ s ∂volume.restrict (Ioo a b),
      HasDerivAt q (v s - 1 + p s) s ∧
        v s - 1 + p s ≤ (-1 / 2 : ℝ) + 0 * (s - a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source] with s hs hd hk
    have hκ := sourceKappa_le_self_add_half (neg_nonneg.mpr (hp s hs))
    rw [sourceKappa_neg] at hκ
    have hv := hk.2.trans hκ
    exact ⟨hd.2, by linarith only [hv]⟩
  have h := absolutelyContinuousOnInterval_quadratic_upper_bound
    D.second_ac D.ordered hd ht
  linarith only [h]

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
  have hαL : α < L := lt_of_le_of_ne hα.2 (by
    intro heq
    rw [heq] at hpα
    linarith only [hpα, hpL])
  refine ⟨α, ⟨hα.1, hαL⟩, hpα, hpbefore, ?_⟩
  intro t ht
  by_contra hnot
  have hq0 : 0 < q 0 := hδ.trans_lt hqδ
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    have htq : q 0 ≤ 0 := by simpa only [← heq] using le_of_not_gt hnot
    exact (not_le_of_gt hq0) htq)
  have htL : t ≤ L := ht.2.trans hα.2
  obtain ⟨ξ, hξ, hqξ, hqbefore⟩ := exists_first_level_crossing ht0
    (D.continuousOn.2.mono (Icc_subset_Icc le_rfl htL)) hq0 (le_of_not_gt hnot)
  have hξα : ξ ≤ α := hξ.2.trans ht.2
  have hξL : ξ ≤ L := hξ.2.trans htL
  have Dξ := D.restrict le_rfl hξ.1.le hξL
  have hpξ : 0 ≤ p ξ := by
    rcases hξα.eq_or_lt with heq | hlt
    · simpa only [heq, hpα] using (le_rfl : (0 : ℝ) ≤ 0)
    · exact (hpbefore ξ ⟨hξ.1.le, hlt⟩).le
  have hpξbefore : ∀ s ∈ Ioo (0 : ℝ) ξ, 0 < p s :=
    fun s hs => hpbefore s ⟨hs.1.le, hs.2.trans_le hξα⟩
  by_cases hξδ : ξ ≤ δ
  · have hqd : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ξ),
        HasDerivAt q (v s - 1 + p s) s ∧ -1 ≤ v s - 1 + p s := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, Dξ.ode, Dξ.companion_nonneg]
        with s hs hd hv
      exact ⟨hd.2, by linarith only [hpξbefore s hs, hv]⟩
    have hlow := absolutelyContinuousOnInterval_linear_lower_bound Dξ.second_ac
      hξ.1.le hqd (right_mem_Icc.mpr hξ.1.le)
    rw [hqξ] at hlow
    linarith only [hlow, hξδ, hqδ]
  · let E : ℝ → ℝ := fun s => Analysis.momentumQuadraticEnergy 1 (-1) 0 (p s) (q s)
    have hE : AbsolutelyContinuousOnInterval E 0 ξ :=
      Analysis.absolutelyContinuousOnInterval_momentumQuadraticEnergy
        Dξ.first_ac Dξ.second_ac 1 (-1) 0
    have hEd : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) ξ),
        HasDerivAt E
          (2 * (p s - 1) * (u s - 1 - q s) +
            2 * (q s + 1) * (v s - 1 + p s)) s ∧
          0 ≤ 2 * (p s - 1) * (u s - 1 - q s) +
            2 * (q s + 1) * (v s - 1 + p s) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, Dξ.ode, Dξ.shadow,
        Dξ.companion_nonneg] with s hs hd hshadow hv
      have hqs := hqbefore s ⟨hs.1.le, hs.2⟩
      have hu := (hshadow (hpξbefore s hs) hqs).1
      refine ⟨?_, ?_⟩
      · exact (Analysis.hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1) 0).congr_deriv
          (by ring)
      · rw [hu]
        have hprod := mul_nonneg (show 0 ≤ 2 * (q s + 1) by linarith only [hqs]) hv
        nlinarith only [hprod]
    have hmon := absolutelyContinuousOnInterval_linear_lower_bound hE hξ.1.le hEd
      (right_mem_Icc.mpr hξ.1.le)
    have hpξone := hfirst ξ ⟨(lt_of_not_ge hξδ).le, hξL⟩
    have hprod := mul_nonneg hpξ (sub_nonneg.mpr hpξone)
    dsimp only [E, Analysis.momentumQuadraticEnergy] at hmon
    rw [hqξ] at hmon
    nlinarith only [hmon, henergy, hprod, hpξone, hpξ]

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
    by_contra hnot
    have hηt : η < t := lt_of_le_of_ne ht.1 (by
      intro heq
      have hp : 0 ≤ p η := by simpa only [← heq] using le_of_not_gt hnot
      exact (not_le_of_gt hpη) hp)
    have hcont : ContinuousOn (fun s => -p s) (Icc η t) :=
      (D.continuousOn.1.mono (Icc_subset_Icc hη.1.le ht.2)).neg
    obtain ⟨ξ, hξ, hpξneg, hpbefore⟩ := exists_first_level_crossing hηt hcont
      (neg_pos.mpr hpη) (neg_nonpos.mpr (le_of_not_gt hnot))
    have hpξ : p ξ = 0 := by linarith only [hpξneg]
    have hξL : ξ ≤ L := hξ.2.trans ht.2
    have Dξ := D.restrict hη.1.le hξ.1.le hξL
    have hpbefore : ∀ s ∈ Ioo η ξ, p s < 0 := by
      intro s hs
      have h := hpbefore s ⟨hs.1.le, hs.2⟩
      linarith only [h]
    have hqnegative : ∀ s ∈ Ioc η ξ, q s < 0 := by
      intro s hs
      have hbound := Dξ.second_linear_decrease_of_nonpos_first
        (fun r hr => (hpbefore r hr).le) ⟨hs.1.le, hs.2⟩
      rw [hqη] at hbound
      linarith only [hbound, hs.1]
    let E : ℝ → ℝ := fun s => Analysis.momentumQuadraticEnergy 1 (-1 / 2) 0 (p s) (q s)
    have hE : AbsolutelyContinuousOnInterval E η ξ :=
      Analysis.absolutelyContinuousOnInterval_momentumQuadraticEnergy
        Dξ.first_ac Dξ.second_ac 1 (-1 / 2) 0
    have hEd : ∀ᵐ s ∂volume.restrict (Ioo η ξ),
        HasDerivAt E
          (2 * (p s - 1) * (u s - 1 - q s) +
            2 * (q s + 1 / 2) * (v s - 1 + p s)) s ∧
          0 ≤ 2 * (p s - 1) * (u s - 1 - q s) +
            2 * (q s + 1 / 2) * (v s - 1 + p s) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, Dξ.ode,
        ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hη.1.le hξL) hshadow]
        with s hs hd hshadow
      obtain ⟨hv, hu⟩ := hshadow (hpbefore s hs) (hqnegative s ⟨hs.1, hs.2.le⟩)
      refine ⟨?_, ?_⟩
      · exact (Analysis.hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1 / 2) 0).congr_deriv
          (by ring)
      · rw [hv]
        have hprod := mul_nonneg
          (show 0 ≤ 2 * (1 - p s) by linarith only [hpbefore s hs])
          (sub_nonneg.mpr hu)
        nlinarith only [hprod]
    have hmon := absolutelyContinuousOnInterval_linear_lower_bound hE hξ.1.le hEd
      (right_mem_Icc.mpr hξ.1.le)
    have hqξlow := D.lower_arm ξ ⟨hη.1.le.trans hξ.1.le, hξL⟩
    have hqξneg := hqnegative ξ ⟨hξ.1, le_rfl⟩
    have hqprod := mul_nonneg (show 0 ≤ q ξ + 1 by linarith only [hqξlow])
      (neg_nonneg.mpr hqξneg.le)
    have hpprod := mul_pos (neg_pos.mpr hpη)
      (show 0 < 2 - p η by linarith only [hpη])
    dsimp only [E, Analysis.momentumQuadraticEnergy] at hmon
    rw [hpξ, hqη] at hmon
    nlinarith only [hmon, hqprod, hpprod]
  intro t ht
  have Dη := D.restrict hη.1.le hη.2.le le_rfl
  have hbound := Dη.second_linear_decrease_of_nonpos_first
    (fun s hs => (hpnegative s (Ioo_subset_Icc_self hs)).le) ⟨ht.1.le, ht.2⟩
  rw [hqη] at hbound
  exact ⟨hpnegative t ⟨ht.1.le, ht.2⟩, by linarith only [hbound, ht.1]⟩

end CornerArcDynamics

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
  by_contra hnot
  rcases (le_of_not_gt hnot).lt_or_eq with hlt | heq
  · have hpos := (hphase.initial_signs t ⟨ht.1, hlt⟩).1
    linarith only [hp, hpos]
  · rw [heq, hphase.first_zero] at hp
    exact lt_irrefl 0 hp

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ}

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
  have hηL : η < L := lt_of_le_of_ne hη.2 (by
    intro heq
    rw [heq] at hqη
    linarith only [hqη, hqL])
  have Dcore := D.restrict hα.1.le hη.1.le hη.2
  have hpcore : ∀ t ∈ Ioc α η, p t < 0 := by
    intro t ht
    have hbound := Dcore.first_linear_decrease_of_nonneg_second
      (fun s hs => (hqcore s ⟨hs.1.le, hs.2⟩).le) ⟨ht.1.le, ht.2⟩
    rw [hpα] at hbound
    linarith only [hbound, ht.1]
  have hpη := hpcore η ⟨hη.1, le_rfl⟩
  refine ⟨α, η, hα, ⟨hη.1, hηL⟩, hpα, hqη, ?_, ?_,
    D.final_negative_sector ⟨hα.1.trans hη.1, hηL⟩ hpη hqη hshadow, hqα, hpη⟩
  · intro t ht
    exact ⟨hpbefore t ht, hqbefore t ⟨ht.1, ht.2.le⟩⟩
  · intro t ht
    exact ⟨hpcore t ⟨ht.1, ht.2.le⟩, hqcore t ⟨ht.1.le, ht.2⟩⟩

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
  rcases harm with hpone | hzero
  · by_cases hplower : -1 ≤ p t
    · exact hk.2.trans (sourceKappa_le_one_of_bounds hplower hpone)
    · have hpbad : p t < -1 := lt_of_not_ge hplower
      have hqnonpos : q t ≤ 0 := le_of_not_gt (fun hq => hno t ht ⟨hpbad, hq⟩)
      rcases hqnonpos.lt_or_eq with hqneg | hqzero
      · rw [(hshadow (by linarith only [hpbad]) hqneg).1]
        norm_num
      · have hflat := hlevel hqzero
        rw [hd.2.deriv] at hflat
        have hκ := sourceKappa_le_self_add_half
          (show 0 ≤ -p t by linarith only [hpbad])
        rw [sourceKappa_neg] at hκ
        have hv := hk.2.trans hκ
        exfalso
        linarith only [hflat, hv]
  · rw [hzero.2]
    norm_num

/-- Either the companion density is unit bounded, or its first possible
excess is reached through the literal first level `p = -1` on the one
positive second-momentum interval. -/
theorem first_bad_crossing_or_unit {L α η : ℝ}
    (D : CornerArcDynamics p q u v 0 L) (hphase : StrictCornerSignPhases p q L α η)
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      p t < 0 → q t < 0 → v t = 0 ∧ u t ≤ 1 / 2) :
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L), v t ≤ 1) ∨
      ∃ τ ∈ Ioo α η, p τ = -1 ∧ 0 < q τ ∧
        (∀ t ∈ Ico α τ, -1 < p t) ∧
        (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) := by
  by_cases hbad : ∃ t ∈ Ioo (0 : ℝ) L, p t < -1 ∧ 0 < q t
  · obtain ⟨t, ht, hpbad, hqbad⟩ := hbad
    have hαt : α < t := by
      by_contra hnot
      rcases (le_of_not_gt hnot).lt_or_eq with hlt | heq
      · have hp := (hphase.initial_signs t ⟨ht.1.le, hlt⟩).1
        linarith only [hp, hpbad]
      · rw [heq, hphase.first_zero] at hpbad
        norm_num at hpbad
    have htη : t < η := by
      by_contra hnot
      rcases (le_of_not_gt hnot).lt_or_eq with hlt | heq
      · have hq := (hphase.final_signs t ⟨hlt, ht.2.le⟩).2
        linarith only [hq, hqbad]
      · rw [← heq, hphase.second_zero] at hqbad
        exact lt_irrefl 0 hqbad
    obtain ⟨τ, hτ, hpτ, hpfirst⟩ := exists_first_level_crossing hαt
      (D.continuousOn.1.mono (Icc_subset_Icc hphase.first_mem.1.le ht.2.le))
      (show -1 < p α by rw [hphase.first_zero]; norm_num) hpbad.le
    have hτη : τ < η := hτ.2.trans_lt htη
    have hτL : τ ≤ L := hτη.le.trans hphase.second_mem.2.le
    have h0τ : 0 < τ := hphase.first_mem.1.trans hτ.1
    have hno : ∀ s ∈ Ioo (0 : ℝ) τ, ¬ (p s < -1 ∧ 0 < q s) := by
      intro s hs hbad
      by_cases hαs : α ≤ s
      · have hp := hpfirst s ⟨hαs, hs.2⟩
        linarith only [hp, hbad.1]
      · have hp := (hphase.initial_signs s ⟨hs.1.le, lt_of_not_ge hαs⟩).1
        linarith only [hp, hbad.1]
    have hprefix := (D.restrict le_rfl h0τ.le hτL).ae_companion_le_one_of_no_bad
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hτL) hshadow) hno
    exact Or.inr ⟨τ, ⟨hτ.1, hτη⟩, hpτ,
      (hphase.core_signs τ ⟨hτ.1, hτη⟩).2, hpfirst, hprefix⟩
  · exact Or.inl (D.ae_companion_le_one_of_no_bad hshadow
      (fun t ht hbad' => hbad ⟨t, ht, hbad'⟩))

theorem first_bad_future_bounds {L α η τ : ℝ}
    (D : CornerArcDynamics p q u v 0 L) (hphase : StrictCornerSignPhases p q L α η)
    (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1) :
    ∀ t ∈ Icc τ η,
      p t ≤ -1 - (t - τ) / 2 ∧ q t ≤ q τ - (t - τ) / 2 := by
  have Dtail := D.restrict (hphase.first_mem.1.trans hτ.1).le hτ.2.le
    hphase.second_mem.2.le
  intro t ht
  have hp := Dtail.first_linear_decrease_of_nonneg_second
    (fun s hs => (hphase.core_signs s ⟨hτ.1.trans hs.1, hs.2⟩).2.le) ht
  have hq := Dtail.second_linear_decrease_of_nonpos_first
    (fun s hs => (hphase.core_signs s ⟨hτ.1.trans hs.1, hs.2⟩).1.le) ht
  rw [hpτ] at hp
  exact ⟨hp, hq⟩

end CornerArcDynamics

end AmbidextrousSofa
