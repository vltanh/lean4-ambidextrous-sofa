module

public import AmbidextrousSofa.Analysis.FirstUnitCrossings

@[expose] public section

/-!
# The first companion excess follows the charged window

The two source lower bounds act on successive actual corner prefixes.
The charged prefix controls the quadratic energy by five. After the
window, a second decreasing quantity bounds the first excess-entry
height by one quarter. All estimates use ordinary absolutely continuous
momenta; the actual source occupation theorems supply the two lower
bounds in the geometric application.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ}

private theorem sourceKappa_of_neg_arm {p : ℝ} (h1 : -1 ≤ p) (h0 : p ≤ 0) :
    sourceKappa p = (1 - p) / 2 := by
  rw [sourceKappa, abs_of_nonpos h0, max_eq_right (by linarith only [h1])]; ring

theorem charged_prefix_energy_le_five {a b : ℝ}
    (D : CornerArcDynamics p q u v a b) (hab : a < b) (hpa : p a = 0)
    (hp : ∀ t ∈ Icc a b, -1 ≤ p t ∧ p t ≤ 0)
    (hq : ∀ t ∈ Icc a b, 0 ≤ q t)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1)
    (hlower : ∀ᵐ t ∂volume.restrict (Ioo a b), 1 + q t ≤ 2 * u t) :
    ∀ t ∈ Icc a b, (p t - 1) ^ 2 + (q t + 1) ^ 2 ≤ 5 := by
  have ha := left_mem_Icc.mpr hab.le
  have hqa := ContinuousOn.le_on_Icc_of_ae_le_on_Ioo (C := 1) D.continuousOn.2 hab (by
    filter_upwards [hunit, hlower] with t hu hl using by linarith only [hu, hl]) a ha
  have hEd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      deriv (fun s => Analysis.momentumQuadraticEnergy 1 (-1) 0 (p s) (q s)) t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source, hlower]
      with t ht hd hk hl
    obtain ⟨hp1, hp0⟩ := hp t (Ioo_subset_Icc_self ht)
    have hv := hk.2.trans_eq (sourceKappa_of_neg_arm hp1 hp0)
    rw [(Analysis.hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1) 0).deriv]
    nlinarith only [hp0, hl, hv, hq t (Ioo_subset_Icc_self ht)]
  intro t ht
  have hle := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
    (Analysis.absolutelyContinuousOnInterval_momentumQuadraticEnergy D.first_ac D.second_ac
      1 (-1) 0) hab.le hEd ht
  simp only [Analysis.momentumQuadraticEnergy, hpa] at hle
  nlinarith only [hle, hqa, hq a ha]

theorem uncharged_prefix_quantity_le_initial {a b : ℝ}
    (D : CornerArcDynamics p q u v a b)
    (hp : ∀ t ∈ Icc a b, -1 ≤ p t ∧ p t ≤ 0)
    (hlower : ∀ᵐ t ∂volume.restrict (Ioo a b), q t ≤ u t) :
    ∀ t ∈ Icc a b,
      q t + (p t - 1) ^ 2 / 4 ≤ q a + (p a - 1) ^ 2 / 4 := by
  let E : ℝ → ℝ := fun t => q t + (p t - 1) ^ 2 / 4
  have hp' := D.first_ac.sub (Analysis.absolutelyContinuousOnInterval_const_real 1 a b)
  have hE : AbsolutelyContinuousOnInterval E a b := by
    simpa only [E, pow_two, Pi.add_def, Pi.sub_def, Pi.mul_def, div_eq_mul_inv] using
      D.second_ac.add ((hp'.mul hp').mul
        (Analysis.absolutelyContinuousOnInterval_const_real ((4 : ℝ)⁻¹) a b))
  refine fun t ht => absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
    hE D.ordered ?_ ht
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source, hlower]
    with t ht hd hk hl
  obtain ⟨hp1, hp0⟩ := hp t (Ioo_subset_Icc_self ht)
  have hv := hk.2.trans_eq (sourceKappa_of_neg_arm hp1 hp0)
  rw [(show HasDerivAt E (v t - 1 + p t + (p t - 1) * (u t - 1 - q t) / 2) t from
    (hd.2.add (((hd.1.sub_const 1).pow 2).div_const 4)).congr_deriv (by ring)).deriv]
  nlinarith only [hp0, hl, hv]

/-- The entry `p = -1,q > 0` cannot occur in the charged window. The
two prefix estimates then give the exact `q ≤ 1/4` entry bound. -/
theorem first_bad_after_window_and_height_bound {L α β η τ : ℝ}
    (D : CornerArcDynamics p q u v 0 L)
    (hphase : StrictCornerSignPhases p q L α η)
    (hαβ : α < β) (hτ : τ ∈ Ioo α η) (hpτ : p τ = -1)
    (hpfirst : ∀ t ∈ Ico α τ, -1 < p t)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L), u t ≤ 1)
    (hcharged : ∀ᵐ t ∂volume.restrict (Ioo α τ), t < β → 1 + q t ≤ 2 * u t)
    (huncharged : ∀ᵐ t ∂volume.restrict (Ioo β τ), q t ≤ u t) :
    β < τ ∧ q τ ≤ 1 / 4 ∧
      (∀ t ∈ Icc α β, (p t - 1) ^ 2 + (q t + 1) ^ 2 ≤ 5) := by
  have h0α := hphase.first_mem.1.le
  have hτL := hτ.2.le.trans hphase.second_mem.2.le
  have hp (t : ℝ) (ht : t ∈ Icc α τ) : -1 ≤ p t ∧ p t ≤ 0 :=
    ⟨ht.2.eq_or_lt.elim (fun h => h ▸ hpτ.ge) fun h => (hpfirst t ⟨ht.1, h⟩).le,
      ht.1.eq_or_lt.elim (fun h => h ▸ hphase.first_zero.le)
        fun h => (hphase.core_signs t ⟨h, ht.2.trans_lt hτ.2⟩).1.le⟩
  have hq (t : ℝ) (ht : t ∈ Icc α τ) : 0 ≤ q t := ht.1.eq_or_lt.elim
    (fun h => h ▸ hphase.second_at_first.le)
    fun h => (hphase.core_signs t ⟨h, ht.2.trans_lt hτ.2⟩).2.le
  -- The charged energy bound holds up to the first of the window exit and the entry.
  have hmτ := min_le_right β τ
  have henergy := (D.restrict h0α (le_min hαβ.le hτ.1.le) (hmτ.trans hτL))
    |>.charged_prefix_energy_le_five (lt_min hαβ hτ.1) hphase.first_zero
      (fun t ht => hp t ⟨ht.1, ht.2.trans hmτ⟩) (fun t ht => hq t ⟨ht.1, ht.2.trans hmτ⟩)
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo h0α (hmτ.trans hτL)) hunit)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioo,
            ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hmτ) hcharged]
            with t ht hc using hc (ht.2.trans_le (min_le_left β τ)))
  have hβτ : β < τ := by
    by_contra hnot
    have h := henergy τ ⟨hτ.1.le, (min_eq_right (not_lt.mp hnot)).ge⟩
    rw [hpτ] at h
    nlinarith only [h, (hphase.core_signs τ hτ).2]
  rw [min_eq_left hβτ.le] at henergy
  have hquantity := (D.restrict (h0α.trans hαβ.le) hβτ.le hτL)
    |>.uncharged_prefix_quantity_le_initial (fun t ht => hp t ⟨hαβ.le.trans ht.1, ht.2⟩)
      huncharged τ (right_mem_Icc.mpr hβτ.le)
  rw [hpτ] at hquantity
  refine ⟨hβτ, ?_, henergy⟩
  nlinarith only [hquantity, henergy β (right_mem_Icc.mpr hαβ.le), sq_nonneg (q β - 1)]

end CornerArcDynamics

end AmbidextrousSofa
