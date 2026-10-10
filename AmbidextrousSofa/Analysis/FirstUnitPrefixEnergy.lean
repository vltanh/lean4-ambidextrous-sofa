import AmbidextrousSofa.Analysis.FirstUnitCrossings

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

theorem charged_prefix_energy_le_five {a b : ℝ}
    (D : CornerArcDynamics p q u v a b) (hab : a < b) (hpa : p a = 0)
    (hp : ∀ t ∈ Icc a b, -1 ≤ p t ∧ p t ≤ 0)
    (hq : ∀ t ∈ Icc a b, 0 ≤ q t)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo a b), u t ≤ 1)
    (hlower : ∀ᵐ t ∂volume.restrict (Ioo a b), 1 + q t ≤ 2 * u t) :
    ∀ t ∈ Icc a b, (p t - 1) ^ 2 + (q t + 1) ^ 2 ≤ 5 := by
  have hqone : ∀ t ∈ Icc a b, q t ≤ 1 :=
    D.continuousOn.2.le_on_Icc_of_ae_le_on_Ioo hab (by
      filter_upwards [hunit, hlower] with t hu hl
      linarith only [hu, hl])
  let E : ℝ → ℝ := fun t => Analysis.momentumQuadraticEnergy 1 (-1) 0 (p t) (q t)
  have hE : AbsolutelyContinuousOnInterval E a b :=
    Analysis.absolutelyContinuousOnInterval_momentumQuadraticEnergy D.first_ac D.second_ac 1 (-1) 0
  have hEd : ∀ᵐ t ∂volume.restrict (Ioo a b), deriv E t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source, hlower]
      with t ht hd hk hl
    have hp' := hp t (Ioo_subset_Icc_self ht)
    have hq' := hq t (Ioo_subset_Icc_self ht)
    have hκ : sourceKappa (p t) = (1 - p t) / 2 := by
      rw [← sourceKappa_neg (p t), sourceKappa_eq_half_of_mem_Icc
        (show -p t ∈ Icc (0 : ℝ) 1 by constructor <;> linarith only [hp'.1, hp'.2])]
      ring
    have hv := hk.2
    rw [hκ] at hv
    have hdE := Analysis.hasDerivAt_momentumQuadraticEnergy hd.1 hd.2 1 (-1) 0
    change deriv (fun s => Analysis.momentumQuadraticEnergy 1 (-1) 0 (p s) (q s)) t ≤ 0
    rw [hdE.deriv]
    have hprodU := mul_nonneg (show 0 ≤ 1 - p t by linarith only [hp'.2])
      (show 0 ≤ 2 * u t - 1 - q t by linarith only [hl])
    have hprodV := mul_nonneg (show 0 ≤ q t + 1 by linarith only [hq'])
      (show 0 ≤ 1 - p t - 2 * v t by linarith only [hv])
    nlinarith only [hprodU, hprodV]
  have hqa0 := hq a (left_mem_Icc.mpr hab.le)
  have hqa1 := hqone a (left_mem_Icc.mpr hab.le)
  have hprod := mul_nonneg (sub_nonneg.mpr hqa1)
    (show 0 ≤ q a + 3 by linarith only [hqa0])
  intro t ht
  have hle := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos hE hab.le hEd ht
  dsimp only [E, Analysis.momentumQuadraticEnergy] at hle
  rw [hpa] at hle
  nlinarith only [hle, hprod]

theorem uncharged_prefix_quantity_le_initial {a b : ℝ}
    (D : CornerArcDynamics p q u v a b)
    (hp : ∀ t ∈ Icc a b, -1 ≤ p t ∧ p t ≤ 0)
    (hlower : ∀ᵐ t ∂volume.restrict (Ioo a b), q t ≤ u t) :
    ∀ t ∈ Icc a b,
      q t + (p t - 1) ^ 2 / 4 ≤ q a + (p a - 1) ^ 2 / 4 := by
  let E : ℝ → ℝ := fun t => q t + (p t - 1) ^ 2 / 4
  have hp' := D.first_ac.sub (absolutelyContinuousOnInterval_const_real 1 a b)
  have hE : AbsolutelyContinuousOnInterval E a b := by
    simpa only [E, pow_two, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, div_eq_mul_inv] using
      D.second_ac.add ((hp'.mul hp').mul
        (absolutelyContinuousOnInterval_const_real ((4 : ℝ)⁻¹) a b))
  have hEd : ∀ᵐ t ∂volume.restrict (Ioo a b), deriv E t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, D.ode, D.source, hlower]
      with t ht hd hk hl
    have hp' := hp t (Ioo_subset_Icc_self ht)
    have hκ : sourceKappa (p t) = (1 - p t) / 2 := by
      rw [← sourceKappa_neg (p t), sourceKappa_eq_half_of_mem_Icc
        (show -p t ∈ Icc (0 : ℝ) 1 by constructor <;> linarith only [hp'.1, hp'.2])]
      ring
    have hv := hk.2
    rw [hκ] at hv
    have hdE : HasDerivAt E
        (v t - 1 + p t + (p t - 1) * (u t - 1 - q t) / 2) t := by
      exact (hd.2.add (((hd.1.sub_const 1).pow 2).div_const 4)).congr_deriv (by ring)
    rw [hdE.deriv]
    have hprod := mul_nonneg (show 0 ≤ 1 - p t by linarith only [hp'.2])
      (sub_nonneg.mpr hl)
    nlinarith only [hprod, hv]
  exact fun t ht => absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
    hE D.ordered hEd ht

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
  have Dprefix := D.restrict h0α hτ.1.le hτL
  have hp : ∀ t ∈ Icc α τ, -1 ≤ p t ∧ p t ≤ 0 := by
    intro t ht
    constructor
    · rcases ht.2.eq_or_lt with heq | hlt
      · simpa only [heq, hpτ] using (le_rfl : (-1 : ℝ) ≤ -1)
      · exact (hpfirst t ⟨ht.1, hlt⟩).le
    · rcases ht.1.eq_or_lt with heq | hlt
      · simpa only [← heq, hphase.first_zero] using (le_rfl : (0 : ℝ) ≤ 0)
      · exact (hphase.core_signs t ⟨hlt, ht.2.trans_lt hτ.2⟩).1.le
  have hq : ∀ t ∈ Icc α τ, 0 ≤ q t := by
    intro t ht
    rcases ht.1.eq_or_lt with heq | hlt
    · simpa only [← heq] using hphase.second_at_first.le
    · exact (hphase.core_signs t ⟨hlt, ht.2.trans_lt hτ.2⟩).2.le
  have hqτ := (hphase.core_signs τ hτ).2
  have hunitPrefix := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo h0α hτL) hunit
  have hβτ : β < τ := by
    by_contra hnot
    have hτβ : τ ≤ β := le_of_not_gt hnot
    have hlower : ∀ᵐ t ∂volume.restrict (Ioo α τ), 1 + q t ≤ 2 * u t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hcharged] with t ht hc
      exact hc (ht.2.trans_le hτβ)
    have henergy := Dprefix.charged_prefix_energy_le_five hτ.1 hphase.first_zero hp hq
      hunitPrefix hlower τ (right_mem_Icc.mpr hτ.1.le)
    rw [hpτ] at henergy
    have hprod := mul_pos hqτ (show 0 < q τ + 2 by linarith only [hqτ])
    nlinarith only [henergy, hprod]
  have hβL := hβτ.le.trans hτL
  have Dcharged := D.restrict h0α hαβ.le hβL
  have hcharged' : ∀ᵐ t ∂volume.restrict (Ioo α β), 1 + q t ≤ 2 * u t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hβτ.le) hcharged]
      with t ht hc
    exact hc ht.2
  have henergy := Dcharged.charged_prefix_energy_le_five hαβ hphase.first_zero
    (fun t ht => hp t ⟨ht.1, ht.2.trans hβτ.le⟩)
    (fun t ht => hq t ⟨ht.1, ht.2.trans hβτ.le⟩)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo h0α hβL) hunit) hcharged'
  have Duncharged := D.restrict (h0α.trans hαβ.le) hβτ.le hτL
  have hquantity := Duncharged.uncharged_prefix_quantity_le_initial
    (fun t ht => hp t ⟨hαβ.le.trans ht.1, ht.2⟩) huncharged
    τ (right_mem_Icc.mpr hβτ.le)
  have hEβ := henergy β (right_mem_Icc.mpr hαβ.le)
  rw [hpτ] at hquantity
  refine ⟨hβτ, ?_, henergy⟩
  nlinarith only [hquantity, hEβ, sq_nonneg (q β - 1)]

end CornerArcDynamics

end AmbidextrousSofa
