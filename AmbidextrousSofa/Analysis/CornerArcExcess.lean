module

public import AmbidextrousSofa.Analysis.CornerArcCrossing

@[expose] public section

/-!
# Excess on a truncated arc after a possible initial impulse

No final crossing is required. At any point with source excess, the
clipped energy forces the entire preceding second momentum above one.
The first momentum has either already become nonpositive at the initial
trace or has a literal first zero. Its quadratic crossing bound and the
subsequent quadratic decay give a linear envelope with an explicit
deadline. This applies when the actual regular arc stops before a
downward second-momentum crossing.
-/

open Set MeasureTheory

namespace AmbidextrousSofa

namespace CornerArcDynamics

variable {p q u v : ℝ → ℝ} {a b : ℝ}

theorem ae_linear_excess_of_quadratic_deadline
    (D : CornerArcDynamics p q u v a b) {d e T ell : ℝ}
    (hfirst : ∀ t ∈ Icc a b, p t ≤ 1)
    (hpa : 0 < p a → p a ≤ e - d * a + a ^ 2 / 2)
    (hqa : 0 < p a → d - 1 - a ≤ q a)
    (hT : a ≤ T) (hcross : e ≤ d * T - T ^ 2 / 2)
    (hell0 : 0 ≤ ell) (hell1 : ell < 1)
    (henergy : clippedCornerEnergy p q a ≤
      1 / 4 + (2 + ell / 2 + ell ^ 2 / 4) ^ 2) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      max (u t - 1) 0 ≤ (ell + 1) / 2 * max (T + ell - t) 0 := by
  have hfactor : 0 ≤ (ell + 1) / 2 := by linarith only [hell0]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, D.shadow] with t ht hk hs
  refine max_le ?_ (mul_nonneg hfactor (le_max_right _ _))
  by_cases hu1 : u t ≤ 1
  · exact (sub_nonpos.mpr hu1).trans (mul_nonneg hfactor (le_max_right _ _))
  have hqhigh := D.second_gt_one_on_prefix_of_energy_gt (Ioo_subset_Icc_self ht) hfirst
    (lt_of_not_ge fun hE => hu1 (curvature_le_one_of_clippedCornerEnergy
      (D.lower_arm t (Ioo_subset_Icc_self ht)) hk.1 (fun hp hq => (hs hp hq).1) hE))
  have hpt : p t ≤ 0 := le_of_not_gt fun h =>
    hu1 ((hs h (by linarith only [hqhigh t ⟨ht.1.le, le_rfl⟩])).1.le.trans zero_le_one)
  obtain ⟨A, hA, hpA, hAT⟩ : ∃ A ∈ Icc a t, p A ≤ 0 ∧ A ≤ T := by
    rcases le_or_gt (p a) 0 with hpa0 | hpa0
    · exact ⟨a, ⟨le_rfl, ht.1.le⟩, hpa0, hT⟩
    obtain ⟨A, hA, hpA, hbefore⟩ := exists_first_level_crossing ht.1
      (D.restrict le_rfl ht.1.le ht.2.le).continuousOn.1 hpa0 hpt
    refine ⟨A, ⟨hA.1.le, hA.2⟩, hpA.le, le_of_not_gt fun hTA => ?_⟩
    have := (D.restrict le_rfl hA.1.le (hA.2.trans ht.2.le)).first_quadratic_before_crossing
      (hpa hpa0) (hqa hpa0) (fun s hs => hbefore s ⟨hs.1.le, hs.2⟩)
      (fun s hs => by linarith only [hqhigh s ⟨hs.1.le, hs.2.le.trans hA.2⟩]) ⟨hT, hTA.le⟩
    linarith only [this, hbefore T ⟨hT, hTA⟩, hcross]
  have hqA := D.second_bound_of_energy_at_nonpositive_first (ε := ell / 2 + ell ^ 2 / 4)
    (by positivity) (add_assoc (2 : ℝ) (ell / 2) (ell ^ 2 / 4) ▸ henergy)
    ⟨hA.1, hA.2.trans ht.2.le⟩ hpA
  have hdec (s : ℝ) (hs : s ∈ Icc A t) (hs1 : s ≤ A + 1) :=
    (D.restrict hA.1 hA.2 ht.2.le).second_quadratic_after_nonpositive_first hpA
      (fun r hr => hqhigh r ⟨hA.1.trans hr.1.le, hr.2.le⟩) hs hs1
  have hlength : t ≤ A + ell := by
    by_contra! h
    rcases le_or_gt t (A + 1) with h1 | h1
    · linarith only [hdec t ⟨hA.2, le_rfl⟩ h1, hqhigh t ⟨ht.1.le, le_rfl⟩, hqA,
        mul_pos (sub_pos.mpr h) (by linarith only [h, hell0] : 0 < t - A + ell + 2)]
    · linarith only [hdec (A + 1) ⟨by linarith only, h1.le⟩ le_rfl, hqA,
        hqhigh (A + 1) ⟨by linarith only [hA.1], h1.le⟩, mul_self_lt_mul_self hell0 hell1, hell1]
  rw [sourceKappa_eq_self_of_one_le (hqhigh t ⟨ht.1.le, le_rfl⟩).le] at hk
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (le_max_left _ _) hfactor)
  linarith only [hk.1, hdec t ⟨hA.2, le_rfl⟩ (by linarith only [hlength, hell1]), hqA,
    sq_nonneg (ell - (t - A)), mul_nonneg hfactor (sub_nonneg.mpr hAT)]

end CornerArcDynamics

end AmbidextrousSofa
