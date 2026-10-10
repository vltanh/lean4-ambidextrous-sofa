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

noncomputable section

open Set Filter MeasureTheory

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
  have hε : 0 ≤ ell / 2 + ell ^ 2 / 4 := by positivity
  have henergy' : clippedCornerEnergy p q a ≤
      1 / 4 + (2 + (ell / 2 + ell ^ 2 / 4)) ^ 2 := by
    convert henergy using 1 <;> ring
  have hfactor : 0 ≤ (ell + 1) / 2 := by positivity
  filter_upwards [ae_restrict_mem measurableSet_Ioo, D.source, D.shadow] with t ht hk hs
  by_cases hu : u t ≤ 1
  · rw [max_eq_right (sub_nonpos.mpr hu)]
    exact mul_nonneg hfactor (le_max_right _ _)
  · have hu1 : 1 < u t := lt_of_not_ge hu
    have hE : 17 / 4 < clippedCornerEnergy p q t := by
      apply lt_of_not_ge
      intro hE
      exact (not_lt_of_ge (curvature_le_one_of_clippedCornerEnergy
        (D.lower_arm t (Ioo_subset_Icc_self ht)) hk.1
        (fun hp hq => (hs hp hq).1) hE)) hu1
    have hqhigh := D.second_gt_one_on_prefix_of_energy_gt
      (Ioo_subset_Icc_self ht) hfirst hE
    have hpt : p t ≤ 0 := by
      by_contra hnot
      have hzero := (hs (lt_of_not_ge hnot)
        (by linarith only [hqhigh t ⟨ht.1.le, le_rfl⟩])).1
      linarith only [hzero, hu1]
    obtain ⟨A, hA, hpA, hbefore⟩ : ∃ A ∈ Icc a t, p A ≤ 0 ∧
        ∀ s ∈ Ico a A, 0 < p s := by
      by_cases hnonpos : p a ≤ 0
      · refine ⟨a, ⟨le_rfl, ht.1.le⟩, hnonpos, ?_⟩
        intro s hs
        exact False.elim ((not_lt_of_ge hs.1) hs.2)
      · have Dt := D.restrict le_rfl ht.1.le ht.2.le
        obtain ⟨A, hA, hpA, hbefore⟩ := exists_first_level_crossing ht.1 Dt.continuousOn.1
          (lt_of_not_ge hnonpos) hpt
        exact ⟨A, ⟨hA.1.le, hA.2⟩, hpA.le, hbefore⟩
    have hAT : A ≤ T := by
      by_contra hnot
      have hTA : T < A := lt_of_not_ge hnot
      have hpos := hbefore T ⟨hT, hTA⟩
      have hstartpos := hbefore a ⟨le_rfl, hT.trans_lt hTA⟩
      have DA := D.restrict le_rfl hA.1 (hA.2.trans ht.2.le)
      have hquad := DA.first_quadratic_before_crossing (hpa hstartpos) (hqa hstartpos)
        (fun s hs => hbefore s ⟨hs.1.le, hs.2⟩)
        (fun s hs => by
          have h := hqhigh s ⟨hs.1.le, hs.2.le.trans hA.2⟩
          linarith only [h])
        (show T ∈ Icc a A from ⟨hT, hTA.le⟩)
      linarith only [hquad, hpos, hcross]
    have hqA := D.second_bound_of_energy_at_nonpositive_first hε henergy'
      ⟨hA.1, hA.2.trans ht.2.le⟩ hpA
    have Dcore := D.restrict hA.1 hA.2 ht.2.le
    have hcore (s : ℝ) (hs : s ∈ Ioo A t) : 1 < q s :=
      hqhigh s ⟨hA.1.trans hs.1.le, hs.2.le⟩
    have hdec (s : ℝ) (hs : s ∈ Icc A t) (hs1 : s ≤ A + 1) :
        q s ≤ q A - (s - A) / 2 - (s - A) ^ 2 / 4 :=
      Dcore.second_quadratic_after_nonpositive_first hpA hcore hs hs1
    have hlength : t ≤ A + ell := by
      by_contra hnot
      have hgap : A + ell < min t (A + 1) :=
        lt_min (lt_of_not_ge hnot) (by linarith only [hell1])
      obtain ⟨s, hsl, hsr⟩ := exists_between hgap
      have hst := hsr.trans_le (min_le_left _ _)
      have hsone := hsr.trans_le (min_le_right _ _)
      have hAs : A < s := by linarith only [hsl, hell0]
      have hhigh := hcore s ⟨hAs, hst⟩
      have hbound := hdec s ⟨hAs.le, hst.le⟩ hsone.le
      have hprod := mul_pos (show 0 < (s - A) - ell by linarith only [hsl])
        (show 0 < (s - A) + ell + 2 by linarith only [hAs, hell0])
      nlinarith only [hhigh, hbound, hprod, hqA]
    have hbound := hdec t ⟨hA.2, le_rfl⟩
      (hlength.trans (by linarith only [hell1]))
    have husource := hk.1
    rw [sourceKappa_eq_self_of_one_le (hqhigh t ⟨ht.1.le, le_rfl⟩).le] at husource
    have hline : u t - 1 ≤ (ell + 1) / 2 * (A + ell - t) := by
      nlinarith only [husource, hbound, hqA, sq_nonneg (ell - (t - A))]
    rw [max_eq_left (sub_nonneg.mpr hu1.le)]
    exact hline.trans (mul_le_mul_of_nonneg_left
      ((show A + ell - t ≤ T + ell - t by linarith only [hAT]).trans
        (le_max_left _ _)) hfactor)

theorem ae_unit_after_quadratic_deadline
    (D : CornerArcDynamics p q u v a b) {d e T ell : ℝ}
    (hfirst : ∀ t ∈ Icc a b, p t ≤ 1)
    (hpa : 0 < p a → p a ≤ e - d * a + a ^ 2 / 2)
    (hqa : 0 < p a → d - 1 - a ≤ q a)
    (hT : a ≤ T) (hcross : e ≤ d * T - T ^ 2 / 2)
    (hell0 : 0 ≤ ell) (hell1 : ell < 1)
    (henergy : clippedCornerEnergy p q a ≤
      1 / 4 + (2 + ell / 2 + ell ^ 2 / 4) ^ 2) :
    ∀ᵐ t ∂volume.restrict (Ioo (T + ell) b), u t ≤ 1 := by
  have hsub : Ioo (T + ell) b ⊆ Ioo a b :=
    Ioo_subset_Ioo (by linarith only [hT, hell0]) le_rfl
  have h := ae_restrict_of_ae_restrict_of_subset hsub
    (D.ae_linear_excess_of_quadratic_deadline hfirst hpa hqa hT hcross hell0 hell1 henergy)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, h] with t ht hbound
  rw [max_eq_right (show T + ell - t ≤ 0 by linarith only [ht.1]), mul_zero] at hbound
  have hu := (le_max_left (u t - 1) 0).trans hbound
  linarith only [hu]

end CornerArcDynamics

end AmbidextrousSofa
