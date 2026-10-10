import AmbidextrousSofa.Analysis.HorizontalNicheConfinement

/-!
# Ordered sign phases from actual reverse-corner exclusion

A first zero of the first manuscript velocity persists by the clipped
absolutely continuous barrier. The other velocity then decreases until
its first zero and remains nonpositive. The separation hypothesis is
an ordinary pointwise sign condition supplied for horizontal maxima
by their strict tangency gap; no contact chart is assumed.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem exists_ordered_corner_sign_switches
    {p q u v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hp : AbsolutelyContinuousOnInterval p 0 L)
    (hq : AbsolutelyContinuousOnInterval q 0 L)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) L), u t ≤ 1 ∧ v t ≤ 1)
    (hp0 : 0 < p 0) (hpL : p L < 0) (hq0 : 0 < q 0) (hqL : q L < 0)
    (hsep : ∀ t ∈ Ioo (0 : ℝ) L, 0 < q t ∨ p t < 0) :
    ∃ b d : ℝ, b ∈ Ioo (0 : ℝ) L ∧ d ∈ Ioo b L ∧ p b = 0 ∧ q d = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) b, 0 ≤ p t) ∧
      (∀ t ∈ Icc b L, p t ≤ 0) ∧
      (∀ t ∈ Icc (0 : ℝ) d, 0 ≤ q t) ∧
      (∀ t ∈ Icc d L, q t ≤ 0) := by
  have hpcont : ContinuousOn p (Icc (0 : ℝ) L) := by
    simpa only [uIcc_of_le hL.le] using hp.continuousOn
  have hqcont : ContinuousOn q (Icc (0 : ℝ) L) := by
    simpa only [uIcc_of_le hL.le] using hq.continuousOn
  obtain ⟨b, hb, hpb, hpfirst⟩ := exists_first_level_crossing hL hpcont hp0 hpL.le
  have hbL : b < L := lt_of_le_of_ne hb.2 (by
    intro heq
    rw [heq] at hpb
    linarith)
  have hqb : 0 < q b := by
    rcases hsep b ⟨hb.1, hbL⟩ with hqpos | hpneg
    · exact hqpos
    · rw [hpb] at hpneg
      exact (lt_irrefl _ hpneg).elim
  have hpBL : AbsolutelyContinuousOnInterval p b L := hp.mono (by
    rw [uIcc_of_le hL.le, uIcc_of_le hb.2]
    exact Icc_subset_Icc hb.1.le le_rfl)
  have hpderiv : ∀ᵐ t ∂volume.restrict (Ioo b L), 0 < p t → deriv p t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hb.1.le le_rfl) hode,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hb.1.le le_rfl) hunit]
      with t ht hd hu
    intro hpt
    have hqt : 0 < q t := by
      rcases hsep t ⟨hb.1.trans ht.1, ht.2⟩ with hqpos | hpneg
      · exact hqpos
      · linarith
    rw [hd.1.deriv]
    linarith [hu.1]
  have hpafter : ∀ t ∈ Icc b L, p t ≤ 0 :=
    fun _ ht => absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above hpBL hb.2
      (by rw [hpb]) hpderiv ht
  obtain ⟨d, hd, hqd, hqfirst⟩ := exists_first_level_crossing hbL
    (hqcont.mono (Icc_subset_Icc hb.1.le le_rfl)) hqb hqL.le
  have hdL : d < L := lt_of_le_of_ne hd.2 (by
    intro heq
    rw [heq] at hqd
    linarith)
  have hd0 : 0 < d := hb.1.trans hd.1
  have hqDL : AbsolutelyContinuousOnInterval q d L := hq.mono (by
    rw [uIcc_of_le hL.le, uIcc_of_le hd.2]
    exact Icc_subset_Icc hd0.le le_rfl)
  have hqderiv : ∀ᵐ t ∂volume.restrict (Ioo d L), deriv q t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hd0.le le_rfl) hode,
      ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hd0.le le_rfl) hunit]
      with t ht hdt hu
    have hpt := hpafter t ⟨hd.1.le.trans ht.1.le, ht.2.le⟩
    rw [hdt.2.deriv]
    linarith [hu.2]
  have hqafter : ∀ t ∈ Icc d L, q t ≤ 0 := by
    intro t ht
    have hle := absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos hqDL hd.2
      hqderiv ht
    simpa only [hqd] using hle
  refine ⟨b, d, ⟨hb.1, hbL⟩, ⟨hd.1, hdL⟩, hpb, hqd, ?_, hpafter, ?_, hqafter⟩
  · intro t ht
    rcases ht.2.eq_or_lt with heq | hlt
    · simpa only [heq, hpb] using (le_rfl : (0 : ℝ) ≤ 0)
    · exact (hpfirst t ⟨ht.1, hlt⟩).le
  · intro t ht
    by_cases hbt : b ≤ t
    · rcases ht.2.eq_or_lt with heq | hlt
      · simpa only [heq, hqd] using (le_rfl : (0 : ℝ) ≤ 0)
      · exact (hqfirst t ⟨hbt, hlt⟩).le
    · have htb : t < b := lt_of_not_ge hbt
      by_cases htzero : t = 0
      · simpa only [htzero] using hq0.le
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
        have hpt := hpfirst t ⟨ht.1, htb⟩
        rcases hsep t ⟨htpos, ht.2.trans_lt hdL⟩ with hqt | hpneg
        · exact hqt.le
        · linarith

end AmbidextrousSofa
