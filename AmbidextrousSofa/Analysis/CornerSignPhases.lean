module

public import AmbidextrousSofa.Analysis.HorizontalNicheConfinement

@[expose] public section

/-!
# Ordered sign phases from actual reverse-corner exclusion

A first zero of the first velocity persists by the clipped
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
  have hsub {c : ℝ} (hc : 0 ≤ c) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hc le_rfl) (hode.and hunit)
  obtain ⟨b, hb, hpb, hpfirst⟩ := exists_first_level_crossing hL
    (by simpa only [uIcc_of_le hL.le] using hp.continuousOn) hp0 hpL.le
  have hbL : b < L := hb.2.lt_of_ne (by rintro rfl; linarith)
  have hpafter : ∀ t ∈ Icc b L, p t ≤ 0 := fun _ ht =>
    absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
      (hp.mono (uIcc_subset_uIcc_right (mem_uIcc_of_le hb.1.le hb.2))) hb.2 hpb.le (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, hsub hb.1.le] with t ht hd hpt
        rw [hd.1.1.deriv]
        linarith [hd.2.1, (hsep t ⟨hb.1.trans ht.1, ht.2⟩).resolve_right (lt_asymm hpt)]) ht
  have hqcont : ContinuousOn q (Icc 0 L) := by simpa only [uIcc_of_le hL.le] using hq.continuousOn
  obtain ⟨d, hd, hqd, hqfirst⟩ := exists_first_level_crossing hbL
    (hqcont.mono (Icc_subset_Icc hb.1.le le_rfl))
    ((hsep b ⟨hb.1, hbL⟩).resolve_right fun h => h.ne hpb) hqL.le
  have hdL : d < L := hd.2.lt_of_ne (by rintro rfl; linarith)
  have hd0 : 0 ≤ d := (hb.1.trans hd.1).le
  refine ⟨b, d, ⟨hb.1, hbL⟩, ⟨hd.1, hdL⟩, hpb, hqd, fun t ht => ?_, hpafter, fun t ht => ?_,
    fun t ht => ?_⟩
  · rcases ht.2.eq_or_lt with rfl | hlt
    exacts [hpb.ge, (hpfirst t ⟨ht.1, hlt⟩).le]
  · rcases lt_or_ge t b with htb | hbt
    · rcases ht.1.eq_or_lt with rfl | htpos
      · exact hq0.le
      exact ((hsep t ⟨htpos, ht.2.trans_lt hdL⟩).resolve_right
        (lt_asymm (hpfirst t ⟨ht.1, htb⟩))).le
    · rcases ht.2.eq_or_lt with rfl | hlt
      exacts [hqd.ge, (hqfirst t ⟨hbt, hlt⟩).le]
  · refine (absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos
      (hq.mono (uIcc_subset_uIcc_right (mem_uIcc_of_le hd0 hd.2))) hd.2 ?_ ht).trans_eq hqd
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hsub hd0] with t ht hdt
    rw [hdt.1.2.deriv]
    linarith [hdt.2.2, hpafter t ⟨hd.1.le.trans ht.1.le, ht.2.le⟩]

end AmbidextrousSofa
