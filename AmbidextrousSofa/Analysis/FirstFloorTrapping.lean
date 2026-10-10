import AmbidextrousSofa.Analysis.FirstUnitCrossings
import AmbidextrousSofa.Measure.SupportAreaAC

/-!
# The visible bad-entry core cannot remain below the floor

Full corner occupation makes the first momentum decrease at unit speed.
Once that momentum reaches minus one, the companion density is strictly
above one and the companion tangent moves strictly down. The first-zero
argument below includes an initial zero: a genuine neighborhood of full
visibility first moves the tangent strictly below the floor, after which
the initial-floor visibility principle prevents any return.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa.Analysis

/-- The two literal source equalities at a fully occupied core point.
The tangent coefficient is nonnegative and vanishes on excess. -/
def firstFloorVisibleLaw (p q u v δ : ℝ → ℝ) (t : ℝ) : Prop :=
  u t = q t ∧ v t = (1 - v t) * δ t - p t ∧
    0 ≤ δ t ∧ (1 < v t → δ t = 0)

theorem firstFloor_visible_core_decay
    {p q u v δ y : ℝ → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ Real.pi)
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hy : AbsolutelyContinuousOnInterval y a b) (hpa : p a ≤ -1)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧
        HasDerivAt y ((1 - v t) * Real.sin t) t)
    (hsource : ∀ᵐ t ∂volume.restrict (Ioo a b), firstFloorVisibleLaw p q u v δ t) :
    (∀ t ∈ Icc a b, p t = p a - (t - a)) ∧
      (∀ t ∈ Icc a b, y t ≤ y a) ∧ y b < y a := by
  have hpD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt p (-1) t := by
    filter_upwards [hode, hsource] with t hd hs
    exact hd.1.congr_deriv (by rw [hs.1]; ring)
  have hpExact : ∀ t ∈ Icc a b, p t = p a - (t - a) := by
    intro t ht
    have hac : AbsolutelyContinuousOnInterval p a t := hp.mono (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2)
    have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt ht.1 hac
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2) hpD)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    linarith only [hi]
  let F : ℝ → ℝ := fun t => (t - a - 1 - p a) * Real.sin t
  have hF : Continuous F := by dsimp only [F]; fun_prop
  have hyD : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt y (-F t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hsource] with t ht hd hs
    have hpt := hpExact t (Ioo_subset_Icc_self ht)
    have hpneg : p t < -1 := by linarith only [hpt, hpa, ht.1]
    have hv : 1 < v t := by
      by_contra hnot
      have hprod := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) hs.2.2.1
      linarith only [hs.2.1, hpneg, hprod, le_of_not_gt hnot]
    have hδ := hs.2.2.2 hv
    have hvp : v t = -p t := by simpa only [hδ, mul_zero, zero_sub] using hs.2.1
    exact hd.2.congr_deriv (by rw [hvp, hpt]; dsimp only [F]; ring)
  have hyExact : ∀ t ∈ Icc a b, y t - y a = -(∫ s in a..t, F s) := by
    intro t ht
    have hac : AbsolutelyContinuousOnInterval y a t := hy.mono (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2)
    have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt ht.1 hac
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2) hyD)
    simpa only [intervalIntegral.integral_neg] using hi.symm
  have hdecay : ∀ t ∈ Ioc a b, y t < y a := by
    intro t ht
    have hpos : 0 < ∫ s in a..t, F s := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on (hF.intervalIntegrable _ _) _ ht.1
      intro s hs
      exact mul_pos (by linarith only [hs.1, hpa])
        (Real.sin_pos_of_pos_of_lt_pi (ha.trans_lt hs.1) (hs.2.trans_le (ht.2.trans hb)))
    have hi := hyExact t ⟨ht.1.le, ht.2⟩
    linarith only [hi, hpos]
  refine ⟨hpExact, ?_, hdecay b ⟨hab, le_rfl⟩⟩
  intro t ht
  rcases ht.1.eq_or_lt with heq | hlt
  · simpa only [← heq] using (le_rfl : y a ≤ y a)
  · exact (hdecay t ⟨hlt, ht.2⟩).le

/-- An initial nonpositive floor history is incompatible with a later
positive floor height after bad entry. `hvisible` is the occupation law
on each literal nonpositive prefix. `hboundary` records the open
visibility neighborhood supplied by strict wall gaps when the initial
height is exactly zero. Neither assumption asks for future floor signs. -/
theorem firstFloor_bad_entry_trapping
    {p q u v δ y : ℝ → ℝ} {τ η : ℝ}
    (hτ : 0 ≤ τ) (hτη : τ < η) (hη : η ≤ Real.pi)
    (hp : AbsolutelyContinuousOnInterval p τ η)
    (hy : AbsolutelyContinuousOnInterval y τ η)
    (hpτ : p τ ≤ -1) (hyτ : y τ ≤ 0) (hyη : 0 < y η)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo τ η),
      HasDerivAt p (u t - 1 - q t) t ∧
        HasDerivAt y ((1 - v t) * Real.sin t) t)
    (hvisible : ∀ b ∈ Ioc τ η, (∀ s ∈ Icc τ b, y s ≤ 0) →
      ∀ᵐ t ∂volume.restrict (Ioo τ b), firstFloorVisibleLaw p q u v δ t)
    (hboundary : y τ = 0 → ∃ b ∈ Ioc τ η,
      ∀ᵐ t ∂volume.restrict (Ioo τ b), firstFloorVisibleLaw p q u v δ t) :
    False := by
  have hdecay (b : ℝ) (hb : b ∈ Ioc τ η)
      (hs : ∀ᵐ t ∂volume.restrict (Ioo τ b), firstFloorVisibleLaw p q u v δ t) :
      (∀ t ∈ Icc τ b, y t ≤ y τ) ∧ y b < y τ := by
    have hsub : uIcc τ b ⊆ uIcc τ η := by
      rw [uIcc_of_le hb.1.le, uIcc_of_le hτη.le]
      exact Icc_subset_Icc le_rfl hb.2
    exact (firstFloor_visible_core_decay hτ hb.1 (hb.2.trans hη)
      (hp.mono hsub) (hy.mono hsub) hpτ
      (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hode) hs).2
  obtain ⟨a, ha, hya, hbefore⟩ : ∃ a ∈ Ico τ η, y a < 0 ∧
      (∀ s ∈ Icc τ a, y s ≤ 0) := by
    rcases hyτ.eq_or_lt with heq | hlt
    · obtain ⟨b, hb, hsource⟩ := hboundary heq
      have hd := hdecay b hb hsource
      have hyb : y b < 0 := hd.2.trans_le hyτ
      have hbη : b < η := lt_of_le_of_ne hb.2 (by
        intro heq
        rw [heq] at hyb
        exact (not_lt_of_ge hyη.le) hyb)
      exact ⟨b, ⟨hb.1.le, hbη⟩, hyb,
        fun s hs => (hd.1 s hs).trans hyτ⟩
    · exact ⟨τ, ⟨le_rfl, hτη⟩, hlt, fun s hs => by
        have heq : s = τ := le_antisymm hs.2 hs.1
        simpa only [heq] using hyτ⟩
  have hycont : ContinuousOn y (Icc τ η) := by
    simpa only [uIcc_of_le hτη.le] using hy.continuousOn
  obtain ⟨b, hb, hyb, hnegative⟩ := exists_first_level_crossing ha.2
    ((hycont.mono (Icc_subset_Icc ha.1 le_rfl)).neg)
    (show (0 : ℝ) < -y a by linarith only [hya])
    (show -y η ≤ 0 by linarith only [hyη])
  have hyb0 : y b = 0 := by linarith only [hyb]
  have hτb : b ∈ Ioc τ η := ⟨ha.1.trans_lt hb.1, hb.2⟩
  have hnonpos : ∀ s ∈ Icc τ b, y s ≤ 0 := by
    intro s hs
    by_cases hsa : s ≤ a
    · exact hbefore s ⟨hs.1, hsa⟩
    · rcases hs.2.eq_or_lt with heq | hlt
      · simpa only [heq, hyb0] using (le_rfl : (0 : ℝ) ≤ 0)
      · have hn := hnegative s ⟨(lt_of_not_ge hsa).le, hlt⟩
        linarith only [hn]
  have hlt := (hdecay b hτb (hvisible b hτb hnonpos)).2
  linarith only [hlt, hyb0, hyτ]

end AmbidextrousSofa.Analysis
