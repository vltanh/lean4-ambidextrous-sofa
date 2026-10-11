module

public import AmbidextrousSofa.Analysis.FirstUnitCrossings
public import AmbidextrousSofa.Measure.SupportAreaAC

@[expose] public section

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
  -- Full occupation on `(τ, b)`: `p` decreases at unit speed and `y` strictly decreases.
  have hdecay (b : ℝ) (hb : b ∈ Ioc τ η)
      (hs : ∀ᵐ t ∂volume.restrict (Ioo τ b), firstFloorVisibleLaw p q u v δ t) :
      (∀ t ∈ Icc τ b, y t ≤ y τ) ∧ y b < y τ := by
    have hode' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hode
    have hint {g D : ℝ → ℝ} (hg : AbsolutelyContinuousOnInterval g τ η)
        (hD : ∀ᵐ t ∂volume.restrict (Ioo τ b), HasDerivAt g (D t) t) {t : ℝ}
        (ht : t ∈ Icc τ b) : ∫ s in τ..t, D s = g t - g τ :=
      integral_eq_sub_of_ac_of_ae_hasDerivAt ht.1
        (hg.mono (uIcc_subset_uIcc_left (Icc_subset_uIcc ⟨ht.1, ht.2.trans hb.2⟩)))
        (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl ht.2) hD)
    have hpExact (t : ℝ) (ht : t ∈ Icc τ b) : p t = p τ - (t - τ) := by
      have h := hint hp (D := fun _ => -1) (by
        filter_upwards [hode', hs] with t hd hs
        exact hd.1.congr_deriv (by rw [hs.1]; ring)) ht
      simp only [intervalIntegral.integral_const, smul_eq_mul] at h
      linarith
    have hyD : ∀ᵐ t ∂volume.restrict (Ioo τ b),
        HasDerivAt y (-((t - τ - 1 - p τ) * Real.sin t)) t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hode', hs] with t ht hd hs
      have hpt := hpExact t (Ioo_subset_Icc_self ht)
      have hv : 1 < v t := by
        by_contra! hv
        linarith [mul_nonneg (sub_nonneg.2 hv) hs.2.2.1, hs.2.1, ht.1]
      have hvp : v t = -p t := by simpa only [hs.2.2.2 hv, mul_zero, zero_sub] using hs.2.1
      exact hd.2.congr_deriv (by rw [hvp, hpt]; ring)
    have hlt (t : ℝ) (ht : t ∈ Ioc τ b) : y t < y τ := by
      have hi := hint hy hyD ⟨ht.1.le, ht.2⟩
      have hpos : 0 < ∫ s in τ..t, (s - τ - 1 - p τ) * Real.sin s :=
        intervalIntegral.intervalIntegral_pos_of_pos_on
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (fun s hs => mul_pos (by linarith [hs.1]) (Real.sin_pos_of_pos_of_lt_pi
            (hτ.trans_lt hs.1) (hs.2.trans_le (ht.2.trans (hb.2.trans hη))))) ht.1
      rw [intervalIntegral.integral_neg] at hi
      linarith
    refine ⟨fun t ht => ?_, hlt b ⟨hb.1, le_rfl⟩⟩
    rcases ht.1.eq_or_lt with rfl | h
    exacts [le_rfl, (hlt t ⟨h, ht.2⟩).le]
  obtain ⟨a, ha, hya, hbefore⟩ : ∃ a ∈ Ico τ η, y a < 0 ∧ ∀ s ∈ Icc τ a, y s ≤ 0 := by
    rcases hyτ.eq_or_lt with heq | hlt
    · obtain ⟨b, hb, hsource⟩ := hboundary heq
      obtain ⟨hd1, hd2⟩ := hdecay b hb hsource
      exact ⟨b, ⟨hb.1.le, hb.2.lt_of_ne (by rintro rfl; linarith)⟩, by linarith,
        fun s hs => (hd1 s hs).trans hyτ⟩
    · exact ⟨τ, ⟨le_rfl, hτη⟩, hlt, fun s hs => le_antisymm hs.2 hs.1 ▸ hyτ⟩
  obtain ⟨b, hb, hyb, hnegative⟩ := exists_first_level_crossing ha.2
    (hy.continuousOn.mono ((Icc_subset_Icc ha.1 le_rfl).trans Icc_subset_uIcc)).neg
    (show (0 : ℝ) < -y a by linarith) (show -y η ≤ 0 by linarith)
  simp only [Pi.neg_apply] at hyb hnegative
  have hτb : b ∈ Ioc τ η := ⟨ha.1.trans_lt hb.1, hb.2⟩
  have hnonpos : ∀ s ∈ Icc τ b, y s ≤ 0 := fun s hs => by
    rcases le_or_gt s a with hsa | hsa
    · exact hbefore s ⟨hs.1, hsa⟩
    rcases hs.2.eq_or_lt with rfl | hsb
    · linarith
    · linarith [hnegative s ⟨hsa.le, hsb⟩]
  linarith [(hdecay b hτb (hvisible b hτb hnonpos)).2]

end AmbidextrousSofa.Analysis
