module

public import AmbidextrousSofa.Analysis.VisibleFluxDensity
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

/-!
# Actual first level crossings and the corner energy threshold

First crossings are constructed by compactness of the literal level set.
The regular-interval energy barrier extends to the complete open future
of a horizontal corner, and an a.e. bound of a continuous function extends
to both endpoints of a nondegenerate interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem exists_first_level_crossing {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (ha : c < f a) (hb : f b ≤ c) :
    ∃ t ∈ Ioc a b, f t = c ∧ ∀ u ∈ Ico a t, c < f u := by
  obtain ⟨t, ⟨ht, hft⟩, hmin⟩ := (isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
    inter_subset_left).exists_isLeast (intermediate_value_Icc' hab.le hf ⟨hb, ha.le⟩)
  refine ⟨t, ⟨ht.1.lt_of_ne (by rintro rfl; exact ha.ne' hft), ht.2⟩, hft, fun u hu => ?_⟩
  by_contra! hfu
  have hub := hu.2.le.trans ht.2
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hu.1 (hf.mono (Icc_subset_Icc le_rfl hub))
    ⟨hfu, ha.le⟩
  exact hu.2.not_ge ((hmin ⟨⟨hv.1, hv.2.trans hub⟩, hfv⟩).trans hv.2)

theorem ContinuousOn.le_on_Icc_of_ae_le_on_Ioo
    {f : ℝ → ℝ} {a b C : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a < b)
    (hle : ∀ᵐ x ∂volume.restrict (Ioo a b), f x ≤ C) :
    ∀ x ∈ Icc a b, f x ≤ C := by
  have hEq : (fun x => min (f x) C) =ᵐ[volume.restrict (Icc a b)] f := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hle] with x hx using min_eq_left hx
  exact fun x hx => (Measure.eqOn_Icc_of_ae_eq volume hab.ne hEq (hf.inf continuousOn_const) hf
    hx).symm.trans_le (min_le_right _ _)

theorem sourceKappa_le_self_add_half {q : ℝ} (hq : 0 ≤ q) :
    sourceKappa q ≤ q + 1 / 2 := by
  simp only [sourceKappa, abs_of_nonneg hq]
  apply max_le <;> linarith

theorem sourceKappa_eq_half_of_mem_Icc {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    sourceKappa q = (q + 1) / 2 := by
  rw [sourceKappa, abs_of_nonneg hq.1, max_eq_right]
  linarith [hq.2]

theorem sourceKappa_eq_self_of_one_le {q : ℝ} (hq : 1 ≤ q) : sourceKappa q = q := by
  rw [sourceKappa, abs_of_nonneg (by linarith), max_eq_left]
  linarith

theorem absolutelyContinuousOnInterval_linear_lower_bound
    {f d : ℝ → ℝ} {a b k x : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hab : a ≤ b)
    (hd : ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (d t) t ∧ k ≤ d t)
    (hx : x ∈ Icc a b) : f a + k * (x - a) ≤ f x := by
  have hax := hf.mono (uIcc_subset_uIcc_left (uIcc_of_le hab ▸ hx))
  have hi := intervalIntegral.integral_mono_ae_restrict hx.1 intervalIntegrable_const
    hax.intervalIntegrable_deriv (by
      rw [← restrict_Ioo_eq_restrict_Icc]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hx.2) hd]
        with t ht using ht.2.trans_eq ht.1.deriv.symm)
  rw [hax.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hi
  linarith

theorem IsFullCapMaximizer.ae_density_le_one_after_cornerEnergy
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C c a : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hstart : actualCornerEnergy U a ≤ 17 / 4) :
    ∀ᵐ t ∂volume.restrict (Ioo a (Real.pi / 2)), ρ t ≤ 1 := by
  refine ae_restrict_of_local_intervals isOpen_Ioo fun t ht => ?_
  obtain ⟨b, htb, hbL⟩ := exists_between ht.2
  exact ⟨a, b, ⟨ht.1, htb⟩, hU.ae_density_le_one_of_cornerEnergy_on_interval
    (m := 0) (c := c) (by simpa only [zero_mul, zero_add] using haffine)
    hρ hρ0 hρC hκ heq (ht.1.le.trans htb.le)
    (regularCornerDomain_zero ▸ fun u hu => ⟨ha.1.trans_le hu.1, hu.2.trans_lt hbL⟩) hstart⟩

theorem actualCornerEnergy_eq_threshold_of_first_eq_one
    {U : Set Plane} {a : ℝ} (hq : firstCornerVelocity U a = 1)
    (hr : 0 ≤ secondCornerVelocity U a) : actualCornerEnergy U a = 17 / 4 := by
  norm_num [actualCornerEnergy, clippedCornerEnergy, hq, max_eq_right (neg_nonpos.mpr hr)]

end AmbidextrousSofa
