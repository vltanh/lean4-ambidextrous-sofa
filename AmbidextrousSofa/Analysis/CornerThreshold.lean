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
  let Z : Set ℝ := Icc a b ∩ f ⁻¹' {c}
  have hZ : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (hf.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton)) inter_subset_left
  have hne : Z.Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hab.le hf ⟨hb, ha.le⟩
    exact ⟨t, ht, hft⟩
  obtain ⟨t, ht, hmin⟩ := hZ.exists_isLeast hne
  have hft : f t = c := ht.2
  have hat : a < t := by
    apply lt_of_le_of_ne ht.1.1
    intro heq
    have hfa : f a = c := by simpa only [← heq] using hft
    exact (ne_of_gt ha) hfa
  refine ⟨t, ⟨hat, ht.1.2⟩, hft, ?_⟩
  intro u hu
  by_contra hnot
  have hfu : f u ≤ c := le_of_not_gt hnot
  have huB : u ≤ b := hu.2.le.trans ht.1.2
  obtain ⟨v, hv, hfv⟩ := intermediate_value_Icc' hu.1
    (hf.mono (Icc_subset_Icc le_rfl huB)) ⟨hfu, ha.le⟩
  have hvZ : v ∈ Z := ⟨⟨hv.1, hv.2.trans huB⟩, hfv⟩
  exact (not_le_of_gt hu.2) ((hmin hvZ).trans hv.2)

theorem ContinuousOn.le_on_Icc_of_ae_le_on_Ioo
    {f : ℝ → ℝ} {a b C : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a < b)
    (hle : ∀ᵐ x ∂volume.restrict (Ioo a b), f x ≤ C) :
    ∀ x ∈ Icc a b, f x ≤ C := by
  have hEq : (fun x => min (f x) C) =ᵐ[volume.restrict (Icc a b)] f := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hle] with x hx
    exact min_eq_left hx
  have hclosed : Icc a b ⊆ closure (interior (Icc a b)) := by
    simpa only [interior_Icc, closure_Ioo hab.ne] using
      (Subset.rfl : Icc a b ⊆ Icc a b)
  have heq := Measure.eqOn_of_ae_eq hEq (hf.inf continuousOn_const) hf hclosed
  intro x hx
  calc
    f x = min (f x) C := (heq hx).symm
    _ ≤ C := min_le_right _ _

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
  have hax : AbsolutelyContinuousOnInterval f a x := hf.mono (by
    rw [uIcc_of_le hab, uIcc_of_le hx.1]
    exact Icc_subset_Icc le_rfl hx.2)
  have hdcc : ∀ᵐ t ∂volume.restrict (Icc a x), k ≤ deriv f t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl hx.2) hd] with t ht
    rw [ht.1.deriv]
    exact ht.2
  have hi := intervalIntegral.integral_mono_ae_restrict hx.1 intervalIntegrable_const
    hax.intervalIntegrable_deriv hdcc
  rw [hax.integral_deriv_eq_sub, intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  nlinarith

theorem IsFullCapMaximizer.ae_density_le_one_after_cornerEnergy
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C c a : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hstart : actualCornerEnergy U a ≤ 17 / 4) :
    ∀ᵐ t ∂volume.restrict (Ioo a (Real.pi / 2)), ρ t ≤ 1 := by
  apply ae_restrict_of_local_intervals isOpen_Ioo
  intro t ht
  obtain ⟨b, htb, hbL⟩ := exists_between ht.2
  have hsub : Icc a b ⊆ regularCornerDomain 0 := by
    intro u hu
    have huq : u ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨ha.1.trans_le hu.1, hu.2.trans_lt hbL⟩
    simpa only [regularCornerDomain_zero] using huq
  exact ⟨a, b, ⟨ht.1, htb⟩, hU.ae_density_le_one_of_cornerEnergy_on_interval
    (m := 0) (c := c) (by simpa only [zero_mul, zero_add] using haffine)
    hρ hρ0 hρC hκ heq (ht.1.le.trans htb.le) hsub hstart⟩

theorem actualCornerEnergy_eq_threshold_of_first_eq_one
    {U : Set Plane} {a : ℝ} (hq : firstCornerVelocity U a = 1)
    (hr : 0 ≤ secondCornerVelocity U a) : actualCornerEnergy U a = 17 / 4 := by
  simp only [actualCornerEnergy, clippedCornerEnergy, hq,
    max_eq_right (neg_nonpos.mpr hr)]
  norm_num

end AmbidextrousSofa
