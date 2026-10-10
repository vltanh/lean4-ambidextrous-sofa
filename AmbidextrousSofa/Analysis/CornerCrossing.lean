module

public import AmbidextrousSofa.Analysis.CornerThreshold

@[expose] public section

/-!
# A positive-corner crossing is incompatible with unit companion curvature

On a genuine first descent from `q = 1` to `q = 0`, the source bound
makes the other corner velocity increase. The actual visible-source
flux then determines the companion density, and the squared distance
`(1 + r)^2 + (1 + q)^2` cannot decrease. Its endpoint values contradict
that conclusion. No partition into prescribed curvature phases is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem corner_first_descent_contradiction
    {q r u v : ℝ → ℝ} {a b : ℝ}
    (hq : AbsolutelyContinuousOnInterval q a b)
    (hr : AbsolutelyContinuousOnInterval r a b) (hab : a < b)
    (hqa : q a = 1) (hqb : q b = 0) (hra : 0 < r a)
    (hqpos : ∀ t ∈ Ico a b, 0 < q t)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt q (v t - r t - 1) t ∧ HasDerivAt r (q t + 1 - u t) t)
    (hκ : ∀ᵐ t ∂volume.restrict (Ioo a b),
      u t ≤ sourceKappa (q t) ∧ v t ≤ sourceKappa (r t))
    (hv : ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ 1)
    (hflux : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 < q t → 0 < r t → 1 + r t ≤ 2 * v t) : False := by
  have hq0 : ∀ t ∈ Icc a b, 0 ≤ q t := by
    intro t ht
    by_cases htb : t = b
    · simpa only [htb, hqb] using (le_rfl : (0 : ℝ) ≤ 0)
    · exact (hqpos t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩).le
  have hrd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt r (q t + 1 - u t) t ∧ 1 / 2 ≤ q t + 1 - u t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hκ] with t ht hd hk
    refine ⟨hd.2, ?_⟩
    have hu := hk.1.trans (sourceKappa_le_self_add_half (hq0 t (Ioo_subset_Icc_self ht)))
    linarith
  have hrpos : ∀ t ∈ Icc a b, 0 < r t := by
    intro t ht
    have hle := absolutelyContinuousOnInterval_linear_lower_bound hr hab.le hrd ht
    have hmul : 0 ≤ (1 / 2 : ℝ) * (t - a) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr ht.1)
    linarith
  have hqd : ∀ᵐ t ∂volume.restrict (Ioo a b), deriv q t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hv] with t ht hd hv'
    rw [hd.1.deriv]
    have hp := hrpos t (Ioo_subset_Icc_self ht)
    linarith
  have hq1 : ∀ t ∈ Icc a b, q t ≤ 1 := by
    intro t ht
    simpa only [hqa] using
      absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos hq hab.le hqd ht
  have hr1ae : ∀ᵐ t ∂volume.restrict (Ioo a b), r t ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hflux, hv] with t ht hf hv'
    have hle := hf (hqpos t ⟨ht.1.le, ht.2⟩) (hrpos t (Ioo_subset_Icc_self ht))
    linarith
  have hrc : ContinuousOn r (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using hr.continuousOn
  have hr1 := hrc.le_on_Icc_of_ae_le_on_Ioo hab hr1ae
  have hvEq : ∀ᵐ t ∂volume.restrict (Ioo a b), v t = (r t + 1) / 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hκ, hflux] with t ht hk hf
    have htcc := Ioo_subset_Icc_self ht
    have hbound := hk.2
    rw [sourceKappa_eq_half_of_mem_Icc ⟨(hrpos t htcc).le, hr1 t htcc⟩] at hbound
    have hlow := hf (hqpos t ⟨ht.1.le, ht.2⟩) (hrpos t htcc)
    linarith
  let E : ℝ → ℝ := fun t => (1 + r t) ^ 2 + (1 + q t) ^ 2
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hE : AbsolutelyContinuousOnInterval E a b := by
    simpa only [E, Pi.add_apply, Pi.mul_apply, pow_two] using
      ((hconst.add hr).mul (hconst.add hr)).add ((hconst.add hq).mul (hconst.add hq))
  have hEd : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt E
        (2 * (1 + r t) * (q t + 1 - u t) + 2 * (1 + q t) * (v t - r t - 1)) t ∧
      0 ≤ 2 * (1 + r t) * (q t + 1 - u t) +
        2 * (1 + q t) * (v t - r t - 1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hκ, hvEq] with t ht hd hk hv'
    have htcc := Ioo_subset_Icc_self ht
    constructor
    · have hdE := ((hd.2.const_add 1).pow 2).add ((hd.1.const_add 1).pow 2)
      change HasDerivAt E _ t at hdE
      exact hdE.congr_deriv (by norm_num; ring)
    · have hu := hk.1
      rw [sourceKappa_eq_half_of_mem_Icc ⟨hq0 t htcc, hq1 t htcc⟩] at hu
      have hp := mul_nonneg (by linarith [hrpos t htcc] : 0 ≤ 1 + r t)
        (sub_nonneg.mpr hu)
      rw [hv']
      nlinarith
  have hEab := absolutelyContinuousOnInterval_linear_lower_bound hE hab.le hEd
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  have hrb0 := (hrpos b ⟨hab.le, le_rfl⟩).le
  have hrb1 := hr1 b ⟨hab.le, le_rfl⟩
  have hprod := mul_nonneg (by linarith : 0 ≤ 1 - r b)
    (by linarith : 0 ≤ 3 + r b)
  dsimp only [E] at hEab
  rw [hqa, hqb] at hEab
  nlinarith [sq_nonneg (r a)]

theorem upperCorner_density_bounds_on_quarter
    {U : Set Plane} {ρ : ℝ → ℝ}
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ t ≤ sourceKappa (firstCornerVelocity U t) ∧
      ρ (t + Real.pi / 2) ≤ sourceKappa (secondCornerVelocity U t) := by
  have hnot : ¬ t + Real.pi / 2 < Real.pi / 2 := by linarith [ht.1]
  constructor
  · simpa only [upperCornerVelocity, if_pos ht.2] using hκ t
  · simpa only [upperCornerVelocity, if_neg hnot, add_sub_cancel_right] using
      hκ (t + Real.pi / 2)

theorem IsFullCapMaximizer.exists_later_negative_firstCornerVelocity
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    {a : ℝ} (ha : a < Real.pi / 2) :
    ∃ b ∈ Ioo a (Real.pi / 2), firstCornerVelocity U b < 0 := by
  have heL := (hU.endpoint_heights_pos_of_affine hheight
    ⟨0, 1, by simpa only [zero_mul, zero_add] using hmiddle⟩).2
  have hlim := (hU.cornerVelocities_tendsto_pi_div_two_left hheight hmiddle).fst
  have hnegative : ∀ᶠ b in 𝓝[<] (Real.pi / 2), firstCornerVelocity U b < 0 :=
    hlim.eventually (eventually_lt_nhds (by linarith : -capRoof U (horizontalLeft U) < 0))
  have hlater : ∀ᶠ b in 𝓝[<] (Real.pi / 2), a < b :=
    (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds
  obtain ⟨b, hab, hbL, hbq⟩ := (hlater.and (self_mem_nhdsWithin.and hnegative)).exists
  exact ⟨b, ⟨hab, hbL⟩, hbq⟩

theorem IsFullCapMaximizer.not_first_eq_one_and_second_pos_of_unit_companion
    {U : Set Plane} (hU : IsFullCapMaximizer U) {ρ : ℝ → ℝ} {C a : ℝ}
    (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρC : ∀ t, ρ t ≤ C)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain 0) =
      (volume.restrict (regularCurvatureDomain 0)).withDensity (fun t => ENNReal.ofReal (ρ t)))
    (hcompanion : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ (t + Real.pi / 2) ≤ 1)
    (ha : a ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    ¬ (firstCornerVelocity U a = 1 ∧ 0 < secondCornerVelocity U a) := by
  rintro ⟨hqa, hra⟩
  obtain ⟨T, hT, hqT⟩ := hU.exists_later_negative_firstCornerVelocity hheight hmiddle ha.2
  have hsubT : Icc a T ⊆ regularCornerDomain 0 := by
    rw [regularCornerDomain_zero]
    exact fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hT.2⟩
  have hdirT := regularCornerDomain_interval_directions hsubT
  have hacT := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hT.1.le hdirT.1 hdirT.2
  have hqcont : ContinuousOn (firstCornerVelocity U) (Icc a T) := by
    simpa only [uIcc_of_le hT.1.le] using hacT.1.continuousOn
  obtain ⟨b, hb, hqb, hqpos⟩ := exists_first_level_crossing hT.1 hqcont
    (by simpa only [hqa] using (show (0 : ℝ) < 1 by norm_num)) hqT.le
  have hsub : Icc a b ⊆ regularCornerDomain 0 :=
    (Icc_subset_Icc le_rfl hb.2).trans hsubT
  have hdir := regularCornerDomain_interval_directions hsub
  have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hb.1.le hdir.1 hdir.2
  have hode := hU.isCap.ae_hasDerivAt_cornerVelocities_of_density
    hρ hρ0 hρC heq hb.1.le hdir.1 hdir.2
  have hfuture := hU.ae_density_le_one_after_cornerEnergy hmiddle hρ hρ0 hρC hκ heq ha
    (actualCornerEnergy_eq_threshold_of_first_eq_one hqa hra.le).le
  have hflux := hU.ae_companion_density_ge_of_unit_companion_and_future hheight hmiddle
    hρ hρ0 hρC heq ha.1.le hcompanion hfuture
  have hI : Ioo a b ⊆ Ioo (0 : ℝ) (Real.pi / 2) := by
    intro t ht
    exact ⟨ha.1.trans ht.1, (ht.2.trans_le hb.2).trans hT.2⟩
  have hIfuture : Ioo a b ⊆ Ioo a (Real.pi / 2) :=
    Ioo_subset_Ioo le_rfl (hb.2.trans hT.2.le)
  have hk : ∀ᵐ t ∂volume.restrict (Ioo a b),
      ρ t ≤ sourceKappa (firstCornerVelocity U t) ∧
      ρ (t + Real.pi / 2) ≤ sourceKappa (secondCornerVelocity U t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact upperCorner_density_bounds_on_quarter hκ (hI ht)
  exact corner_first_descent_contradiction hac.1 hac.2 hb.1 hqa hqb hra hqpos
    hode hk (ae_restrict_of_ae_restrict_of_subset hI hcompanion)
    (ae_restrict_of_ae_restrict_of_subset hIfuture hflux)

end AmbidextrousSofa
