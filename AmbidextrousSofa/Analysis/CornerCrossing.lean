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

open Set MeasureTheory

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
  have hq0 (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ q t :=
    ht.2.eq_or_lt.elim (fun h => h ▸ hqb.ge) fun h => (hqpos t ⟨ht.1, h⟩).le
  -- The source bound makes `r` increase, so `r` stays positive.
  have hrpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < r t := by
    have := absolutelyContinuousOnInterval_linear_lower_bound (d := fun t => q t + 1 - u t)
      (k := 1 / 2) hr hab.le (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hκ] with t ht hd hk
        exact ⟨hd.2, by linarith [hk.1.trans (sourceKappa_le_self_add_half
          (hq0 t (Ioo_subset_Icc_self ht)))]⟩) ht
    linarith [ht.1]
  -- Then `q` decreases from `1`, and the flux bound caps `r` by `1`.
  have hq1 (t : ℝ) (ht : t ∈ Icc a b) : q t ≤ 1 :=
    hqa ▸ absolutelyContinuousOnInterval_le_initial_of_ae_deriv_nonpos hq hab.le (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hv] with t ht hd hv
      linarith [hd.1.deriv, hrpos t (Ioo_subset_Icc_self ht)]) ht
  have hr1 := ContinuousOn.le_on_Icc_of_ae_le_on_Ioo (C := 1)
    (uIcc_of_le hab.le ▸ hr.continuousOn) hab (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hflux, hv] with t ht hf hv
      linarith [hf (hqpos t ⟨ht.1.le, ht.2⟩) (hrpos t (Ioo_subset_Icc_self ht))])
  -- The squared distance `(1 + r)^2 + (1 + q)^2` cannot decrease.
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) a b :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have := absolutelyContinuousOnInterval_linear_lower_bound (k := 0)
    (((hconst.add hr).mul (hconst.add hr)).add ((hconst.add hq).mul (hconst.add hq))) hab.le (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo, hode, hκ, hflux] with t ht hd hk hf
      have htcc := Ioo_subset_Icc_self ht
      refine ⟨((hd.2.const_add 1).mul (hd.2.const_add 1)).add
        ((hd.1.const_add 1).mul (hd.1.const_add 1)), ?_⟩
      rw [sourceKappa_eq_half_of_mem_Icc ⟨hq0 t htcc, hq1 t htcc⟩] at hk
      simp only [Pi.add_apply]
      linarith [mul_nonneg (by linarith [hrpos t htcc] : 0 ≤ 1 + r t) (sub_nonneg.mpr hk.1),
        mul_nonneg (by linarith [hq0 t htcc] : 0 ≤ 1 + q t)
          (sub_nonneg.mpr (hf (hqpos t ⟨ht.1.le, ht.2⟩) (hrpos t htcc)))])
    ⟨hab.le, le_rfl⟩
  simp only [Pi.add_apply, Pi.mul_apply, hqa, hqb] at this
  nlinarith [hrpos b ⟨hab.le, le_rfl⟩, hr1 b ⟨hab.le, le_rfl⟩]

theorem upperCorner_density_bounds_on_quarter
    {U : Set Plane} {ρ : ℝ → ℝ}
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    ρ t ≤ sourceKappa (firstCornerVelocity U t) ∧
      ρ (t + Real.pi / 2) ≤ sourceKappa (secondCornerVelocity U t) :=
  ⟨by simpa [upperCornerVelocity, ht.2] using hκ t,
    by simpa [upperCornerVelocity, ht.1.not_gt] using hκ (t + Real.pi / 2)⟩

theorem IsFullCapMaximizer.exists_later_negative_firstCornerVelocity
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (hmiddle : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x = 1)
    {a : ℝ} (ha : a < Real.pi / 2) :
    ∃ b ∈ Ioo a (Real.pi / 2), firstCornerVelocity U b < 0 := by
  have heL := (hU.endpoint_heights_pos_of_affine hheight
    ⟨0, 1, by simpa only [zero_mul, zero_add] using hmiddle⟩).2
  have hnegative := (hU.cornerVelocities_tendsto_pi_div_two_left hheight
    hmiddle).fst_nhds.eventually (eventually_lt_nhds (neg_neg_of_pos heL))
  obtain ⟨b, hab, hbL, hbq⟩ := (((eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds).and
    (eventually_mem_nhdsWithin.and hnegative)).exists
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
  have hsubT : Icc a T ⊆ regularCornerDomain 0 := regularCornerDomain_zero ▸
    fun t ht => ⟨ha.1.trans_le ht.1, ht.2.trans_lt hT.2⟩
  have hdirT := regularCornerDomain_interval_directions hsubT
  obtain ⟨b, hb, hqb, hqpos⟩ := exists_first_level_crossing hT.1 (uIcc_of_le hT.1.le ▸
    (hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
      hρ hρ0 hρC heq hT.1.le hdirT.1 hdirT.2).1.continuousOn) (hqa ▸ one_pos) hqT.le
  have hdir := regularCornerDomain_interval_directions ((Icc_subset_Icc le_rfl hb.2).trans hsubT)
  have hac := hU.isCap.absolutelyContinuousOnInterval_cornerVelocities_of_density
    hρ hρ0 hρC heq hb.1.le hdir.1 hdir.2
  have hI : Ioo a b ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    fun t ht => ⟨ha.1.trans ht.1, (ht.2.trans_le hb.2).trans hT.2⟩
  have hflux := hU.ae_companion_density_ge_of_unit_companion_and_future hheight hmiddle
    hρ hρ0 hρC heq ha.1.le hcompanion (hU.ae_density_le_one_after_cornerEnergy hmiddle
      hρ hρ0 hρC hκ heq ha (actualCornerEnergy_eq_threshold_of_first_eq_one hqa hra.le).le)
  exact corner_first_descent_contradiction hac.1 hac.2 hb.1 hqa hqb hra hqpos
    (hU.isCap.ae_hasDerivAt_cornerVelocities_of_density hρ hρ0 hρC heq hb.1.le hdir.1 hdir.2)
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht =>
      upperCorner_density_bounds_on_quarter hκ (hI ht))
    (ae_restrict_of_ae_restrict_of_subset hI hcompanion)
    (ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl (hb.2.trans hT.2.le)) hflux)

end AmbidextrousSofa
