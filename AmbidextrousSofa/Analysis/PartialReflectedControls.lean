module

public import AmbidextrousSofa.Analysis.PartialReflectedSupport
public import AmbidextrousSofa.Analysis.TiltedSupportControls

@[expose] public section

/-!
# Actual source controls for the reflected proper arcs

The active reflected interval ends when the original parameter reaches
the affine middle normal, or zero when that normal is negative. Its
closed arm bounds follow from the actual original corner and continuity
of the two closed support derivatives. On the remaining interval both
literal densities are zero. Same-sign shadowing and the sharp curvature
bounds are transferred through the measure-preserving parameter change.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def properReflectedActiveEnd (m : ℝ) : ℝ :=
  Real.pi / 2 - max 0 (Real.arctan m)

variable {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
  (hregime : ProperTailRegime U α m) (hproper : α < Real.pi / 2)
  (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C) (hheight : capHeight U = 1)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
  (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
    (volume.restrict (regularProperCurvatureDomain α m)).withDensity
      (fun t => ENNReal.ofReal (ρ t)))

include hU haffine in
theorem IsJointCapMaximizer.properReflected_active_interval :
    Real.pi / 2 - α < properReflectedActiveEnd m ∧
      properReflectedActiveEnd m ≤ Real.pi / 2 := by
  have h : Real.arctan m < α := by
    simpa [affineNormalAngle] using hU.middle_normal_lt_terminal_companion haffine
  exact ⟨sub_lt_sub_left (max_lt hU.angle_pos h) _, sub_le_self _ (le_max_left _ _)⟩

include hU hproper hl hr hheight haffine hρ hρ0 heq in
theorem IsJointCapMaximizer.proper_wing_densities_zero_before_affine :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.arctan m)),
      ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
  by_cases hm : 0 ≤ m
  · have hmα : Real.arctan m < α := by
      simpa [affineNormalAngle] using hU.middle_normal_lt_terminal_companion haffine
    filter_upwards [ae_density_eq_zero_of_restrict_withDensity_null hρ hρ0 heq measurableSet_Ioo
      (fun t ht => ⟨firstQuarter_subset_regularCurvatureDomain_of_nonneg hm
        ⟨ht.1, ht.2.trans (Real.arctan_lt_pi_div_two m)⟩, (ht.2.trans hmα).ne⟩)
      (hU.proper_first_wing_initial_curvature_zero hproper hl hr hheight hm haffine),
      ae_restrict_mem measurableSet_Ioo] with t ht hmem
    exact ⟨ht, leftCompanionWingDensity_eq_zero <| le_max_of_le_right <| by
      unfold affineNormalAngle; linarith [hmem.2]⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact absurd (Real.arctan_pos.mp (ht.1.trans ht.2)).le hm

include hU hregime hproper hheight haffine hρ hρ0 hρK heq in
theorem IsJointCapMaximizer.properReflected_arm_bounds_of_tail_regime :
    ∀ r ∈ Icc (Real.pi / 2 - α) (properReflectedActiveEnd m),
      properReflectedP U m ρ r ≤ 1 ∧ -1 ≤ properReflectedQ U m ρ r := by
  have hab := hU.properReflected_active_interval haffine
  have hcont := hU.properReflected_momenta_absolutelyContinuous (m := m) hρ hρ0 hρK
  have hinside : ∀ r ∈ Ioo (Real.pi / 2 - α) (properReflectedActiveEnd m),
      properReflectedP U m ρ r ≤ 1 ∧ -1 ≤ properReflectedQ U m ρ r := fun r hr => by
    have hrt : max 0 (Real.arctan m) < Real.pi / 2 - r := by
      unfold properReflectedActiveEnd at hr; linarith [hr.2]
    have hmatch := hU.properUsed_momenta_eq_actual_after_affine_of_tail_regime hregime hproper
      hheight haffine hρ hρ0 hρK heq ⟨(le_max_left _ _).trans hrt.le, by linarith [hr.1]⟩
      ((le_max_right _ _).trans hrt.le)
    rw [properReflectedP, properReflectedQ, hmatch.1, hmatch.2, neg_neg]
    exact ⟨by linarith [hU.isCap.firstCornerVelocity_ge_neg_one (Real.pi / 2 - r)],
      by linarith [hU.isCap.neg_secondCornerVelocity_le_one (Real.pi / 2 - r)]⟩
  have hcl : closure (Ioo (Real.pi / 2 - α) (properReflectedActiveEnd m)) ⊆
      uIcc (Real.pi / 2 - α) (Real.pi / 2) := by
    rw [closure_Ioo hab.1.ne, uIcc_of_le (hab.1.le.trans hab.2)]
    exact Icc_subset_Icc_right hab.2
  intro r hr
  rw [← closure_Ioo hab.1.ne] at hr
  exact ⟨le_on_closure (fun s hs => (hinside s hs).1) (hcont.1.continuousOn.mono hcl)
      continuousOn_const hr,
    le_on_closure (fun s hs => (hinside s hs).2) continuousOn_const
      (hcont.2.continuousOn.mono hcl) hr⟩

include hU hregime hproper hl hr hheight haffine hρ hρ0 hρK hκ heq in
theorem IsJointCapMaximizer.properUsed_source_controls_of_tail_regime :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) α),
      ρ t ≤ sourceKappa (properUsedQ U m ρ t) ∧
      leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ sourceKappa (properUsedP U m ρ t) ∧
      (0 < properUsedP U m ρ t → 0 < properUsedQ U m ρ t →
        ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (properUsedP U m ρ t < 0 → properUsedQ U m ρ t < 0 →
        leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp
      (hU.proper_wing_densities_zero_before_affine hproper hl hr hheight haffine hρ hρ0 heq)),
    ae_restrict_of_ae ((ae_restrict_iff' (isOpen_regularProperCornerDomain α m).measurableSet).mp
      (hU.ae_proper_curvature_same_sign_quadrants hproper haffine hρ hρ0 hρK heq)),
    ae_restrict_of_ae (volume.ae_ne (Real.arctan m))] with t ht hz hs hne
  rcases lt_or_gt_of_ne hne with hpre | hpost
  · obtain ⟨h1, h2⟩ := hz ⟨ht.1, hpre⟩
    simp [h1, h2, sourceKappa_nonneg]
  obtain ⟨hP, hQ⟩ := hU.properUsed_momenta_eq_actual_after_affine_of_tail_regime hregime hproper
    hheight haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le
  have hsource := hs ⟨⟨ht.1, ht.2.trans hproper⟩,
    hU.proper_first_arc_subset_regular_of_tail_regime hregime hproper hheight haffine ht,
    regularCompanionDomain_subset_regularProperCurvatureDomain hproper ⟨⟨by linarith [ht.1],
      by linarith [ht.2]⟩, fun h => hne (by simpa [affineNormalAngle] using h)⟩⟩
  have hbounds := upperCorner_density_bounds_on_quarter hκ ⟨ht.1, ht.2.trans hproper⟩
  rw [hP, hQ, leftCompanionWingDensity_shift_eq_after ht.1 hpost, sourceKappa_neg]
  exact ⟨hbounds.1, hbounds.2, fun hp hq => hsource.1 ⟨hq, neg_pos.mp hp⟩,
    fun hp hq => hsource.2 ⟨hq, neg_lt_zero.mp hp⟩⟩

include hU hregime hproper hl hr hheight haffine hρ hρ0 hρK hκ heq in
theorem IsJointCapMaximizer.properReflected_source_controls_of_tail_regime :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      0 ≤ properReflectedFirstDensity m ρ r ∧
      0 ≤ properReflectedSecondDensity ρ r ∧
      properReflectedFirstDensity m ρ r ≤ sourceKappa (properReflectedQ U m ρ r) ∧
      properReflectedSecondDensity ρ r ≤ sourceKappa (properReflectedP U m ρ r) ∧
      (0 < properReflectedP U m ρ r → 0 < properReflectedQ U m ρ r →
        properReflectedFirstDensity m ρ r = 0 ∧ properReflectedSecondDensity ρ r ≤ 1 / 2) ∧
      (properReflectedP U m ρ r < 0 → properReflectedQ U m ρ r < 0 →
        properReflectedSecondDensity ρ r = 0 ∧ properReflectedFirstDensity m ρ r ≤ 1 / 2) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
    ((volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).mp (hU.properUsed_source_controls_of_tail_regime
        hregime hproper hl hr hheight haffine hρ hρ0 hρK hκ heq)))] with r hr hs
  obtain ⟨hu, hv, hpp, hmm⟩ :=
    hs (show Real.pi / 2 - r ∈ Ioo 0 α from ⟨by linarith [hr.2], by linarith [hr.1]⟩)
  simp only [properReflectedFirstDensity, properReflectedSecondDensity, properReflectedP,
    properReflectedQ, sourceKappa_neg, neg_pos, neg_lt_zero]
  exact ⟨(leftCompanionWingDensity_bounds hρ0 hρK _).1, hρ0 _, hv, hu,
    fun h1 h2 => hmm h2 h1, fun h1 h2 => hpp h2 h1⟩

include hU hproper hl hr hheight haffine hρ hρ0 heq in
theorem IsJointCapMaximizer.properReflected_densities_zero_after_active :
    ∀ᵐ r ∂volume.restrict (Ioo (properReflectedActiveEnd m) (Real.pi / 2)),
      properReflectedFirstDensity m ρ r = 0 ∧ properReflectedSecondDensity ρ r = 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae
    ((volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).mp (hU.proper_wing_densities_zero_before_affine
        hproper hl hr hheight haffine hρ hρ0 heq)))] with r hr hs
  have ht0 : 0 < Real.pi / 2 - r := by linarith [hr.2]
  unfold properReflectedActiveEnd at hr
  have h := hs ⟨ht0, (lt_max_iff.mp (by linarith [hr.1])).resolve_left ht0.le.not_gt⟩
  exact ⟨h.2, h.1⟩

end AmbidextrousSofa
