import AmbidextrousSofa.Analysis.PartialReflectedSupport
import AmbidextrousSofa.Analysis.TiltedSupportControls

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

theorem IsJointCapMaximizer.properReflected_active_interval
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    Real.pi / 2 - α < properReflectedActiveEnd m ∧
      properReflectedActiveEnd m ≤ Real.pi / 2 := by
  have hmα : Real.arctan m < α := by
    have h := hU.middle_normal_lt_terminal_companion haffine
    unfold affineNormalAngle at h
    linarith only [h]
  have hmax : max 0 (Real.arctan m) < α := max_lt hU.angle_pos hmα
  dsimp only [properReflectedActiveEnd]
  exact ⟨sub_lt_sub_left hmax _, sub_le_self _ (le_max_left _ _)⟩

theorem IsJointCapMaximizer.mem_regularProperCornerDomain_after_affine
    {U : Set Plane} {α m c t : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (ht : t ∈ Ioo (0 : ℝ) α) (hmt : Real.arctan m < t) :
    t ∈ regularProperCornerDomain α m := by
  refine ⟨⟨ht.1, ht.2.trans hproper⟩,
    hU.proper_first_arc_subset_regular hLargest hproper hheight haffine ht, ?_⟩
  apply regularCompanionDomain_subset_regularProperCurvatureDomain hproper
  refine ⟨⟨by linarith only [ht.1], by linarith only [ht.2, hproper]⟩, ?_⟩
  intro heq
  simp only [mem_singleton_iff] at heq
  unfold affineNormalAngle at heq
  linarith only [heq, hmt]

theorem IsJointCapMaximizer.proper_wing_densities_zero_before_affine
    {U : Set Plane} {α C m c : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.arctan m)),
      ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
  by_cases hm : 0 ≤ m
  · have hzero := hU.proper_first_wing_initial_curvature_zero
      hproper hl hr hheight hm haffine
    have hmα : Real.arctan m < α := by
      have h := hU.middle_normal_lt_terminal_companion haffine
      unfold affineNormalAngle at h
      linarith only [h]
    have hsub : Ioo (0 : ℝ) (Real.arctan m) ⊆ regularProperCurvatureDomain α m := by
      intro t ht
      exact ⟨firstQuarter_subset_regularCurvatureDomain_of_nonneg hm
        ⟨ht.1, ht.2.trans (Real.arctan_lt_pi_div_two m)⟩, (ht.2.trans hmα).ne⟩
    have hfirst := ae_density_eq_zero_of_restrict_withDensity_null hρ hρ0 heq
      measurableSet_Ioo hsub hzero
    filter_upwards [hfirst, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    refine ⟨ht, leftCompanionWingDensity_eq_zero ?_⟩
    apply le_trans _ (le_max_right _ _)
    unfold affineNormalAngle
    linarith only [hmem.2]
  · have hm0 : Real.arctan m ≤ 0 := Real.arctan_nonpos.mpr (le_of_not_ge hm)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exfalso
    linarith only [ht.1, ht.2, hm0]

theorem IsJointCapMaximizer.properUsed_momenta_continuous
    {U : Set Plane} {α m K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) :
    Continuous (properUsedP U m ρ) ∧ Continuous (properUsedQ U m ρ) := by
  have hV := hU.isCap_properLeftCompanion
  have hf := hU.isCap.imported_isConvexBody.continuous_supp
  have hg := hV.imported_isConvexBody.continuous_supp.comp
    (continuous_id.add_const (Real.pi / 2))
  have hfD := hU.isCap.continuous_closedSupportDerivative hρ hρ0 hρK 0
  have hgD := hV.continuous_closedSupportDerivative
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).2) (Real.pi / 2)
  exact ⟨(hfD.sub hg).add continuous_const, (hgD.add hf).sub continuous_const⟩

theorem IsJointCapMaximizer.properReflected_momenta_continuous
    {U : Set Plane} {α m K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) :
    Continuous (properReflectedP U m ρ) ∧ Continuous (properReflectedQ U m ρ) := by
  have h := hU.properUsed_momenta_continuous (m := m) hρ hρ0 hρK
  exact ⟨(h.2.comp (continuous_const.sub continuous_id)).neg,
    (h.1.comp (continuous_const.sub continuous_id)).neg⟩

theorem IsJointCapMaximizer.properReflected_arm_bounds
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ r ∈ Icc (Real.pi / 2 - α) (properReflectedActiveEnd m),
      properReflectedP U m ρ r ≤ 1 ∧ -1 ≤ properReflectedQ U m ρ r := by
  have hab := (hU.properReflected_active_interval haffine).1
  have hcont := hU.properReflected_momenta_continuous (m := m) hρ hρ0 hρK
  have hinside : ∀ r ∈ Ioo (Real.pi / 2 - α) (properReflectedActiveEnd m),
      properReflectedP U m ρ r ≤ 1 ∧ -1 ≤ properReflectedQ U m ρ r := by
    intro r hr
    have hrt : max 0 (Real.arctan m) < Real.pi / 2 - r := by
      dsimp only [properReflectedActiveEnd] at hr
      linarith only [hr.2]
    have ht0 : 0 < Real.pi / 2 - r := (le_max_left _ _).trans_lt hrt
    have htα : Real.pi / 2 - r < α := by linarith only [hr.1]
    have hmt : Real.arctan m ≤ Real.pi / 2 - r := (le_max_right _ _).trans hrt.le
    have hmatch := hU.properUsed_momenta_eq_actual_after_affine
      hLargest hproper hheight haffine hρ hρ0 hρK heq ⟨ht0.le, htα⟩ hmt
    dsimp only [properReflectedP, properReflectedQ]
    rw [hmatch.1, hmatch.2, neg_neg]
    have hp := hU.isCap.firstCornerVelocity_ge_neg_one (Real.pi / 2 - r)
    have hq := hU.isCap.neg_secondCornerVelocity_le_one (Real.pi / 2 - r)
    constructor <;> linarith only [hp, hq]
  have hclosure : closure (Ioo (Real.pi / 2 - α) (properReflectedActiveEnd m)) =
      Icc (Real.pi / 2 - α) (properReflectedActiveEnd m) := closure_Ioo hab.ne
  intro r hr
  have hrcl := hclosure.symm ▸ hr
  exact ⟨le_on_closure (fun s hs => (hinside s hs).1)
      hcont.1.continuousOn continuousOn_const hrcl,
    le_on_closure (fun s hs => (hinside s hs).2)
      continuousOn_const hcont.2.continuousOn hrcl⟩

theorem IsJointCapMaximizer.properUsed_source_controls
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) α),
      ρ t ≤ sourceKappa (properUsedQ U m ρ t) ∧
      leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ sourceKappa (properUsedP U m ρ t) ∧
      (0 < properUsedP U m ρ t → 0 < properUsedQ U m ρ t →
        ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (properUsedP U m ρ t < 0 → properUsedQ U m ρ t < 0 →
        leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  have hinit := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.proper_wing_densities_zero_before_affine hproper hl hr hheight haffine hρ hρ0 heq)
  have hshadow := (ae_restrict_iff'
    (isOpen_regularProperCornerDomain α m).measurableSet).mp
      (hU.ae_proper_curvature_same_sign_quadrants hproper haffine hρ hρ0 hρK heq)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hinit,
    ae_restrict_of_ae hshadow, ae_restrict_of_ae (volume.ae_ne (Real.arctan m))]
    with t ht hz hs hne
  by_cases hpre : t < Real.arctan m
  · have hzero := hz ⟨ht.1, hpre⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hzero.1]
      exact sourceKappa_nonneg _
    · rw [hzero.2]
      exact sourceKappa_nonneg _
    · intro _ _
      exact ⟨hzero.1, by rw [hzero.2]; norm_num⟩
    · intro _ _
      exact ⟨hzero.2, by rw [hzero.1]; norm_num⟩
  · have hpost : Real.arctan m < t :=
      lt_of_le_of_ne (le_of_not_gt hpre) (Ne.symm hne)
    have hsource := hs (hU.mem_regularProperCornerDomain_after_affine
      hLargest hproper hheight haffine ht hpost)
    have hmatch := hU.properUsed_momenta_eq_actual_after_affine
      hLargest hproper hheight haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le
    have hveq := leftCompanionWingDensity_shift_eq_after (ρ := ρ) ht.1 hpost
    have hbounds := upperCorner_density_bounds_on_quarter hκ ⟨ht.1, ht.2.trans hproper⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmatch.2]
      exact hbounds.1
    · rw [hveq, hmatch.1, sourceKappa_neg]
      exact hbounds.2
    · intro hp hq
      rw [hmatch.1] at hp
      rw [hmatch.2] at hq
      have h := hsource.1 ⟨hq, by linarith only [hp]⟩
      exact ⟨h.1, by rw [hveq]; exact h.2⟩
    · intro hp hq
      rw [hmatch.1] at hp
      rw [hmatch.2] at hq
      have h := hsource.2 ⟨hq, by linarith only [hp]⟩
      exact ⟨by rw [hveq]; exact h.1, h.2⟩

theorem IsJointCapMaximizer.properReflected_source_controls
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      0 ≤ properReflectedFirstDensity m ρ r ∧
      0 ≤ properReflectedSecondDensity ρ r ∧
      properReflectedFirstDensity m ρ r ≤ sourceKappa (properReflectedQ U m ρ r) ∧
      properReflectedSecondDensity ρ r ≤ sourceKappa (properReflectedP U m ρ r) ∧
      (0 < properReflectedP U m ρ r → 0 < properReflectedQ U m ρ r →
        properReflectedFirstDensity m ρ r = 0 ∧ properReflectedSecondDensity ρ r ≤ 1 / 2) ∧
      (properReflectedP U m ρ r < 0 → properReflectedQ U m ρ r < 0 →
        properReflectedSecondDensity ρ r = 0 ∧ properReflectedFirstDensity m ρ r ≤ 1 / 2) := by
  have hused := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.properUsed_source_controls hLargest hproper hl hr hheight haffine hρ hρ0 hρK hκ heq)
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae hused
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with r hr hs
  have ht : Real.pi / 2 - r ∈ Ioo (0 : ℝ) α := by
    constructor <;> linarith only [hr.1, hr.2]
  obtain ⟨hu, hv, hpp, hmm⟩ := hs ht
  refine ⟨(leftCompanionWingDensity_bounds hρ0 hρK _).1, hρ0 _, ?_, ?_, ?_, ?_⟩
  · simpa only [properReflectedFirstDensity, properReflectedQ, sourceKappa_neg] using hv
  · simpa only [properReflectedSecondDensity, properReflectedP, sourceKappa_neg] using hu
  · intro hp hq
    dsimp only [properReflectedP, properReflectedQ] at hp hq
    exact hmm (by linarith only [hq]) (by linarith only [hp])
  · intro hp hq
    dsimp only [properReflectedP, properReflectedQ] at hp hq
    exact hpp (by linarith only [hq]) (by linarith only [hp])

theorem IsJointCapMaximizer.properReflected_densities_zero_after_active
    {U : Set Plane} {α C m c : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ r ∂volume.restrict (Ioo (properReflectedActiveEnd m) (Real.pi / 2)),
      properReflectedFirstDensity m ρ r = 0 ∧ properReflectedSecondDensity ρ r = 0 := by
  have hzero := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.proper_wing_densities_zero_before_affine hproper hl hr hheight haffine hρ hρ0 heq)
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae hzero
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with r hr hs
  have ht0 : 0 < Real.pi / 2 - r := by linarith only [hr.2]
  have htmax : Real.pi / 2 - r < max 0 (Real.arctan m) := by
    dsimp only [properReflectedActiveEnd] at hr
    linarith only [hr.1]
  have htm : Real.pi / 2 - r < Real.arctan m :=
    (lt_max_iff.mp htmax).resolve_left (not_lt_of_ge ht0.le)
  have h := hs ⟨ht0, htm⟩
  exact ⟨h.2, h.1⟩

end AmbidextrousSofa
