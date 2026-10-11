module

public import AmbidextrousSofa.Analysis.TiltedSupportPair
public import AmbidextrousSofa.Analysis.NonpositiveCornerCurvature

@[expose] public section

/-!
# Actual source controls for the tilted support pair

Before the middle normal the original corner lies below the floor, so
both wing densities vanish by actual source occupation and the literal
cut construction. After it the pair agrees with the original corner, so
the sharp arm bounds and same-sign source laws transfer exactly. The
single joining angle has zero Lebesgue mass.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem mem_regularCornerDomain_of_after_nonneg_affine {m t : ℝ}
    (hm : 0 ≤ m) (ht : t ∈ Ioo 0 (Real.pi / 2)) (hmt : Real.arctan m < t) :
    t ∈ regularCornerDomain m :=
  ⟨ht, firstQuarter_subset_regularCurvatureDomain_of_nonneg hm ht,
    regularCompanionDomain_subset_regularCurvatureDomain m
      ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, fun h => by
        simp only [mem_singleton_iff, affineNormalAngle] at h; linarith⟩⟩

theorem leftCompanionWingDensity_shift_eq_after {m t : ℝ} {ρ : ℝ → ℝ}
    (ht0 : 0 < t) (hmt : Real.arctan m < t) :
    leftCompanionWingDensity m ρ (t + Real.pi / 2) = ρ (t + Real.pi / 2) :=
  leftCompanionWingDensity_eq (max_lt (by linarith) (by unfold affineNormalAngle; linarith))

/-- The zero interval concerns the original first source and the
actual cut companion source, not a formally assigned continuation. -/
theorem IsFullCapMaximizer.full_tilted_wing_densities_zero_before_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ} {ρ : ℝ → ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hm : 0 ≤ m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) (hhigh : capRoof U C = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.arctan m)),
      ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 := by
  -- Before the middle normal the original corner lies below the floor.
  have hzero : upperCurvature U (Ioo (0 : ℝ) (Real.arctan m)) = 0 := by
    refine measure_mono_null (fun t ht => ?_)
      (hU.upperCurvature_negative_corners_eq_zero hheight haffine)
    have htL := ht.2.trans (Real.arctan_lt_pi_div_two m)
    refine ⟨firstQuarter_subset_regularCurvatureDomain_of_nonneg hm ⟨ht.1, htL⟩, ?_⟩
    rw [sourceCornerHeight, sourceQuarterAngle, ite_eq_left htL]
    exact hU.isCap.attachedCorner_neg_before_positive_affine hl hr hC hsmall
      ((centered_quarter_points hl hr).2.2 ▸ haffine) hhigh ht
  filter_upwards [ae_density_eq_zero_of_restrict_withDensity_null hρ hρ0 heq measurableSet_Ioo
    (fun t ht => firstQuarter_subset_regularCurvatureDomain_of_nonneg hm
      ⟨ht.1, ht.2.trans (Real.arctan_lt_pi_div_two m)⟩) hzero,
    ae_restrict_mem measurableSet_Ioo] with t ht hmem
  exact ⟨ht, leftCompanionWingDensity_eq_zero
    (le_max_of_le_right (by unfold affineNormalAngle; linarith [hmem.2]))⟩

/-- The companion supporting point belongs to the original cap. This
direct geometric inclusion gives the lower momentum bound throughout
the closed quarter, including both actual endpoint traces. -/
theorem fullTiltedSupportQuarterPair_q_ge_neg_one
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    {m c : ℝ} {ρ : ℝ → ℝ} {K t : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Icc 0 (Real.pi / 2)) :
    let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq;
    -1 ≤ supportQ F.gD F.f t := by
  intro F
  have hdot := coordDot_le_support hU.isCap.isCompact (leftCompanionCap_subset U _
    ((fullTiltedSupportQuarterPair_points_mem hU hm haffine hρ hρ0 hρK heq).2 t ht)) (unitNormal t)
  change coordDot (Reference.companionSupportPoint F.g F.gD t) (unitNormal t) ≤ F.f t at hdot
  simp only [companionSupportPoint_coordinates, coordDot, unitNormal] at hdot
  simp only [supportQ]
  nlinarith [congrArg (F.gD t * ·) (Real.sin_sq_add_cos_sq t)]

theorem fullTiltedSupportQuarterPair_p_le_one_after_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U)
    {m c : ℝ} {ρ : ℝ → ℝ} {K t : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s)))
    (ht : t ∈ Ico 0 (Real.pi / 2)) (hmt : Real.arctan m ≤ t) :
    let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
    supportP F.fD F.g t ≤ 1 :=
  (fullTiltedSupportQuarterPair_after_affine hU hm haffine hρ hρ0 hρK heq ht hmt).2.2.1.trans_le
    (hU.isCap.neg_secondCornerVelocity_le_one t)

/-- Sharp bounds and both same-sign laws for the literal tilted pair.
The only changes of representation occur on its already-proved zero
initial interval and at a single null joining angle. -/
theorem IsFullCapMaximizer.fullTiltedSupportQuarterPair_source_controls
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hm : 0 ≤ m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) (hhigh : capRoof U C = 1)
    (hρ : Measurable ρ) (hρ0 : ∀ s, 0 ≤ ρ s) (hρK : ∀ s, ρ s ≤ K)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun s => ENNReal.ofReal (ρ s))) :
    let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      ρ t ≤ sourceKappa (supportQ F.gD F.f t) ∧
      leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ sourceKappa (supportP F.fD F.g t) ∧
      (0 < supportP F.fD F.g t → 0 < supportQ F.gD F.f t →
        ρ t = 0 ∧ leftCompanionWingDensity m ρ (t + Real.pi / 2) ≤ 1 / 2) ∧
      (supportP F.fD F.g t < 0 → supportQ F.gD F.f t < 0 →
        leftCompanionWingDensity m ρ (t + Real.pi / 2) = 0 ∧ ρ t ≤ 1 / 2) := by
  have hinit := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.full_tilted_wing_densities_zero_before_affine hl hr hC hm hsmall
      hheight haffine hhigh hρ hρ0 heq)
  have hshadow := (ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mp
    (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρK heq)
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hinit,
    ae_restrict_of_ae hshadow, ae_restrict_of_ae (volume.ae_ne (Real.arctan m))]
    with t ht hz hs hne
  rcases hne.lt_or_gt with hpre | hpost
  · obtain ⟨h1, h2⟩ := hz ⟨ht.1, hpre⟩
    rw [h1, h2]
    exact ⟨sourceKappa_nonneg _, sourceKappa_nonneg _, fun _ _ => ⟨rfl, by norm_num⟩,
      fun _ _ => ⟨rfl, by norm_num⟩⟩
  · have hsource := hs (mem_regularCornerDomain_of_after_nonneg_affine hm ht hpost)
    obtain ⟨-, -, hP, hQ⟩ := fullTiltedSupportQuarterPair_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le
    rw [leftCompanionWingDensity_shift_eq_after ht.1 hpost, hP, hQ, sourceKappa_neg]
    exact ⟨(upperCorner_density_bounds_on_quarter hκ ht).1,
      (upperCorner_density_bounds_on_quarter hκ ht).2, fun hp hq => hsource.1 ⟨hq, by linarith⟩,
      fun hp hq => hsource.2 ⟨hq, by linarith⟩⟩

end AmbidextrousSofa
