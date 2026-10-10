import AmbidextrousSofa.Analysis.TiltedSupportPair
import AmbidextrousSofa.Analysis.NonpositiveCornerCurvature

/-!
# Actual source controls for the tilted support pair

Before the middle normal both wing densities vanish by actual source
occupation and the literal cut construction. After it the pair agrees
with the original corner, so the sharp arm bounds and same-sign source
laws transfer exactly. The single joining angle has zero Lebesgue mass.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem mem_regularCornerDomain_of_after_nonneg_affine {m t : ℝ}
    (hm : 0 ≤ m) (ht : t ∈ Ioo 0 (Real.pi / 2)) (hmt : Real.arctan m < t) :
    t ∈ regularCornerDomain m := by
  refine ⟨ht, firstQuarter_subset_regularCurvatureDomain_of_nonneg hm ht, ?_⟩
  apply regularCompanionDomain_subset_regularCurvatureDomain m
  refine ⟨⟨by linarith only [ht.1], by linarith only [ht.2]⟩, ?_⟩
  intro heq
  simp only [mem_singleton_iff] at heq
  unfold affineNormalAngle at heq
  linarith only [heq, hmt]

theorem leftCompanionWingDensity_shift_eq_after {m t : ℝ} {ρ : ℝ → ℝ}
    (ht0 : 0 < t) (hmt : Real.arctan m < t) :
    leftCompanionWingDensity m ρ (t + Real.pi / 2) = ρ (t + Real.pi / 2) := by
  apply leftCompanionWingDensity_eq
  apply max_lt
  · linarith only [ht0]
  · unfold affineNormalAngle
    linarith only [hmt]

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
  have hzero := hU.first_wing_curvature_zero_before_affine
    hl hr hC hm hsmall hheight haffine hhigh
  have hsub : Ioo (0 : ℝ) (Real.arctan m) ⊆ regularCurvatureDomain m := by
    intro t ht
    exact firstQuarter_subset_regularCurvatureDomain_of_nonneg hm
      ⟨ht.1, ht.2.trans (Real.arctan_lt_pi_div_two m)⟩
  have hfirst := ae_density_eq_zero_of_restrict_withDensity_null hρ hρ0 heq
    measurableSet_Ioo hsub hzero
  filter_upwards [hfirst, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  refine ⟨ht, leftCompanionWingDensity_eq_zero ?_⟩
  apply le_trans _ (le_max_right _ _)
  unfold affineNormalAngle
  linarith only [hmem.2]

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
    let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
    -1 ≤ supportQ F.gD F.f t := by
  let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
  have hp := (fullTiltedSupportQuarterPair_points_mem hU hm haffine hρ hρ0 hρK heq).2 t ht
  have hdot := coordDot_le_support hU.isCap.isCompact
    (leftCompanionCap_subset U (horizontalLeft U + capWidth U / 4) hp) (unitNormal t)
  change coordDot (Reference.companionSupportPoint F.g F.gD t) (unitNormal t) ≤ F.f t at hdot
  rw [companionSupportPoint_coordinates] at hdot
  dsimp only [coordDot, unitNormal] at hdot
  have hcircle := congrArg (fun z : ℝ => F.gD t * z) (Real.sin_sq_add_cos_sq t)
  dsimp only [supportQ]
  nlinarith only [hdot, hcircle]

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
    supportP F.fD F.g t ≤ 1 := by
  rw [(fullTiltedSupportQuarterPair_after_affine hU hm haffine hρ hρ0 hρK heq ht hmt).2.2.1]
  exact hU.isCap.neg_secondCornerVelocity_le_one t

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
  let F := fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
  have hinit := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.full_tilted_wing_densities_zero_before_affine hl hr hC hm hsmall
      hheight haffine hhigh hρ hρ0 heq)
  have hshadow := (ae_restrict_iff' (isOpen_regularCornerDomain m).measurableSet).mp
    (hU.ae_curvature_same_sign_quadrants haffine hρ hρ0 hρK heq)
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
    have hreg := mem_regularCornerDomain_of_after_nonneg_affine hm ht hpost
    have hsource := hs hreg
    have hmatch := fullTiltedSupportQuarterPair_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost.le
    have hveq := leftCompanionWingDensity_shift_eq_after (ρ := ρ) ht.1 hpost
    have hbounds := upperCorner_density_bounds_on_quarter hκ ht
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmatch.2.2.2]
      exact hbounds.1
    · rw [hveq, hmatch.2.2.1, sourceKappa_neg]
      exact hbounds.2
    · intro hp hq
      rw [hmatch.2.2.1] at hp
      rw [hmatch.2.2.2] at hq
      have h := hsource.1 ⟨hq, by linarith only [hp]⟩
      exact ⟨h.1, by rw [hveq]; exact h.2⟩
    · intro hp hq
      rw [hmatch.2.2.1] at hp
      rw [hmatch.2.2.2] at hq
      have h := hsource.2 ⟨hq, by linarith only [hp]⟩
      exact ⟨by rw [hveq]; exact h.1, h.2⟩

end AmbidextrousSofa
