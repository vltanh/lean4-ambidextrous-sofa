module

public import AmbidextrousSofa.Analysis.ContactSlopeBounds
public import AmbidextrousSofa.Analysis.FirstUnitPhases
public import AmbidextrousSofa.Analysis.CanonicalTiltParameters

@[expose] public section

/-!
# The actual core contact phase and its strict horizontal order

A differentiable original-corner contact after the affine normal cannot
lie in either equal-sign phase. Thus its angle lies in the closed core
phase, and avoiding the two endpoint angles places it in the open
phase. Positive original contacts also supply their own after-affine
condition from the actual canonical geometry. On the core phase, the
literal corner coordinate is strictly decreasing, giving the injective
spatial parameter needed for the common source measure.
-/

open Set MeasureTheory

namespace AmbidextrousSofa

private theorem mem_Icc_of_not_same_sign {P Q : ℝ → ℝ} {α η t : ℝ}
    (hphase : StrictCornerSignPhases P Q (Real.pi / 2) α η) (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hnot : ¬ ((0 < P t ∧ 0 < Q t) ∨ (P t < 0 ∧ Q t < 0))) : t ∈ Icc α η :=
  ⟨le_of_not_gt fun h => hnot (.inl (hphase.initial_signs t ⟨ht.1.le, h⟩)),
    le_of_not_gt fun h => hnot (.inr (hphase.final_signs t ⟨h, ht.2.le⟩))⟩

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_contact_mem_core_phase_of_after_affine
    {α η t g : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (htα : t ≠ α) (htη : t ≠ η)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) : t ∈ Ioo α η := by
  have h := mem_Icc_of_not_same_sign hphase ht
    (fullTiltedSupportQuarterPair_not_same_sign_at_attachedCorner_contact_after_affine
      hU hm haffine hρ hρ0 hρK heq ht hmt hderiv hcontact)
  exact ⟨h.1.lt_of_ne htα.symm, h.2.lt_of_ne htη⟩

/-- Every numerical condition in the pre-normal corner exclusion is
derived from this same canonical full maximum. -/
theorem fullTiltedSupportQuarterPair_positive_attachedCorner_contact_mem_closed_core_phase
    {C α η t g : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1) (hmpos : 0 < m)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hy : 0 < (attachedCorner U t).2)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) : Real.arctan m ≤ t ∧ t ∈ Icc α η := by
  obtain ⟨hC0, -, -, -, hsmall, -, hhigh⟩ :=
    hU.centered_positive_tilt_parameters hl hr hheight hmpos haffine
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]; congr 1 <;> ring
  have hmt : Real.arctan m ≤ t := le_of_not_gt fun h => hy.not_gt
    (hU.isCap.attachedCorner_neg_before_positive_affine hl hr (by linarith) hsmall
      (hmid ▸ haffine) hhigh ⟨ht.1, h⟩)
  exact ⟨hmt, mem_Icc_of_not_same_sign hphase ht
    (fullTiltedSupportQuarterPair_not_same_sign_at_attachedCorner_contact_after_affine
      hU hm haffine hρ hρ0 hρK heq ht hmt hderiv hcontact)⟩

theorem fullTiltedSupportQuarterPair_core_strictAntiOn_open {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    StrictAntiOn (fun t => (innerCornerPoint (F).f (F).g t).1) (Ioo α η) :=
  (fullTiltedSupportQuarterPair_core_strictAntiOn hU hm haffine hρ hρ0 hρK heq
    hphase.first_mem.1.le hphase.second_mem.2.le hphase.core_signs).mono Ioo_subset_Icc_self

end ActualPair

end AmbidextrousSofa
