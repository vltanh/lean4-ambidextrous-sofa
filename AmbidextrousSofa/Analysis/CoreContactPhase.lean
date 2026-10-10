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

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f

theorem fullTiltedSupportQuarterPair_contact_mem_closed_core_phase_of_after_affine
    {α η t g : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) : t ∈ Icc α η := by
  have hnot := fullTiltedSupportQuarterPair_not_same_sign_at_attachedCorner_contact_after_affine
    hU hm haffine hρ hρ0 hρK heq ht hmt hderiv hcontact
  constructor
  · by_contra hbefore
    exact hnot (Or.inl (hphase.initial_signs t ⟨ht.1.le, lt_of_not_ge hbefore⟩))
  · by_contra hafter
    exact hnot (Or.inr (hphase.final_signs t ⟨lt_of_not_ge hafter, ht.2.le⟩))

theorem fullTiltedSupportQuarterPair_contact_mem_core_phase_of_after_affine
    {α η t g : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hmt : Real.arctan m ≤ t)
    (htα : t ≠ α) (htη : t ≠ η)
    (hderiv : HasDerivAt (sweptNiche U (Real.pi / 2)) g (attachedCorner U t).1)
    (hcontact : sweptNiche U (Real.pi / 2) (attachedCorner U t).1 =
      (attachedCorner U t).2) : t ∈ Ioo α η := by
  have hclosed := fullTiltedSupportQuarterPair_contact_mem_closed_core_phase_of_after_affine
    hU hm haffine hρ hρ0 hρK heq hphase ht hmt hderiv hcontact
  exact ⟨lt_of_le_of_ne hclosed.1 htα.symm, lt_of_le_of_ne hclosed.2 htη⟩

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
  obtain ⟨hC0, _hC1, _hh0, _hh1, hsmall, _hlow, hhigh⟩ :=
    hU.centered_positive_tilt_parameters hl hr hheight hmpos haffine
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have hmt : Real.arctan m ≤ t := by
    by_contra hbefore
    have hneg := hU.isCap.attachedCorner_neg_before_positive_affine hl hr
      (show 0 < C by linarith only [hC0]) hsmall
      (by simpa only [hmid] using haffine) hhigh ⟨ht.1, lt_of_not_ge hbefore⟩
    exact (not_lt_of_ge hy.le) hneg
  exact ⟨hmt, fullTiltedSupportQuarterPair_contact_mem_closed_core_phase_of_after_affine
    hU hm haffine hρ hρ0 hρK heq hphase ht hmt hderiv hcontact⟩

theorem fullTiltedSupportQuarterPair_core_strictAntiOn_open {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    StrictAntiOn (fun t => (Z t).1) (Ioo α η) := by
  have hclosed := fullTiltedSupportQuarterPair_core_strictAntiOn
    hU hm haffine hρ hρ0 hρK heq hphase.first_mem.1.le hphase.second_mem.2.le
      hphase.core_signs
  intro s hs t ht hst
  exact hclosed (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) hst

end ActualPair

end AmbidextrousSofa
