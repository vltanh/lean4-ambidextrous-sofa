module

public import AmbidextrousSofa.Analysis.FirstUnitBadEntry

@[expose] public section

/-!
# Choosing the actual first-unit events

The sign changes, the first middle crossing, and the first possible
companion excess are all chosen from the actual closed support pair.
Their ordering and the one-quarter excess height are conclusions. No
event time or source occupation is supplied to this selector.
-/

noncomputable section

open Set Filter MeasureTheory

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
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))
set_option quotPrecheck false in
local notation "B" => firstTangentPoint (F).f (F).fD

theorem fullTiltedSupportQuarterPair_exists_firstUnit_events {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 17 / 50) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∃ α β η, StrictCornerSignPhases p q (Real.pi / 2) α η ∧
      Real.arctan m < α ∧ α < β ∧ β ∈ Ioo (0 : ℝ) (Real.pi / 2) ∧
      (B β).1 = C ∧
      (∀ t ∈ Ico (0 : ℝ) β, (B t).1 < C) ∧
      (∀ t ∈ Icc β (Real.pi / 2), C ≤ (B t).1) ∧
      3 / 5 ≤ Real.sin β ∧ 0 ≤ (B β).2 ∧
      ((∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), v t ≤ 1) ∨
        ∃ τ ∈ Ioo β η, p τ = -1 ∧ 0 < q τ ∧ q τ ≤ 1 / 4 ∧
          (∀ t ∈ Ico α τ, -1 < p t) ∧
          (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) ∧
          (∀ t ∈ Icc α β, (p t - 1) ^ 2 + (q t + 1) ^ 2 ≤ 5) ∧
          (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
            1 < v t → q t ≤ 1 / 4)) := by
  obtain ⟨α, η, hphase⟩ := fullTiltedSupportQuarterPair_exists_strict_sign_phases
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hmpos hsmall hheight
    hlow hhigh hκ hunit
  have hαδ := fullTiltedSupportQuarterPair_first_phase_after_affine
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hmpos hsmall hheight
    hlow hhigh hκ hunit hphase
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have htop := hU.firstUnit_top_overhang_pos hl hr hC0 hC1 hh0 hh1 hheight haff
    hlow hhigh hρ hρ0 hρK heq hκ hunit
  obtain ⟨β, hβ, hβx, hbefore, hafter, _hβacos, hβsin, hβp, hβy⟩ :=
    fullTiltedSupportQuarterPair_exists_first_middle_crossing hU hm haffine hρ hρ0 hρK heq
      hl hr hC0 hC1 hh1.le hmpos hheight hlow (by linarith only [htop]) hunit
  have hαβ := hphase.first_lt_of_first_neg (Ioo_subset_Icc_self hβ) hβp
  refine ⟨α, β, η, hphase, hαδ, hαβ, hβ, hβx, hbefore, hafter, hβsin, hβy, ?_⟩
  rcases fullTiltedSupportQuarterPair_first_bad_crossing_or_unit
    hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hsmall hheight hhigh
    hκ hphase with hcompanion | ⟨τ, hτ, hpτ, hqτ0, hpfirst, hprefix⟩
  · exact Or.inl hcompanion
  · obtain ⟨_hαβ, hβτ, hqτ, henergy, hbad⟩ :=
      fullTiltedSupportQuarterPair_first_bad_after_middle
        hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh1.le hmpos hsmall hheight
        hlow hhigh hκ hunit hphase (Ioo_subset_Icc_self hβ) hβx hτ hpτ hpfirst hprefix
    exact Or.inr ⟨τ, ⟨hβτ, hτ.2⟩, hpτ, hqτ0, hqτ, hpfirst, hprefix, henergy, hbad⟩

end ActualPair

end AmbidextrousSofa
