module

public import AmbidextrousSofa.Analysis.FirstUnitCrossings
public import AmbidextrousSofa.Analysis.FirstUnitTopOverhang
public import AmbidextrousSofa.Analysis.TiltedLateExcess

@[expose] public section

/-!
# The actual first-unit tilted corner phases

All crossing data below are constructed from the literal support pair.
The original sharp source bounds, the surrogate's short initial arm
exception, positive endpoint pressures, and exact top projection supply
the hypotheses of the absolutely continuous crossing argument.
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

set_option quotPrecheck false
local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
local notation "p" => supportP (F).fD (F).g
local notation "q" => supportQ (F).gD (F).f
local notation "v" => (fun t : ℝ => leftCompanionWingDensity m ρ (t + Real.pi / 2))

theorem fullTiltedSupportQuarterPair_exists_strict_sign_phases {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 17 / 50) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∃ α η, StrictCornerSignPhases p q (Real.pi / 2) α η := by
  have hC : 0 < C := by linarith only [hC0]
  have D := fullTiltedSupportQuarterPair_cornerArcDynamics
    hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh hκ
  obtain ⟨hp0, hq0, -, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  obtain ⟨-, -, -, -, hpL, hqL⟩ := fullTiltedSupportQuarterPair_tangent_traces
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  have htop := hU.firstUnit_top_overhang_pos hl hr hC0 hC1 hh0 hh1 hheight
    (fun x hx => haffine x (by
      rw [middleHalfInterval, hl, hr]; constructor <;> linarith only [hx.1, hx.2]))
    hlow hhigh hρ hρ0 hρK heq hκ hunit
  have he := hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩
  have hδ0 : 0 ≤ Real.arctan m := Real.arctan_nonneg.mpr hm
  refine D.exists_strict_sign_phases (by positivity) hδ0
    (by rw [hq0]; linarith only [Real.arctan_le_self hm, hsmall, hC0])
    (ContinuousOn.le_on_Icc_of_ae_le_on_Ioo (D.continuousOn.1.mono (Icc_subset_Icc hδ0 le_rfl))
      (Real.arctan_lt_pi_div_two m) ?_)
    (by rw [hp0]; linarith only [he.1, hh0]) (by rw [hpL]; linarith only [htop, hC0])
    (by rw [hqL]; linarith only [he.2]) (by rw [hq0]; nlinarith only [hC0, sq_nonneg (p 0 - 1)])
    ((hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight haffine hhigh
      hρ hρ0 hρK hκ heq).mono fun _ hs => hs.2.2.2)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact fullTiltedSupportQuarterPair_p_le_one_after_affine
    hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1.le, ht.2⟩ ht.1.le

theorem fullTiltedSupportQuarterPair_first_bad_crossing_or_unit {C α η : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), v t ≤ 1) ∨
      ∃ τ ∈ Ioo α η, p τ = -1 ∧ 0 < q τ ∧
        (∀ t ∈ Ico α τ, -1 < p t) ∧
        (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) :=
  (fullTiltedSupportQuarterPair_cornerArcDynamics hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall
    hheight hhigh hκ).first_bad_crossing_or_unit hphase
    ((hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight haffine hhigh
      hρ hρ0 hρK hκ heq).mono fun _ hs => hs.2.2.2)

/-- The literal zero-source circle stays strictly in the first positive
sector through the middle normal: the dry endpoint pressure supplies a
uniformly positive lower bound for its first momentum there. -/
theorem fullTiltedSupportQuarterPair_first_phase_after_affine {C h α η : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 17 / 50) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    Real.arctan m < α := by
  by_contra hnot
  have hα : α ∈ Icc 0 (Real.arctan m) := ⟨hphase.first_mem.1.le, not_lt.mp hnot⟩
  have hC : 0 < C := by linarith only [hC0]
  have haff : ∀ x ∈ Icc (-C) C, capRoof U x = m * x + c := fun x hx =>
    haffine x (by rw [middleHalfInterval, hl, hr]; constructor <;> linarith only [hx.1, hx.2])
  have hEP := (hU.tilted_endpoint_laws hl hr hheight haff hlow hhigh).1
  have hdry := (hU.firstUnit_dry_left_and_overhang_bounds
    hl hr hC0 hC1 hh0 hh1 hheight haff hlow hhigh hρ hρ0 hρK heq hκ hunit).2.1
  have heRone : capRoof U (horizontalRight U) ≤ 1 :=
    (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact
      (horizontalRight_mem hU.isCap.nonempty hU.isCap.isCompact))).2
  have hcm : 3 * C * m = 3 * h / 2 := by
    linarith only [haff (-C) ⟨le_rfl, by linarith only [hC]⟩,
      haff C ⟨by linarith only [hC], le_rfl⟩, hlow, hhigh]
  have hδ0 : 0 ≤ Real.arctan m := Real.arctan_nonneg.mpr hm
  have hδL : Real.arctan m ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two m).le
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hodeZero : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (Real.arctan m)),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (p t - 1) t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hδL) hode,
      hU.full_tilted_wing_densities_zero_before_affine
        hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 heq] with t hd hz
    exact ⟨hd.1.congr_deriv (by rw [hz.1]; ring), hd.2.congr_deriv (by rw [hz.2]; ring)⟩
  obtain ⟨hp0, hq0, -, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  have hsub := uIcc_subset_uIcc (left_mem_uIcc (a := (0 : ℝ)) (b := Real.pi / 2))
    (mem_uIcc_of_le hδ0 hδL)
  have hpα := (Analysis.eqOn_initialFloorCircle_of_zero_source hδ0
    (hpAC.mono hsub) (hqAC.mono hsub) hodeZero
    (show p 0 = 1 + (capRoof U (horizontalRight U) - 1 + h) by linarith only [hp0]) hq0).1 hα
  rw [hphase.first_zero, Analysis.initialFloorCircleP] at hpα
  have hsin := mul_le_mul_of_nonneg_left (show Real.sin α ≤ m * Real.cos α by
    linarith only [tilted_initial_coefficient_nonneg hα.1 hα.2]) (show 0 ≤ 3 * C by linarith)
  rw [← mul_assoc, hcm] at hsin
  nlinarith only [hpα, hsin, hEP, hdry, hh1, sweptNiche_nonneg U (Real.pi / 2) C,
    mul_nonneg (sub_nonneg.mpr (Real.cos_le_one α))
      (show 0 ≤ 1 - capRoof U (horizontalRight U) + h / 2 by linarith only [heRone, hh0])]

end ActualPair

end AmbidextrousSofa
