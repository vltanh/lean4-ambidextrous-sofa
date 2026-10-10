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

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
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
  obtain ⟨hp0, hq0, _hD0, _hDL⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  obtain ⟨_hB0, _hBL, _hD0, _hDL, hpL, hqL⟩ :=
    fullTiltedSupportQuarterPair_tangent_traces
      hU hm haffine hρ hρ0 hρK heq hl hr hmpos hheight hlow
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have htop := hU.firstUnit_top_overhang_pos
    hl hr hC0 hC1 hh0 hh1 hheight haff hlow hhigh hρ hρ0 hρK heq hκ hunit
  have he := hU.endpoint_heights_pos_of_affine hheight ⟨m, c, haffine⟩
  have hδ0 : 0 ≤ Real.arctan m := Real.arctan_nonneg.mpr hm
  have hδL : Real.arctan m < Real.pi / 2 := Real.arctan_lt_pi_div_two m
  have hpcont : ContinuousOn p (Icc (Real.arctan m) (Real.pi / 2)) :=
    D.continuousOn.1.mono (Icc_subset_Icc hδ0 le_rfl)
  have hfirst : ∀ t ∈ Icc (Real.arctan m) (Real.pi / 2), p t ≤ 1 :=
    ContinuousOn.le_on_Icc_of_ae_le_on_Ioo hpcont hδL (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact fullTiltedSupportQuarterPair_p_le_one_after_affine
        hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1.le, ht.2⟩ ht.1.le)
  have hqδ : Real.arctan m < q 0 := by
    rw [hq0]
    have hδm := Real.arctan_le_self hm
    linarith only [hδm, hsmall, hC0]
  have hstart : 0 < p 0 := by rw [hp0]; linarith only [he.1, hh0]
  have hend : p (Real.pi / 2) < 0 := by
    rw [hpL]
    linarith only [htop, hC0]
  have hqend : q (Real.pi / 2) < 0 := by rw [hqL]; linarith only [he.2]
  have henergy : 2 < (p 0 - 1) ^ 2 + (q 0 + 1) ^ 2 := by
    rw [hq0]
    have hprod := mul_pos (show 0 < 3 * C - 3 / 2 by linarith only [hC0])
      (show 0 < 3 * C + 3 / 2 by linarith only [hC0])
    nlinarith only [hprod, sq_nonneg (p 0 - 1)]
  have hsource := hU.fullTiltedSupportQuarterPair_source_controls
    hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 hρK hκ heq
  exact D.exists_strict_sign_phases (by positivity) hδ0 hqδ hfirst hstart hend hqend henergy
    (hsource.mono (fun _ hs => hs.2.2.2))

theorem fullTiltedSupportQuarterPair_first_bad_crossing_or_unit {C α η : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), v t ≤ 1) ∨
      ∃ τ ∈ Ioo α η, p τ = -1 ∧ 0 < q τ ∧
        (∀ t ∈ Ico α τ, -1 < p t) ∧
        (∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) τ), v t ≤ 1) := by
  have D := fullTiltedSupportQuarterPair_cornerArcDynamics
    hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh hκ
  have hsource := hU.fullTiltedSupportQuarterPair_source_controls
    hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 hρK hκ heq
  exact D.first_bad_crossing_or_unit hphase (hsource.mono (fun _ hs => hs.2.2.2))

/-- The literal zero-source circle stays strictly in the first positive
sector through the middle normal. The dry endpoint pressure supplies a
uniformly positive lower bound for its first momentum. -/
theorem fullTiltedSupportQuarterPair_first_pos_through_affine {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 1 / 2 < C) (hC1 : C ≤ 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 17 / 50) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hlow : capRoof U (-C) = 1 - h)
    (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∀ t ∈ Icc (0 : ℝ) (Real.arctan m), 0 < p t := by
  have hC : 0 < C := by linarith only [hC0]
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have haff := haffine
  rw [hmid] at haff
  have hdry := (hU.firstUnit_dry_left_and_overhang_bounds
    hl hr hC0 hC1 hh0 hh1 hheight haff hlow hhigh hρ hρ0 hρK heq hκ hunit).2.1
  have hEP := (hU.tilted_endpoint_laws hl hr hheight haff hlow hhigh).1
  rw [hdry] at hEP
  have heRhalf : 1 / 2 ≤ capRoof U (horizontalRight U) := by
    linarith only [hEP, hh0, sweptNiche_nonneg U (Real.pi / 2) C]
  have heRone : capRoof U (horizontalRight U) ≤ 1 :=
    (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact
      (horizontalRight_mem hU.isCap.nonempty hU.isCap.isCompact))).2
  have hleft := haff (-C) ⟨le_rfl, by linarith only [hC]⟩
  have hright := haff C ⟨by linarith only [hC], le_rfl⟩
  rw [hlow] at hleft
  rw [hhigh] at hright
  have hcm : 3 * C * m = 3 * h / 2 := by nlinarith only [hleft, hright]
  have hδ0 : 0 ≤ Real.arctan m := Real.arctan_nonneg.mpr hm
  have hδL : Real.arctan m ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two m).le
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hzero := hU.full_tilted_wing_densities_zero_before_affine
    hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 heq
  have hodeZero : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (Real.arctan m)),
      HasDerivAt p (-1 - q t) t ∧ HasDerivAt q (p t - 1) t := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo le_rfl hδL) hode, hzero] with t hd hz
    exact ⟨hd.1.congr_deriv (by rw [hz.1]; ring),
      hd.2.congr_deriv (by rw [hz.2]; ring)⟩
  obtain ⟨hp0, hq0, _hD0, _hDL⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  have hsubcc : uIcc (0 : ℝ) (Real.arctan m) ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le hδ0, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact Icc_subset_Icc le_rfl hδL
  have hcircle := Analysis.eqOn_initialFloorCircle_of_zero_source hδ0
    (hpAC.mono hsubcc) (hqAC.mono hsubcc) hodeZero
    (show p 0 = 1 + (capRoof U (horizontalRight U) - 1 + h) by linarith only [hp0]) hq0
  intro t ht
  have hcoef := tilted_initial_coefficient_nonneg ht.1 ht.2
  have hsin := mul_le_mul_of_nonneg_left
    (show Real.sin t ≤ m * Real.cos t by linarith only [hcoef])
    (show 0 ≤ 3 * C by linarith only [hC])
  rw [← mul_assoc, hcm] at hsin
  have hprod := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one t))
    (show 0 ≤ 1 - capRoof U (horizontalRight U) + h / 2 by linarith only [heRone, hh0])
  have hpvalue := hcircle.1 ht
  dsimp only [Analysis.initialFloorCircleP] at hpvalue
  have hplower : capRoof U (horizontalRight U) - h / 2 ≤ p t := by
    nlinarith only [hpvalue, hsin, hprod]
  linarith only [hplower, heRhalf, hh1]

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
  have hp := fullTiltedSupportQuarterPair_first_pos_through_affine
    hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hh0 hh1 hmpos hsmall hheight
    hlow hhigh hκ hunit α ⟨hphase.first_mem.1.le, le_of_not_gt hnot⟩
  rw [hphase.first_zero] at hp
  exact lt_irrefl 0 hp

end ActualPair

end AmbidextrousSofa
