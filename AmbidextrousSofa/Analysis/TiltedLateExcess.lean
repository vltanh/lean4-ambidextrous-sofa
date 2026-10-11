module

public import AmbidextrousSofa.Analysis.CornerArcCrossing
public import AmbidextrousSofa.Analysis.TiltedCrossingExcess
public import AmbidextrousSofa.Analysis.TiltedLeakageMoment

@[expose] public section

/-!
# Actual late unit curvature and first excess moment

The regular corner arc comes from the original support and its literal
low-wing cut. Its first excess interval is constructed by the source
ODE crossing theorem. The actual circle and endpoint bounds place its
quadratic endpoint before `11/15` and bound its length by `1/3`. These
give both the late unit-curvature statement and the strict `1/40`
sine-weighted excess bound. The final theorem selects its density from
the maximizing cap itself.
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

theorem fullTiltedSupportQuarterPair_cornerArcDynamics {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s)) :
    CornerArcDynamics p q ρ (fun t => leftCompanionWingDensity m ρ (t + Real.pi / 2))
      0 (Real.pi / 2) := by
  obtain ⟨hpAC, hqAC, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hcontrols := hU.fullTiltedSupportQuarterPair_source_controls
    hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 hρK hκ heq
  exact ⟨by positivity, hpAC, hqAC, hode, hcontrols.mono fun _ hs => ⟨hs.1, hs.2.1⟩,
    .of_forall fun t => (leftCompanionWingDensity_bounds hρ0 hρK (t + Real.pi / 2)).1,
    fun t ht => fullTiltedSupportQuarterPair_q_ge_neg_one hU hm haffine hρ hρ0 hρK heq ht,
    fullTiltedSupportQuarterPair_first_arm_or_zero_sources
      hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh,
    hcontrols.mono fun _ hs => hs.2.2.1⟩

include hU hm haffine hρ hρ0 hρK heq in
/-- The compact quadratic envelope uses the actual first momentum
zero and actual excess height, unless the whole first source is already
unit bounded. No crossing or energy premise remains in this theorem. -/
theorem fullTiltedSupportQuarterPair_exists_short_quadratic_excess_envelope {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s)) :
    ∃ A ell : ℝ, 0 ≤ A ∧ 0 ≤ ell ∧ ell < 1 / 3 ∧ A + ell < 11 / 15 ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        ρ t - 1 ≤ horizontalLeakageEnvelope A ell t := by
  have D := fullTiltedSupportQuarterPair_cornerArcDynamics
    hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hsmall hheight hhigh hκ
  obtain ⟨hp0, hq0, -, -⟩ := fullTiltedSupportQuarterPair_initial_values
    hU hm haffine hρ hρ0 hρK heq hl hr hmpos hlow
  obtain ⟨-, -, hfL, -, -, -, -, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  have heR := capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1)
    (horizontalRight U)
  have heL := capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1)
    (horizontalLeft U)
  have hqend : q (Real.pi / 2) ≤ 1 := by
    simp only [supportQ, hgDL, hfL, hheight]
    linarith only [heL]
  rcases D.exists_first_excess_crossings (by rw [hp0]; linarith only [heR, hh0])
    (by rw [hq0]; linarith only [hC0]) hqend with hunit | hcross
  · refine ⟨0, 0, le_rfl, le_rfl, by norm_num, by norm_num, ?_⟩
    filter_upwards [hunit] with t ht
    exact (sub_nonpos.mpr ht).trans (horizontalLeakageEnvelope_nonneg 0 0 t)
  · obtain ⟨A, B, hA, hB, hpA, _hqB, hqA, hpbefore, hqbefore, hquad, hout⟩ := hcross
    have hAL : A ∈ Ioo (0 : ℝ) (Real.pi / 2) := ⟨hA.1, hA.2.trans_le hB.2⟩
    have hquad' : 0 ≤ capRoof U (horizontalRight U) + h - 3 * C * A + A ^ 2 / 2 := by
      rw [hp0, hq0] at hquad
      linarith only [hquad]
    obtain ⟨_hε, hell, hend⟩ := fullTiltedSupportQuarterPair_first_zero_excess_stops_early
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hmpos hsmall hh0 hh1 hheight hhigh hlow hκ
      hAL hpA hpbefore hqA hquad'
    have henv := D.quadratic_excess_envelope_at_first_crossing
      hA.1.le hA.2 hB.2 hpA.le hqA.le
      (fun t ht => hqbefore t ⟨(hA.1.trans ht.1).le, ht.2⟩) hout
      (by linarith only [hell])
    exact ⟨A, Analysis.quadraticExcessLength (q A - 1), hA.1.le,
      Analysis.quadraticExcessLength_nonneg (by linarith only [hqA]), hell, hend, henv.2⟩

end ActualPair

/-- The slope sign, initial zero-source margin, density and every
late-excess input are derived from the actual centered tilted cap. -/
theorem IsFullCapMaximizer.exists_tilted_first_density_with_late_controls
    {U : Set Plane} (hU : IsFullCapMaximizer U) {C h m c : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50)
    (hh0 : 0 < h) (hh1 : h < 17 / 50) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hhigh : capRoof U C = 1) (hlow : capRoof U (-C) = 1 - h) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧
      (∀ t, 0 ≤ ρ t ∧ ρ t ≤ sourceKappa (upperCornerVelocity U t)) ∧
      (∀ t, ρ t ≤ 4 * (|horizontalLeft U| + |horizontalRight U| + 1) + 10) ∧
      (upperCurvature U).restrict (regularCurvatureDomain m) =
        (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)) ∧
      (∀ᵐ t ∂volume.restrict (Ioo (11 / 15 : ℝ) (Real.pi / 2)), ρ t ≤ 1) ∧
      firstExcessMoment ρ < 1 / 40 := by
  have hmid : middleHalfInterval (horizontalLeft U) (horizontalRight U) = Icc (-C) C := by
    rw [middleHalfInterval, hl, hr]
    congr 1 <;> ring
  have hleft := haffine (-C) (hmid ▸ ⟨le_rfl, by linarith only [hC0]⟩)
  have hright := haffine C (hmid ▸ ⟨by linarith only [hC0], le_rfl⟩)
  have hmEq : m = h / (2 * C) := by
    rw [eq_div_iff (by linarith only [hC0])]
    linarith only [hleft, hright, hlow, hhigh]
  have hmpos : 0 < m := hmEq ▸ div_pos hh0 (by linarith only [hC0])
  obtain ⟨ρ, hρ, hbounds, hcoarse, heq, _⟩ :=
    hU.curvature_density_corner_controls hheight haffine
  obtain ⟨A, ell, -, hell0, hell1, hend, henv⟩ :=
    fullTiltedSupportQuarterPair_exists_short_quadratic_excess_envelope hU hmpos.le haffine hρ
      (fun t => (hbounds t).1) hcoarse heq hl hr hC0 hC1 hmpos
      (hmEq ▸ canonical_width_add_slope_lt_one (by linarith only [hC0]) hC1.le hh1) hh0 hh1
      hheight hhigh hlow (fun t => (hbounds t).2)
  refine ⟨ρ, hρ, hbounds, hcoarse, heq, ?_, firstExcessMoment_lt_one_fortieth_of_short_envelope
    hρ (fun t => (hbounds t).1) hcoarse hell0 hell1.le hend.le henv⟩
  -- after `11/15` the envelope vanishes
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (by norm_num) le_rfl) henv] with t ht hbound
  rw [horizontalLeakageEnvelope,
    indicator_of_notMem fun hmem => by linarith only [hmem.2, ht.1, hend]] at hbound
  linarith only [hbound]

end AmbidextrousSofa
