module

public import AmbidextrousSofa.Analysis.CornerArcCrossing
public import AmbidextrousSofa.Analysis.TiltedCrossingExcess
public import AmbidextrousSofa.Analysis.TiltedLeakageMoment

@[expose] public section

/-!
# Actual first-wing unit curvature and first excess moment

The regular corner arc comes from the original support and its literal
low-wing cut; before the middle normal its first arm bound is replaced
by the vanishing of both sources. Its energy barrier turns the
initial-floor conditions at the stopped initial circle into unit
curvature on the whole first quarter. Otherwise the first excess
interval is constructed by the source ODE crossing theorem. The actual
circle and endpoint bounds place its quadratic endpoint before `11/15`
and bound its length by `1/3`. These give both the late unit-curvature
statement and the strict `1/40` sine-weighted excess bound.
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
  have hinit := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.full_tilted_wing_densities_zero_before_affine hl hr hC hm hsmall
      hheight haffine hhigh hρ hρ0 heq)
  refine ⟨by positivity, hpAC, hqAC, hode, hcontrols.mono fun _ hs => ⟨hs.1, hs.2.1⟩,
    .of_forall fun t => (leftCompanionWingDensity_bounds hρ0 hρK (t + Real.pi / 2)).1,
    fun t ht => fullTiltedSupportQuarterPair_q_ge_neg_one hU hm haffine hρ hρ0 hρK heq ht, ?_,
    hcontrols.mono fun _ hs => hs.2.2.1⟩
  -- Before the middle normal both sources vanish; after it the first arm bound holds.
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hinit] with t ht hz
  rcases le_or_gt (Real.arctan m) t with hpost | hpost
  · exact .inl (fullTiltedSupportQuarterPair_p_le_one_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨ht.1.le, ht.2⟩ hpost)
  · exact .inr (hz ⟨ht.1, hpost⟩)

include hU hm haffine hρ hρ0 hρK heq in
/-- The initial-floor scalar conditions imply unit curvature of the actual original first
quarter. Every stopping, source and energy propagation hypothesis is discharged from the cap
inside this proof. -/
theorem fullTiltedSupportQuarterPair_ae_first_le_one_of_initial_floor_conditions {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 1 / 2 < C) (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh : 0 < h) (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s))
    (hconditions : Analysis.InitialFloorEnergyConditions (3 * C)
      (capRoof U (horizontalRight U) - 1 + h) h) :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)), ρ t ≤ 1 := by
  obtain ⟨τ, hτ, -, hzero, hpcircle, hqcircle, hstop⟩ :=
    fullTiltedSupportQuarterPair_exists_initial_stopping_circle
      hU hm haffine hρ hρ0 hρK heq hl hr hC hmpos hsmall hh hheight hhigh hlow hκ
  have hτmem : τ ∈ Icc (0 : ℝ) τ := ⟨hτ.1.le, le_rfl⟩
  have henergy := Analysis.initialFloor_stopped_energy_le hh.le
    (by linarith [capRoof_nonneg hU.isCap.isCompact (fun x hx => (hU.isCap.inStrip hx).1) (-C)])
    hconditions (hstop.imp_left (hpcircle hτmem).symm.trans)
  rw [← hpcircle hτmem, ← hqcircle hτmem] at henergy
  -- After the stopping angle the energy stays at most `17/4`.
  have hfuture := ((fullTiltedSupportQuarterPair_cornerArcDynamics hU hm haffine hρ hρ0 hρK heq
    hl hr (by linarith only [hC]) hsmall hheight hhigh hκ).restrict hτ.1.le hτ.2.le le_rfl
    ).ae_unit_of_initial_energy ((clippedCornerEnergy_le_initialFloorEnergy p q τ).trans henergy)
  have hz := (ae_restrict_iff' measurableSet_Ioo).mp hzero
  have hf := (ae_restrict_iff' measurableSet_Ioo).mp hfuture
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hz,
    ae_restrict_of_ae hf, ae_restrict_of_ae (volume.ae_ne τ)] with t ht hz hf hne
  rcases lt_or_gt_of_ne hne with hpre | hpost
  · exact (hz ⟨ht.1, hpre⟩).1.trans_le zero_le_one
  · exact hf ⟨hpost, ht.2⟩

include hU hm haffine hρ hρ0 hρK heq in
/-- The compact quadratic envelope uses the actual first momentum zero and actual excess height,
unless the whole first source is already unit bounded. It gives unit curvature after `11/15` and
the strict `1/40` excess moment bound. No crossing or energy premise remains in this theorem. -/
theorem fullTiltedSupportQuarterPair_late_unit_and_excess_moment {C h : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC0 : 2 / 3 < C) (hC1 : C < 37 / 50)
    (hmpos : 0 < m) (hsmall : C + m < 1)
    (hh0 : 0 < h) (hh1 : h < 17 / 50)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hlow : capRoof U (-C) = 1 - h)
    (hκ : ∀ s, ρ s ≤ sourceKappa (upperCornerVelocity U s)) :
    (∀ᵐ t ∂volume.restrict (Ioo (11 / 15 : ℝ) (Real.pi / 2)), ρ t ≤ 1) ∧
      firstExcessMoment ρ < 1 / 40 := by
  have D := fullTiltedSupportQuarterPair_cornerArcDynamics
    hU hm haffine hρ hρ0 hρK heq hl hr (by linarith only [hC0]) hsmall hheight hhigh hκ
  obtain ⟨A, ell, hell0, hell1, hend, henv⟩ : ∃ A ell : ℝ, 0 ≤ ell ∧ ell < 1 / 3 ∧
      A + ell < 11 / 15 ∧ ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        ρ t - 1 ≤ horizontalLeakageEnvelope A ell t := by
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
    · refine ⟨0, 0, le_rfl, by norm_num, by norm_num, ?_⟩
      filter_upwards [hunit] with t ht
      exact (sub_nonpos.mpr ht).trans (horizontalLeakageEnvelope_nonneg 0 0 t)
    obtain ⟨A, B, hA, hB, hpA, -, hqA, hpbefore, hqbefore, hquad, hout⟩ := hcross
    rw [hp0, hq0] at hquad
    obtain ⟨-, hell, hend⟩ := fullTiltedSupportQuarterPair_first_zero_excess_stops_early
      hU hm haffine hρ hρ0 hρK heq hl hr hC0 hC1 hmpos hsmall hh0 hh1 hheight hhigh hlow hκ
      (fun a ha t ht => (D.restrict ha.1 ha.2 le_rfl).energy_le_max_initial ht)
      ⟨hA.1, hA.2.trans_le hB.2⟩ hpA hpbefore hqA (by linarith only [hquad])
    exact ⟨A, _, Analysis.quadraticExcessLength_nonneg (by linarith only [hqA]), hell, hend,
      (D.quadratic_excess_envelope_at_first_crossing hA.1.le hA.2 hB.2 hpA.le hqA.le
        (fun t ht => hqbefore t ⟨(hA.1.trans ht.1).le, ht.2⟩) hout (by linarith only [hell])).2⟩
  refine ⟨?_, firstExcessMoment_lt_one_fortieth_of_short_envelope hρ hρ0 hρK hell0 hell1.le
    hend.le henv⟩
  -- after `11/15` the envelope vanishes
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (by norm_num) le_rfl) henv] with t ht hbound
  rw [horizontalLeakageEnvelope,
    indicator_of_notMem fun hmem => by linarith only [hmem.2, ht.1, hend]] at hbound
  linarith only [hbound]

end ActualPair

end AmbidextrousSofa
