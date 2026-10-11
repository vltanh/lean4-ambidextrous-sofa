module

public import AmbidextrousSofa.Analysis.TiltedSupportControls
public import AmbidextrousSofa.Analysis.SupportArcCalculus
public import AmbidextrousSofa.Analysis.CornerArcCrossing

@[expose] public section

/-!
# The actual reflected active arc of a full tilted maximum

Reflection changes the parameter and exchanges the two actual support
momenta. The active arc stops at the middle normal. On that closed arc
both arm bounds hold; beyond it the two literal wing densities vanish.
The right endpoint of the original top face remains in the reflected
initial data, so a collapsed overhang gives the exact span `3C`.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

def reflectedSupportP (F : Analysis.QuarterPair) (r : ℝ) : ℝ :=
  -supportQ F.gD F.f (Real.pi / 2 - r)

def reflectedSupportQ (F : Analysis.QuarterPair) (r : ℝ) : ℝ :=
  -supportP F.fD F.g (Real.pi / 2 - r)

def reflectedFirstWingDensity (m : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  leftCompanionWingDensity m ρ (Real.pi / 2 - r + Real.pi / 2)

def reflectedSecondWingDensity (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ρ (Real.pi / 2 - r)

def fullReflectedActiveEnd (m : ℝ) : ℝ := Real.pi / 2 - Real.arctan m

theorem fullReflectedActiveEnd_bounds {m : ℝ} (hm : 0 ≤ m) :
    0 < fullReflectedActiveEnd m ∧ fullReflectedActiveEnd m ≤ Real.pi / 2 :=
  ⟨sub_pos.2 (Real.arctan_lt_pi_div_two m), sub_le_self _ (Real.arctan_nonneg.2 hm)⟩

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
local notation "pR" => reflectedSupportP F
local notation "qR" => reflectedSupportQ F
local notation "uR" => reflectedFirstWingDensity m ρ
local notation "vR" => reflectedSecondWingDensity ρ

theorem fullTiltedSupportQuarterPair_reflected_calculus :
    AbsolutelyContinuousOnInterval pR 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval qR 0 (Real.pi / 2) ∧
      ∀ᵐ r ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        HasDerivAt pR (uR r - 1 - qR r) r ∧
        HasDerivAt qR (vR r - 1 + pR r) r := by
  obtain ⟨hp, hq, hode⟩ :=
    fullTiltedSupportQuarterPair_corner_calculus hU hm haffine hρ hρ0 hρK heq
  have hL : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hpR := (absolutelyContinuousOnInterval_comp_const_sub hq hL (Real.pi / 2)).neg
  have hqR := (absolutelyContinuousOnInterval_comp_const_sub hp hL (Real.pi / 2)).neg
  have hpr := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2) (hode.mono fun _ ht => ht.1)
  have hqr := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2) (hode.mono fun _ ht => ht.2)
  simp only [sub_self, sub_zero] at hpR hqR hpr hqr
  refine ⟨hpR, hqR, ?_⟩
  filter_upwards [hpr, hqr] with r hp hq
  exact ⟨hq.neg.congr_deriv (by simp only [reflectedFirstWingDensity, reflectedSupportQ]; ring),
    hp.neg.congr_deriv (by simp only [reflectedSecondWingDensity, reflectedSupportP]; ring)⟩

theorem fullTiltedSupportQuarterPair_reflected_dynamics {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t)) :
    CornerArcDynamics pR qR uR vR 0 (fullReflectedActiveEnd m) := by
  have hb := fullReflectedActiveEnd_bounds hm
  have hδ0 := Real.arctan_nonneg.mpr hm
  obtain ⟨hp, hq, hode⟩ :=
    fullTiltedSupportQuarterPair_reflected_calculus hU hm haffine hρ hρ0 hρK heq
  -- Both arm bounds hold on the closed active arc.
  have harms : ∀ r ∈ Icc 0 (fullReflectedActiveEnd m), pR r ≤ 1 ∧ -1 ≤ qR r := by
    have hp := ContinuousOn.le_on_Icc_of_ae_le_on_Ioo (f := p)
      ((((F).continuous_fD.sub (F).continuous_g).add continuousOn_const).mono
        (Icc_subset_Icc hδ0 le_rfl)) (Real.arctan_lt_pi_div_two m) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact fullTiltedSupportQuarterPair_p_le_one_after_affine
        hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1.le, ht.2⟩ ht.1.le)
    intro r hr
    have ht : Real.pi / 2 - r ∈ Icc (Real.arctan m) (Real.pi / 2) := by
      unfold fullReflectedActiveEnd at hr
      constructor <;> linarith [hr.1, hr.2]
    have hq := fullTiltedSupportQuarterPair_q_ge_neg_one
      hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1, ht.2⟩
    simp only [reflectedSupportP, reflectedSupportQ]
    constructor <;> linarith [hp _ ht]
  -- The source laws are those of the original pair at the reflected angle.
  have hs : ∀ᵐ r ∂volume.restrict (Ioo 0 (fullReflectedActiveEnd m)),
      uR r ≤ sourceKappa (qR r) ∧ vR r ≤ sourceKappa (pR r) ∧
      (0 < pR r → 0 < qR r → uR r = 0 ∧ vR r ≤ 1 / 2) := by
    have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
      ((ae_restrict_iff' measurableSet_Ioo).mp
        (hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight
          haffine hhigh hρ hρ0 hρK hκ heq))
    filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with r hr hs
    obtain ⟨hu, hv, -, hmm⟩ := hs ⟨by linarith [hr.2, hb.2], by linarith [hr.1]⟩
    simp only [reflectedFirstWingDensity, reflectedSecondWingDensity, reflectedSupportP,
      reflectedSupportQ, sourceKappa_neg]
    exact ⟨hv, hu, fun hp hq => hmm (by linarith) (by linarith)⟩
  have hcc := uIcc_subset_uIcc_left (Icc_subset_uIcc ⟨hb.1.le, hb.2⟩)
  exact ⟨hb.1.le, hp.mono hcc, hq.mono hcc,
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo le_rfl hb.2) hode,
    hs.mono fun _ h => ⟨h.1, h.2.1⟩, .of_forall fun r => hρ0 _, fun r hr => (harms r hr).2,
    (ae_restrict_mem measurableSet_Ioo).mono fun r hr => .inl (harms r (Ioo_subset_Icc_self hr)).1,
    hs.mono fun _ h => h.2.2⟩

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_reflected_zero_after_active {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1) :
    ∀ᵐ r ∂volume.restrict (Ioo (fullReflectedActiveEnd m) (Real.pi / 2)),
      uR r = 0 ∧ vR r = 0 := by
  have _ := hρK -- not needed by the proof; it stays in the statement for the callers
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioo).mp (hU.full_tilted_wing_densities_zero_before_affine
      hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 heq))
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift] with r hr hs
  unfold fullReflectedActiveEnd at hr
  exact (hs ⟨by linarith [hr.2], by linarith [hr.1]⟩).symm

theorem fullTiltedSupportQuarterPair_reflected_initial_values {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hmpos : 0 < m)
    (hheight : capHeight U = 1) :
    pR 0 = capRoof U (horizontalLeft U) ∧
      qR 0 = (MovingSofaOptimality.vminus U (Real.pi / 2)).1 + 2 * C - 1 := by
  obtain ⟨-, -, hfL, hgL, -, -, hfDL, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  simp only [reflectedSupportP, reflectedSupportQ, supportP, supportQ, sub_zero, hfL, hgL, hfDL,
    hgDL, hheight, hl]
  constructor <;> ring

/-- The active endpoint has second momentum below one. A coarse box
estimate at the actual middle normal suffices; no late phase is assumed. -/
theorem fullTiltedSupportQuarterPair_reflected_second_at_activeEnd {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 2 / 3 ≤ C) (hsmall : C + m < 1) :
    qR (fullReflectedActiveEnd m) ≤ 1 := by
  have hδ0 := Real.arctan_nonneg.mpr hm
  have hδL := Real.arctan_lt_pi_div_two m
  have hs := Real.sin_nonneg_of_mem_Icc ⟨hδ0, by linarith [Real.pi_pos]⟩
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hδL.le⟩
  have hcoef := tilted_initial_coefficient_nonneg hδ0 (le_refl (Real.arctan m))
  have hsin : Real.sin (Real.arctan m) ≤ m := by
    nlinarith [mul_nonneg hm (sub_nonneg.2 (Real.cos_le_one (Real.arctan m)))]
  have hleft : horizontalLeft U + capWidth U / 4 = -C := by unfold capWidth; rw [hl, hr]; ring
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints (zero_lt_two.trans hU.two_lt_width)
  have hg : (F).g (Real.arctan m) = _ :=
    hU.isCap.companionSupport_leftCut_eq_low_of_affine ha hb hab haffine hc hcoef
  have hroof : capRoof U _ ≤ 1 := (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact ha)).2
  have hpU := (MovingSofaOptimality.vplus_mem_edge hU.isCap.imported_isConvexBody
    (Real.arctan m)).1
  have hx := (hU.isCap.fst_mem_Icc hpU).2
  rw [hleft] at hg hroof
  rw [hr] at hx
  simp only [reflectedSupportQ, fullReflectedActiveEnd, sub_sub_cancel, supportP, hg,
    fullTiltedSupportQuarterPair_first_derivative hU hm haffine hρ hρ0 hρK heq ⟨hδ0, hδL⟩,
    supportTangent, MovingSofaOptimality.dot, MovingSofaOptimality.vvec]
  nlinarith [mul_le_mul_of_nonneg_right hx hs, mul_nonneg (hU.isCap.inStrip hpU).1 hc,
    mul_le_mul_of_nonneg_right hroof hc, mul_le_mul_of_nonneg_left hsin (by linarith : 0 ≤ C),
    mul_nonneg hm (by linarith : 0 ≤ 1 - C), Real.cos_le_one (Real.arctan m)]

end ActualPair

end AmbidextrousSofa
