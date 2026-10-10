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
    0 < fullReflectedActiveEnd m ∧ fullReflectedActiveEnd m ≤ Real.pi / 2 := by
  dsimp only [fullReflectedActiveEnd]
  exact ⟨sub_pos.mpr (Real.arctan_lt_pi_div_two m),
    sub_le_self _ (Real.arctan_nonneg.mpr hm)⟩

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
  have hpAC : AbsolutelyContinuousOnInterval pR 0 (Real.pi / 2) := by
    have h := (absolutelyContinuousOnInterval_comp_const_sub hq hL (Real.pi / 2)).neg
    simp only [sub_self, sub_zero] at h
    exact h
  have hqAC : AbsolutelyContinuousOnInterval qR 0 (Real.pi / 2) := by
    have h := (absolutelyContinuousOnInterval_comp_const_sub hp hL (Real.pi / 2)).neg
    simp only [sub_self, sub_zero] at h
    exact h
  refine ⟨hpAC, hqAC, ?_⟩
  have hpr := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2)
    (hode.mono (fun _ ht => ht.1))
  have hqr := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2)
    (hode.mono (fun _ ht => ht.2))
  simp only [sub_self, sub_zero] at hpr hqr
  filter_upwards [hpr, hqr] with r hp hq
  constructor
  · apply hq.neg.congr_deriv
    dsimp only [reflectedFirstWingDensity, reflectedSupportQ]
    ring
  · apply hp.neg.congr_deriv
    dsimp only [reflectedSecondWingDensity, reflectedSupportP]
    ring

theorem fullTiltedSupportQuarterPair_reflected_arm_bounds :
    ∀ r ∈ Icc 0 (fullReflectedActiveEnd m), pR r ≤ 1 ∧ -1 ≤ qR r := by
  have hδ0 := Real.arctan_nonneg.mpr hm
  have hδL := Real.arctan_lt_pi_div_two m
  have hpcont : ContinuousOn p (Icc (Real.arctan m) (Real.pi / 2)) :=
    (((F).continuous_fD.sub (F).continuous_g).add continuousOn_const).mono
      (Icc_subset_Icc hδ0 le_rfl)
  have hpclosed := ContinuousOn.le_on_Icc_of_ae_le_on_Ioo hpcont hδL (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact fullTiltedSupportQuarterPair_p_le_one_after_affine
      hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1.le, ht.2⟩ ht.1.le)
  intro r hr
  have ht : Real.pi / 2 - r ∈ Icc (Real.arctan m) (Real.pi / 2) := by
    dsimp only [fullReflectedActiveEnd] at hr
    constructor <;> linarith only [hr.1, hr.2]
  have hq := fullTiltedSupportQuarterPair_q_ge_neg_one
    hU hm haffine hρ hρ0 hρK heq ⟨hδ0.trans ht.1, ht.2⟩
  have hp := hpclosed _ ht
  dsimp only [reflectedSupportP, reflectedSupportQ]
  constructor <;> linarith only [hp, hq]

theorem fullTiltedSupportQuarterPair_reflected_source_controls {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t)) :
    ∀ᵐ r ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      uR r ≤ sourceKappa (qR r) ∧ vR r ≤ sourceKappa (pR r) ∧
      (0 < pR r → 0 < qR r → uR r = 0 ∧ vR r ≤ 1 / 2) := by
  have hactual := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.fullTiltedSupportQuarterPair_source_controls hl hr hC hm hsmall hheight
      haffine hhigh hρ hρ0 hρK hκ heq)
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae
    hactual
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift]
    with r hr hs
  have ht : Real.pi / 2 - r ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor <;> linarith only [hr.1, hr.2]
  obtain ⟨hu, hv, _hpp, hmm⟩ := hs ht
  refine ⟨?_, ?_, ?_⟩
  · simpa only [reflectedFirstWingDensity, reflectedSupportQ, sourceKappa_neg] using hv
  · simpa only [reflectedSecondWingDensity, reflectedSupportP, sourceKappa_neg] using hu
  · intro hp hq
    dsimp only [reflectedSupportP, reflectedSupportQ] at hp hq
    exact hmm (by linarith only [hq]) (by linarith only [hp])

theorem fullTiltedSupportQuarterPair_reflected_dynamics {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t)) :
    CornerArcDynamics pR qR uR vR 0 (fullReflectedActiveEnd m) := by
  have hb := fullReflectedActiveEnd_bounds hm
  obtain ⟨hp, hq, hode⟩ :=
    fullTiltedSupportQuarterPair_reflected_calculus hU hm haffine hρ hρ0 hρK heq
  have hsubcc : uIcc 0 (fullReflectedActiveEnd m) ⊆ uIcc 0 (Real.pi / 2) := by
    rw [uIcc_of_le hb.1.le, uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact Icc_subset_Icc le_rfl hb.2
  have hsub : Ioo (0 : ℝ) (fullReflectedActiveEnd m) ⊆ Ioo (0 : ℝ) (Real.pi / 2) :=
    Ioo_subset_Ioo le_rfl hb.2
  have hs := ae_restrict_of_ae_restrict_of_subset hsub
    (fullTiltedSupportQuarterPair_reflected_source_controls
      hU hm haffine hρ hρ0 hρK heq hl hr hC hsmall hheight hhigh hκ)
  have harms := fullTiltedSupportQuarterPair_reflected_arm_bounds
    hU hm haffine hρ hρ0 hρK heq
  refine ⟨hb.1.le, hp.mono hsubcc, hq.mono hsubcc,
    ae_restrict_of_ae_restrict_of_subset hsub hode,
    hs.mono (fun _ h => ⟨h.1, h.2.1⟩), ?_,
    fun r hr => (harms r hr).2, ?_, hs.mono (fun _ h => h.2.2)⟩
  · exact Filter.Eventually.of_forall (fun r => hρ0 (Real.pi / 2 - r))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact Or.inl (harms r (Ioo_subset_Icc_self hr)).1

include hU hm haffine hρ hρ0 hρK heq in
theorem fullTiltedSupportQuarterPair_reflected_zero_after_active {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 0 < C) (hsmall : C + m < 1)
    (hheight : capHeight U = 1) (hhigh : capRoof U C = 1) :
    ∀ᵐ r ∂volume.restrict (Ioo (fullReflectedActiveEnd m) (Real.pi / 2)),
      uR r = 0 ∧ vR r = 0 := by
  have hzero := (ae_restrict_iff' measurableSet_Ioo).mp
    (hU.full_tilted_wing_densities_zero_before_affine
      hl hr hC hm hsmall hheight haffine hhigh hρ hρ0 heq)
  have hshift := (volume.measurePreserving_sub_left (Real.pi / 2)).quasiMeasurePreserving.ae hzero
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hshift]
    with r hr hs
  have ht : Real.pi / 2 - r ∈ Ioo (0 : ℝ) (Real.arctan m) := by
    dsimp only [fullReflectedActiveEnd] at hr
    constructor <;> linarith only [hr.1, hr.2]
  exact ⟨(hs ht).2, (hs ht).1⟩

theorem fullTiltedSupportQuarterPair_reflected_initial_values {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hmpos : 0 < m)
    (hheight : capHeight U = 1) :
    pR 0 = capRoof U (horizontalLeft U) ∧
      qR 0 = (MovingSofaOptimality.vminus U (Real.pi / 2)).1 + 2 * C - 1 := by
  obtain ⟨_hf0, _hg0, hfL, hgL, _hfD0, _hgD0, hfDL, hgDL⟩ :=
    fullTiltedSupportQuarterPair_traces hU hm haffine hρ hρ0 hρK heq hmpos
  constructor
  · dsimp only [reflectedSupportP, supportQ]
    rw [sub_zero, hgDL, hfL, hheight]
    ring
  · dsimp only [reflectedSupportQ, supportP]
    rw [sub_zero, hfDL, hgL, hl]
    ring

/-- The active endpoint has second momentum below one. A coarse box
estimate at the actual middle normal suffices; no late phase is assumed. -/
theorem fullTiltedSupportQuarterPair_reflected_second_at_activeEnd {C : ℝ}
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hC : 2 / 3 ≤ C) (hsmall : C + m < 1) :
    qR (fullReflectedActiveEnd m) ≤ 1 := by
  let δ := Real.arctan m
  have hδ0 : 0 ≤ δ := Real.arctan_nonneg.mpr hm
  have hδL : δ < Real.pi / 2 := Real.arctan_lt_pi_div_two m
  have hCpos : 0 < C := by linarith only [hC]
  have hC1 : C < 1 := by linarith only [hsmall, hm]
  have hm1 : m < 1 / 3 := by linarith only [hsmall, hC]
  have hs : 0 ≤ Real.sin δ := Real.sin_nonneg_of_mem_Icc
    ⟨hδ0, by linarith only [hδL, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos δ := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hδ0, Real.pi_pos], hδL⟩).le
  have hcoef := tilted_initial_coefficient_nonneg hδ0 (le_refl δ)
  have hsin : Real.sin δ ≤ m := by
    have hp := mul_nonneg hm (sub_nonneg.mpr (Real.cos_le_one δ))
    linarith only [hcoef, hp]
  have hW : capWidth U = 4 * C := by unfold capWidth; rw [hl, hr]; ring
  have hleft : horizontalLeft U + capWidth U / 4 = -C := by rw [hl, hW]; ring
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by rw [hW]; positivity)
  have hg := hU.isCap.companionSupport_leftCut_eq_low_of_affine
    ha hb hab haffine hc hcoef
  change (F).g δ = -(horizontalLeft U + capWidth U / 4) * Real.sin δ +
    capRoof U (horizontalLeft U + capWidth U / 4) * Real.cos δ at hg
  have hroof := (hU.isCap.inStrip (capRoof_mem hU.isCap.isCompact ha)).2
  have hroofcos := mul_le_mul_of_nonneg_right hroof hc
  have hgupper : (F).g δ ≤ C * Real.sin δ + 1 := by
    rw [hg, hleft]
    rw [hleft] at hroofcos
    nlinarith only [hroofcos, Real.cos_le_one δ]
  have hpU := (MovingSofaOptimality.vplus_mem_edge hU.isCap.imported_isConvexBody δ).1
  have hx := (hU.isCap.fst_mem_Icc hpU).2
  rw [hr] at hx
  have hy := (hU.isCap.inStrip hpU).1
  have hxsin := mul_le_mul_of_nonneg_right hx hs
  have hycos := mul_nonneg hy hc
  have hfD := fullTiltedSupportQuarterPair_first_derivative
    hU hm haffine hρ hρ0 hρK heq ⟨hδ0, hδL⟩
  have hfDlower : -2 * C * Real.sin δ ≤ (F).fD δ := by
    rw [hfD]
    dsimp only [supportTangent, MovingSofaOptimality.dot, MovingSofaOptimality.vvec]
    nlinarith only [hxsin, hycos]
  have hps : -3 * C * Real.sin δ ≤ p δ := by
    dsimp only [supportP]
    linarith only [hfDlower, hgupper]
  have hCms := mul_le_mul_of_nonneg_left hsin (show 0 ≤ 3 * C by linarith only [hC])
  have hCm := mul_nonneg hm (sub_nonneg.mpr hC1.le)
  have hpδ : -1 < p δ := by nlinarith only [hps, hCms, hCm, hm1]
  dsimp only [reflectedSupportQ, fullReflectedActiveEnd]
  rw [sub_sub_cancel]
  change -p δ ≤ 1
  linarith only [hpδ]

end ActualPair

end AmbidextrousSofa
