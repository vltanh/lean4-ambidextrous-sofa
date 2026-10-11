module

public import AmbidextrousSofa.Analysis.ClosedSupportPair
public import AmbidextrousSofa.Analysis.TiltedWingSupport
public import AmbidextrousSofa.Analysis.CornerCrossing

@[expose] public section

/-!
# The actual two-cap support pair for a tilted full maximum

The first quarter belongs to the original cap. The companion quarter
belongs to its literal left cut at the low middle endpoint. Both use the
same original density, with the cut density set to zero through the
middle normal. All closed derivatives, endpoint traces, and coupled
equations are obtained from these actual supports.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem leftCompanionWingDensity_bounds {ρ : ℝ → ℝ} {K m : ℝ}
    (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) (t : ℝ) :
    0 ≤ leftCompanionWingDensity m ρ t ∧ leftCompanionWingDensity m ρ t ≤ K :=
  ⟨indicator_nonneg (fun s _ => hρ0 s) t,
    indicator_apply_le' (fun _ => hρK t) fun _ => (hρ0 0).trans (hρK 0)⟩

theorem IsFullCapMaximizer.isCap_fullLeftCompanion
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsDownwardCap (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) :=
  hU.isCap.leftCompanionCap (hU.isCap.middleChord_endpoints (zero_lt_two.trans hU.two_lt_width)).1

def fullTiltedSupportQuarterPair {U : Set Plane} (hU : IsFullCapMaximizer U)
    {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
      (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t))) :
    Analysis.QuarterPair :=
  supportQuarterPair hU.isCap hU.isCap_fullLeftCompanion hρ hρ0 hρK
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).2)
    (restrict_withDensity_of_subset heq measurableSet_Ioo
      (firstQuarter_subset_regularCurvatureDomain_of_nonneg hm))
    (hU.leftCompanion_density_of_regular_companion haffine
      (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
        (regularCompanionDomain_subset_regularCurvatureDomain m)))

section ActualPair

variable {U : Set Plane} (hU : IsFullCapMaximizer U)
  {m c : ℝ} {ρ : ℝ → ℝ} {K : ℝ} (hm : 0 ≤ m)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

local notation "F" => fullTiltedSupportQuarterPair hU hm haffine hρ hρ0 hρK heq

theorem fullTiltedSupportQuarterPair_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (F).f 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (F).g 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (F).fD 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (F).gD 0 (Real.pi / 2) :=
  supportQuarterPair_absolutelyContinuous _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_ae_derivatives :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt (F).f ((F).fD t) t ∧ HasDerivAt (F).g ((F).gD t) t ∧
      HasDerivAt (F).fD (ρ t - (F).f t) t ∧
      HasDerivAt (F).gD (leftCompanionWingDensity m ρ (t + Real.pi / 2) - (F).g t) t :=
  supportQuarterPair_ae_derivatives _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_corner_calculus :
    AbsolutelyContinuousOnInterval (supportP (F).fD (F).g) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (supportQ (F).gD (F).f) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        HasDerivAt (supportP (F).fD (F).g) (ρ t - 1 - supportQ (F).gD (F).f t) t ∧
        HasDerivAt (supportQ (F).gD (F).f)
          (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1 + supportP (F).fD (F).g t) t :=
  supportQuarterPair_corner_calculus _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_points_mem :
    (∀ t ∈ Icc 0 (Real.pi / 2), Reference.supportPoint (F).f (F).fD t ∈ U) ∧
      ∀ t ∈ Icc 0 (Real.pi / 2), Reference.companionSupportPoint (F).g (F).gD t ∈
        leftCompanionCap U (horizontalLeft U + capWidth U / 4) :=
  supportQuarterPair_points_mem _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_base_traces :
    (F).f 0 = horizontalRight U ∧
      (F).g 0 = capHeight (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) ∧
      (F).f (Real.pi / 2) = capHeight U ∧
      (F).g (Real.pi / 2) = -horizontalLeft (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) ∧
      (F).fD 0 = capRoof U (horizontalRight U) ∧
      (F).gD 0 = -(MovingSofaOptimality.vplus (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
        (Real.pi / 2)).1 ∧
      (F).fD (Real.pi / 2) = -(MovingSofaOptimality.vminus U (Real.pi / 2)).1 ∧
      (F).gD (Real.pi / 2) = -capRoof (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
        (horizontalLeft (leftCompanionCap U (horizontalLeft U + capWidth U / 4))) :=
  supportQuarterPair_traces _ _ _ _ _ _ _ _ _ _

/-- Positive tilt pins the cut's unique top point at the actual low
middle endpoint. The terminal first derivative retains the genuine
right endpoint of the original top face. -/
theorem fullTiltedSupportQuarterPair_traces (hmpos : 0 < m) :
    (F).f 0 = horizontalRight U ∧
      (F).g 0 = capRoof U (horizontalLeft U + capWidth U / 4) ∧
      (F).f (Real.pi / 2) = capHeight U ∧ (F).g (Real.pi / 2) = -horizontalLeft U ∧
      (F).fD 0 = capRoof U (horizontalRight U) ∧
      (F).gD 0 = -(horizontalLeft U + capWidth U / 4) ∧
      (F).fD (Real.pi / 2) = -(MovingSofaOptimality.vminus U (Real.pi / 2)).1 ∧
      (F).gD (Real.pi / 2) = -capRoof U (horizontalLeft U) := by
  have hW := zero_lt_two.trans hU.two_lt_width
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hW
  have htop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hmpos haffine
  have hP := horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex
  have hroof : capRoof (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (horizontalLeft U) = capRoof U (horizontalLeft U) :=
    capRoof_horizontalCut hU.isCap (by linarith) (hP ▸ Icc_subset_Icc le_rfl (hP ▸ ha).2)
      ⟨le_rfl, by linarith⟩
  simpa only [htop.1, htop.2, horizontalLeft_leftCompanionCap hU.isCap ha, hroof] using
    fullTiltedSupportQuarterPair_base_traces hU hm haffine hρ hρ0 hρK heq

theorem fullTiltedSupportQuarterPair_first_derivative {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) : (F).fD t = supportTangent U t := by
  simpa only [fullTiltedSupportQuarterPair, supportQuarterPair, add_zero] using
    hU.isCap.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq (d := 0)
      (by simpa using firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) ht.1 ht.2

/-- After the middle normal, the surrogate's support and tangent are
literally the original cap's companion support and tangent. -/
theorem fullTiltedSupportQuarterPair_after_affine {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) (hmt : Real.arctan m ≤ t) :
    (F).g t = angleSupport U (t + Real.pi / 2) ∧
      (F).gD t = supportTangent U (t + Real.pi / 2) ∧
      supportP (F).fD (F).g t = -secondCornerVelocity U t ∧
      supportQ (F).gD (F).f t = firstCornerVelocity U t := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints (zero_lt_two.trans hU.two_lt_width)
  have hmatch := hU.isCap.companionSupport_and_tangent_leftCut_after_affine
    ha hb hab haffine hmt ht.1 ht.2
  have hgd := hU.isCap_fullLeftCompanion.closedSupportDerivative_eq_supportTangent
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2)
    (hU.leftCompanion_density_of_regular_companion haffine
      (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
        (regularCompanionDomain_subset_regularCurvatureDomain m)))
    (d := Real.pi / 2) (fun s hs => ⟨hs.1, by linarith [hs.2]⟩) ht.1 ht.2
  have hg : (F).g t = angleSupport U (t + Real.pi / 2) := hmatch.1
  have hgD : (F).gD t = supportTangent U (t + Real.pi / 2) := hgd.trans hmatch.2
  refine ⟨hg, hgD, ?_, ?_⟩
  · rw [supportP, fullTiltedSupportQuarterPair_first_derivative hU hm haffine hρ hρ0 hρK heq ht,
      hg]
    simp only [angleSupport_eq_imported_supp, supportTangent, secondCornerVelocity]
    ring
  · rw [supportQ, hgD]
    simp only [fullTiltedSupportQuarterPair, supportQuarterPair, angleSupport_eq_imported_supp,
      supportTangent, firstCornerVelocity]
    ring

/-- The first tangent is always the original cap's tangent, regardless
of whether the companion quarter has passed its middle normal. -/
theorem fullTiltedSupportQuarterPair_first_tangency {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) :
    firstTangentPoint (F).f (F).fD t = firstTangency U t := by
  simp only [firstTangentPoint, Reference.supportPoint,
    fullTiltedSupportQuarterPair_first_derivative hU hm haffine hρ hρ0 hρK heq ht]
  exact Prod.ext (firstTangency_fst_eq_support U t).symm (firstTangency_snd_eq_support U t).symm

theorem fullTiltedSupportQuarterPair_other_points_after_affine {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) (hmt : Real.arctan m ≤ t) :
    secondTangentPoint (F).g (F).gD t = secondTangency U t ∧
      innerCornerPoint (F).f (F).g t = attachedCorner U t := by
  obtain ⟨hg, hgD, -, -⟩ :=
    fullTiltedSupportQuarterPair_after_affine hU hm haffine hρ hρ0 hρK heq ht hmt
  constructor
  · rw [secondTangentPoint, companionSupportPoint_coordinates, hg, hgD]
    ext <;> simp only [secondTangency_fst_eq_support, secondTangency_snd_eq_support] <;> ring
  · simp only [innerCornerPoint, hg]
    exact Prod.ext (attachedCorner_fst_eq_support U t).symm (attachedCorner_snd_eq_support U t).symm

end ActualPair

end AmbidextrousSofa
