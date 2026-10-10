import AmbidextrousSofa.Analysis.ClosedSupportPair
import AmbidextrousSofa.Analysis.TiltedWingSupport
import AmbidextrousSofa.Analysis.CornerCrossing

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
    0 ≤ leftCompanionWingDensity m ρ t ∧ leftCompanionWingDensity m ρ t ≤ K := by
  by_cases ht : max (Real.pi / 2) (affineNormalAngle m) < t
  · rw [leftCompanionWingDensity_eq ht]
    exact ⟨hρ0 t, hρK t⟩
  · rw [leftCompanionWingDensity_eq_zero (le_of_not_gt ht)]
    exact ⟨le_rfl, (hρ0 0).trans (hρK 0)⟩

theorem IsFullCapMaximizer.isCap_fullLeftCompanion
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsDownwardCap (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) :=
  hU.isCap.leftCompanionCap (hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])).1

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
    AbsolutelyContinuousOnInterval F.f 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval F.g 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval F.fD 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval F.gD 0 (Real.pi / 2) := by
  unfold fullTiltedSupportQuarterPair
  exact supportQuarterPair_absolutelyContinuous _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_ae_derivatives :
    ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
      HasDerivAt F.f (F.fD t) t ∧ HasDerivAt F.g (F.gD t) t ∧
      HasDerivAt F.fD (ρ t - F.f t) t ∧
      HasDerivAt F.gD (leftCompanionWingDensity m ρ (t + Real.pi / 2) - F.g t) t := by
  unfold fullTiltedSupportQuarterPair
  exact supportQuarterPair_ae_derivatives _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_corner_calculus :
    AbsolutelyContinuousOnInterval (supportP F.fD F.g) 0 (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (supportQ F.gD F.f) 0 (Real.pi / 2) ∧
      ∀ᵐ t ∂volume.restrict (Ioo 0 (Real.pi / 2)),
        HasDerivAt (supportP F.fD F.g) (ρ t - 1 - supportQ F.gD F.f t) t ∧
        HasDerivAt (supportQ F.gD F.f)
          (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1 + supportP F.fD F.g t) t := by
  unfold fullTiltedSupportQuarterPair
  exact supportQuarterPair_corner_calculus _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_points_mem :
    (∀ t ∈ Icc 0 (Real.pi / 2), Reference.supportPoint F.f F.fD t ∈ U) ∧
      ∀ t ∈ Icc 0 (Real.pi / 2), Reference.companionSupportPoint F.g F.gD t ∈
        leftCompanionCap U (horizontalLeft U + capWidth U / 4) := by
  unfold fullTiltedSupportQuarterPair
  exact supportQuarterPair_points_mem _ _ _ _ _ _ _ _ _ _

theorem fullTiltedSupportQuarterPair_base_traces :
    F.f 0 = horizontalRight U ∧
      F.g 0 = capHeight (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) ∧
      F.f (Real.pi / 2) = capHeight U ∧
      F.g (Real.pi / 2) = -horizontalLeft (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) ∧
      F.fD 0 = capRoof U (horizontalRight U) ∧
      F.gD 0 = -(Imported.vplus (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
        (Real.pi / 2)).1 ∧
      F.fD (Real.pi / 2) = -(Imported.vminus U (Real.pi / 2)).1 ∧
      F.gD (Real.pi / 2) = -capRoof (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
        (horizontalLeft (leftCompanionCap U (horizontalLeft U + capWidth U / 4))) := by
  unfold fullTiltedSupportQuarterPair
  exact supportQuarterPair_traces _ _ _ _ _ _ _ _ _ _

/-- Positive tilt pins the cut's unique top point at the actual low
middle endpoint. The terminal first derivative retains the genuine
right endpoint of the original top face. -/
theorem fullTiltedSupportQuarterPair_traces (hmpos : 0 < m) :
    F.f 0 = horizontalRight U ∧
      F.g 0 = capRoof U (horizontalLeft U + capWidth U / 4) ∧
      F.f (Real.pi / 2) = capHeight U ∧ F.g (Real.pi / 2) = -horizontalLeft U ∧
      F.fD 0 = capRoof U (horizontalRight U) ∧
      F.gD 0 = -(horizontalLeft U + capWidth U / 4) ∧
      F.fD (Real.pi / 2) = -(Imported.vminus U (Real.pi / 2)).1 ∧
      F.gD (Real.pi / 2) = -capRoof U (horizontalLeft U) := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have htop := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hmpos haffine
  have hleft := horizontalLeft_leftCompanionCap hU.isCap ha
  have ha' := ha
  rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex] at ha'
  have hsub : Icc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) ⊆
      horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    exact Icc_subset_Icc le_rfl ha'.2
  have hroof : capRoof (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (horizontalLeft U) = capRoof U (horizontalLeft U) :=
    capRoof_horizontalCut hU.isCap ha'.1 hsub ⟨le_rfl, ha'.1⟩
  simpa only [htop.1, htop.2, hleft, hroof] using
    fullTiltedSupportQuarterPair_base_traces hU hm haffine hρ hρ0 hρK heq

theorem fullTiltedSupportQuarterPair_first_derivative {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) : F.fD t = supportTangent U t := by
  have h := hU.isCap.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK heq
    (d := 0) (by simpa only [zero_add] using
      firstQuarter_subset_regularCurvatureDomain_of_nonneg hm) ht.1 ht.2
  simpa only [fullTiltedSupportQuarterPair, supportQuarterPair, add_zero] using h

/-- After the middle normal, the surrogate's support and tangent are
literally the original cap's companion support and tangent. -/
theorem fullTiltedSupportQuarterPair_after_affine {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) (hmt : Real.arctan m ≤ t) :
    F.g t = angleSupport U (t + Real.pi / 2) ∧
      F.gD t = supportTangent U (t + Real.pi / 2) ∧
      supportP F.fD F.g t = -secondCornerVelocity U t ∧
      supportQ F.gD F.f t = firstCornerVelocity U t := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hmatch := hU.isCap.companionSupport_and_tangent_leftCut_after_affine
    ha hb hab haffine hmt ht.1 ht.2
  have hcut := hU.leftCompanion_density_of_regular_companion haffine
    (restrict_withDensity_of_subset heq (measurableSet_regularCompanionDomain m)
      (regularCompanionDomain_subset_regularCurvatureDomain m))
  have hgd := hU.isCap_fullLeftCompanion.closedSupportDerivative_eq_supportTangent
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2) hcut
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith only [hs.2]⟩) ht.1 ht.2
  have hg : F.g t = angleSupport U (t + Real.pi / 2) := hmatch.1
  have hgD : F.gD t = supportTangent U (t + Real.pi / 2) := hgd.trans hmatch.2
  have hfD := fullTiltedSupportQuarterPair_first_derivative hU hm haffine hρ hρ0 hρK heq ht
  refine ⟨hg, hgD, ?_, ?_⟩
  · dsimp only [supportP]
    rw [hfD, hg]
    dsimp only [supportTangent, secondCornerVelocity, angleSupport]
    ring
  · dsimp only [supportQ]
    rw [hgD]
    change supportTangent U (t + Real.pi / 2) + angleSupport U t - 1 =
      firstCornerVelocity U t
    dsimp only [supportTangent, firstCornerVelocity, angleSupport]
    ring

/-- The first tangent is always the original cap's tangent, regardless
of whether the companion quarter has passed its middle normal. -/
theorem fullTiltedSupportQuarterPair_first_tangency {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) :
    firstTangentPoint F.f F.fD t = firstTangency U t := by
  have hfD := fullTiltedSupportQuarterPair_first_derivative hU hm haffine hρ hρ0 hρK heq ht
  apply Prod.ext
  · change (angleSupport U t - 1) * Real.cos t - F.fD t * Real.sin t = _
    rw [hfD, firstTangency_fst_eq_support]
  · change (angleSupport U t - 1) * Real.sin t + F.fD t * Real.cos t = _
    rw [hfD, firstTangency_snd_eq_support]

theorem fullTiltedSupportQuarterPair_other_points_after_affine {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) (hmt : Real.arctan m ≤ t) :
    secondTangentPoint F.g F.gD t = secondTangency U t ∧
      innerCornerPoint F.f F.g t = attachedCorner U t := by
  have hmatch := fullTiltedSupportQuarterPair_after_affine hU hm haffine hρ hρ0 hρK heq ht hmt
  constructor
  · rw [secondTangentPoint, companionSupportPoint_coordinates, hmatch.1, hmatch.2.1]
    apply Prod.ext
    · dsimp only [Prod.fst]
      rw [secondTangency_fst_eq_support]
      ring
    · dsimp only [Prod.snd]
      rw [secondTangency_snd_eq_support]
      ring
  · apply Prod.ext
    · change (angleSupport U t - 1) * Real.cos t - (F.g t - 1) * Real.sin t = _
      rw [hmatch.1, attachedCorner_fst_eq_support]
    · change (angleSupport U t - 1) * Real.sin t + (F.g t - 1) * Real.cos t = _
      rw [hmatch.1, attachedCorner_snd_eq_support]

end ActualPair

end AmbidextrousSofa
