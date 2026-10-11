module

public import AmbidextrousSofa.Analysis.PartialWingSupport
public import AmbidextrousSofa.Analysis.TiltedSupportPair
public import AmbidextrousSofa.Analysis.TiltedInitialEnergy

@[expose] public section

/-!
# The actual reflected support system after the terminal impulse

The first derivative is continued across the used arc by its curvature
integral, ending at the actual left tangent trace of the terminal face.
The second support is the literal left companion cut. Their reflected
momenta are absolutely continuous on the closed used interval. At its
initial endpoint the exact terminal atom is added to the free harmonic
tail value of the second momentum. No central atom from an unused
negative-tilt arc is included.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The first used momentum. -/
def properUsedP (U : Set Plane) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  supportP (closedSupportDerivative U ρ 0)
    (fun t => angleSupport (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (t + Real.pi / 2))

def properUsedQ (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  supportQ
    (closedSupportDerivative (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (leftCompanionWingDensity m ρ) (Real.pi / 2)) (angleSupport U)

def properReflectedP (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -properUsedQ U m ρ (Real.pi / 2 - r)

def properReflectedQ (U : Set Plane) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -properUsedP U ρ (Real.pi / 2 - r)

def properReflectedFirstDensity (m : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  leftCompanionWingDensity m ρ (Real.pi / 2 - r + Real.pi / 2)

def properReflectedSecondDensity (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ρ (Real.pi / 2 - r)

def terminalReflectedHeight (U : Set Plane) (α : ℝ) : ℝ :=
  capRoof U (horizontalLeft U) + 1 - (terminalTailPoint U α).2

def terminalReflectedSpan (U : Set Plane) (α : ℝ) : ℝ :=
  (terminalTailPoint U α).1 - horizontalLeft U

theorem IsJointCapMaximizer.isCap_properLeftCompanion
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    IsDownwardCap (leftCompanionCap U (horizontalLeft U + capWidth U / 4)) :=
  hU.isCap.leftCompanionCap (hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])).1

section

variable {U : Set Plane} {α m c K t : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
  (hregime : ProperTailRegime U α m) (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
    capRoof U x = m * x + c)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
    (volume.restrict (regularProperCurvatureDomain α m)).withDensity
      (fun t => ENNReal.ofReal (ρ t)))
include hU hρ hρ0 hρK

/-- The used momenta are absolutely continuous on `[0, α]`; reflecting by `r ↦ π / 2 - r`
gives the reflected momenta on `[π / 2 - α, π / 2]`. -/
theorem IsJointCapMaximizer.properReflected_momenta_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (properReflectedP U m ρ) (Real.pi / 2 - α) (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (properReflectedQ U ρ) (Real.pi / 2 - α) (Real.pi / 2) := by
  have hV := hU.isCap_properLeftCompanion
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 α :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval (properUsedP U ρ) 0 α :=
    ((hU.isCap.absolutelyContinuousOnInterval_closedSupportDerivative hρ hρ0 hρK 0 α 0).sub
      (hV.absolutelyContinuousOnInterval_angleSupport_shift 0 α (Real.pi / 2))).add hc
  have hQ : AbsolutelyContinuousOnInterval (properUsedQ U m ρ) 0 α :=
    ((hV.absolutelyContinuousOnInterval_closedSupportDerivative
      (measurable_leftCompanionWingDensity hρ m)
      (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).1)
      (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).2) 0 α (Real.pi / 2)).add
        (hU.isCap.absolutelyContinuousOnInterval_angleSupport 0 α)).sub hc
  replace hP := (absolutelyContinuousOnInterval_comp_const_sub hP hU.angle_pos.le (Real.pi / 2)).neg
  replace hQ := (absolutelyContinuousOnInterval_comp_const_sub hQ hU.angle_pos.le (Real.pi / 2)).neg
  rw [sub_zero] at hP hQ
  exact ⟨hQ, hP⟩

include hregime hproper haffine heq

/-- The used momenta satisfy the support system almost everywhere on `(0, α)`; reflecting by
`r ↦ π / 2 - r` gives the reflected system. -/
theorem IsJointCapMaximizer.properReflected_momenta_ae_derivatives_of_tail_regime :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      HasDerivAt (properReflectedP U m ρ)
        (properReflectedFirstDensity m ρ r - 1 - properReflectedQ U ρ r) r ∧
      HasDerivAt (properReflectedQ U ρ)
        (properReflectedSecondDensity ρ r - 1 + properReflectedP U m ρ r) r := by
  have hV := hU.isCap_properLeftCompanion
  have hσ := measurable_leftCompanionWingDensity hρ m
  have hσ0 := fun t => (leftCompanionWingDensity_bounds (m := m) hρ0 hρK t).1
  have hσK := fun t => (leftCompanionWingDensity_bounds (m := m) hρ0 hρK t).2
  have h : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) α),
      HasDerivAt (properUsedP U ρ) (ρ t - 1 - properUsedQ U m ρ t) t ∧
      HasDerivAt (properUsedQ U m ρ)
        (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1 + properUsedP U ρ t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      hU.isCap.ae_hasDerivAt_closedSupportDerivative hρ hρ0 hρK 0,
      hV.ae_hasDerivAt_closedSupportDerivative hσ hσ0 hσK (Real.pi / 2)]
      with t ht hfDD hgDD
    have hdf := hU.isCap.hasDerivAt_shiftedSupport_of_open_density hρ hρ0 hρK
      (hregime.first_density_of_regular hproper heq) (d := 0) (by simp) ht
    have hdg := hV.hasDerivAt_shiftedSupport_of_open_density hσ hσ0 hσK
      (hU.proper_leftCompanion_density_of_regular hproper haffine heq) (d := Real.pi / 2)
      (Ioo_subset_Ioo le_rfl (add_halves _).le) ⟨ht.1, ht.2.trans hproper⟩
    simp only [add_zero] at hfDD hdf
    exact ⟨((hfDD.sub hdg).add_const 1).congr_deriv (by simp only [properUsedQ, supportQ]; ring),
      ((hgDD.add hdf).sub_const 1).congr_deriv (by simp only [properUsedP, supportP]; ring)⟩
  have hp := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2) (h.mono fun _ ht => ht.1)
  have hq := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2) (h.mono fun _ ht => ht.2)
  rw [sub_zero] at hp hq
  filter_upwards [hp, hq] with r hp hq
  exact ⟨hq.neg.congr_deriv (by simp only [properReflectedFirstDensity, properReflectedQ]; ring),
    hp.neg.congr_deriv (by simp only [properReflectedSecondDensity, properReflectedP]; ring)⟩

theorem IsJointCapMaximizer.properUsed_momenta_eq_actual_after_affine_of_tail_regime
    (ht : t ∈ Ico (0 : ℝ) α) (hmt : Real.arctan m ≤ t) :
    properUsedP U ρ t = -secondCornerVelocity U t ∧
      properUsedQ U m ρ t = firstCornerVelocity U t := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hmatch := hU.isCap.companionSupport_and_tangent_leftCut_after_affine
    ha hb hab haffine hmt ht.1 (ht.2.trans hproper)
  have hfd := hU.isCap.closedSupportDerivative_eq_supportTangent hρ hρ0 hρK
    (hregime.first_density_of_regular hproper heq) (d := 0) (by simp) ht.1 ht.2
  have hgd := hU.isCap_properLeftCompanion.closedSupportDerivative_eq_supportTangent
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2)
    (hU.proper_leftCompanion_density_of_regular hproper haffine heq) (d := Real.pi / 2)
    (Ioo_subset_Ioo le_rfl (add_halves _).le) ht.1 (ht.2.trans hproper)
  rw [properUsedP, properUsedQ, supportP, supportQ, hfd, hgd, hmatch.1, hmatch.2]
  simp only [angleSupport_eq_imported_supp, supportTangent, secondCornerVelocity,
    firstCornerVelocity, add_zero]
  constructor <;> ring

/-- Both initial reflected values are computed at actual supporting
endpoints. The second value contains the whole terminal atom. -/
theorem IsJointCapMaximizer.properReflected_terminal_impulse_of_tail_regime :
    properReflectedP U m ρ (Real.pi / 2 - α) =
        Analysis.initialFloorCircleP (terminalReflectedSpan U α)
          (terminalReflectedHeight U α - 1) (Real.pi / 2 - α) ∧
      properReflectedQ U ρ (Real.pi / 2 - α) =
        Analysis.initialFloorCircleQ (terminalReflectedSpan U α)
          (terminalReflectedHeight U α - 1) (Real.pi / 2 - α) + MovingSofaOptimality.sigmaAt U α := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hmatch := hU.isCap.companionSupport_and_tangent_leftCut_after_affine ha hb hab haffine
    (by simpa [affineNormalAngle] using (hU.middle_normal_lt_terminal_companion haffine).le)
    hU.angle_pos.le hproper
  have hfd := hU.isCap.closedSupportDerivative_at_end hρ hρ0 hρK
    (hregime.first_density_of_regular hproper heq) hU.angle_pos (d := 0) (by simp)
  rw [add_zero] at hfd
  have hgd := hU.isCap_properLeftCompanion.closedSupportDerivative_eq_supportTangent
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2)
    (hU.proper_leftCompanion_density_of_regular hproper haffine heq) (d := Real.pi / 2)
    (Ioo_subset_Ioo le_rfl (add_halves _).le) hU.angle_pos.le hproper
  have hσ := MovingSofaOptimality.sigmaAt_eq_dot_sub hU.isCap.imported_isConvexBody α
  have hf := MovingSofaOptimality.dot_vplus_uvec U α
  have hg := MovingSofaOptimality.dot_vplus_uvec U (α + Real.pi / 2)
  rw [properReflectedP, properReflectedQ, sub_sub_cancel, properUsedP, properUsedQ, supportP,
    supportQ, hfd, hgd, hmatch.1, hmatch.2, supportTangent]
  simp only [hU.terminal_companion_vplus hproper haffine, angleSupport_eq_imported_supp,
    terminalReflectedHeight, terminalReflectedSpan, terminalTailPoint,
    Analysis.initialFloorCircleP, Analysis.initialFloorCircleQ, MovingSofaOptimality.dot,
    MovingSofaOptimality.uvec, MovingSofaOptimality.vvec, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at hσ hf hg ⊢
  constructor <;> linarith

end

end AmbidextrousSofa
