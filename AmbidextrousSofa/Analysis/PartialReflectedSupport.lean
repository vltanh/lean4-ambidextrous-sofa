import AmbidextrousSofa.Analysis.PartialWingSupport
import AmbidextrousSofa.Analysis.SupportArcCalculus
import AmbidextrousSofa.Analysis.TiltedSupportPair
import AmbidextrousSofa.Analysis.TiltedInitialEnergy

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

def properUsedP (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  supportP (closedSupportDerivative U ρ 0)
    (fun t => angleSupport (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (t + Real.pi / 2))

def properUsedQ (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  supportQ
    (closedSupportDerivative (leftCompanionCap U (horizontalLeft U + capWidth U / 4))
      (leftCompanionWingDensity m ρ) (Real.pi / 2)) (angleSupport U)

def properReflectedP (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -properUsedQ U m ρ (Real.pi / 2 - r)

def properReflectedQ (U : Set Plane) (m : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : ℝ :=
  -properUsedP U m ρ (Real.pi / 2 - r)

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

theorem IsJointCapMaximizer.properUsed_momenta_absolutelyContinuous
    {U : Set Plane} {α m K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) :
    AbsolutelyContinuousOnInterval (properUsedP U m ρ) 0 α ∧
      AbsolutelyContinuousOnInterval (properUsedQ U m ρ) 0 α := by
  have hV := hU.isCap_properLeftCompanion
  have hf := hU.isCap.absolutelyContinuousOnInterval_angleSupport 0 α
  have hg := hV.absolutelyContinuousOnInterval_angleSupport_shift 0 α (Real.pi / 2)
  have hfD := hU.isCap.absolutelyContinuousOnInterval_closedSupportDerivative
    hρ hρ0 hρK 0 α 0
  have hgD := hV.absolutelyContinuousOnInterval_closedSupportDerivative
    (measurable_leftCompanionWingDensity hρ m)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).1)
    (fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).2) 0 α (Real.pi / 2)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) 0 α :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ⟨(hfD.sub hg).add hc, (hgD.add hf).sub hc⟩

theorem IsJointCapMaximizer.properUsed_momenta_ae_derivatives
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) α),
      HasDerivAt (properUsedP U m ρ) (ρ t - 1 - properUsedQ U m ρ t) t ∧
      HasDerivAt (properUsedQ U m ρ)
        (leftCompanionWingDensity m ρ (t + Real.pi / 2) - 1 + properUsedP U m ρ t) t := by
  have hV := hU.isCap_properLeftCompanion
  have hfirst := hU.proper_first_density_of_regular hLargest hproper hheight haffine heq
  have hsecond := hU.proper_leftCompanion_density_of_regular hproper haffine heq
  have hσ := measurable_leftCompanionWingDensity hρ m
  have hσ0 := fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).1
  have hσK := fun t => (leftCompanionWingDensity_bounds hρ0 hρK t).2
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    hU.isCap.ae_hasDerivAt_closedSupportDerivative hρ hρ0 hρK hU.angle_pos.le 0,
    hV.ae_hasDerivAt_closedSupportDerivative hσ hσ0 hσK hU.angle_pos.le (Real.pi / 2)]
    with t ht hfDD hgDD
  have hdf := hU.isCap.hasDerivAt_angleSupport_of_open_arc hρ hρ0 hρK hfirst Subset.rfl ht
  have hdg := hV.hasDerivAt_shiftedSupport_of_open_density hσ hσ0 hσK hsecond
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith only [hs.2]⟩)
    ⟨ht.1, ht.2.trans hproper⟩
  simp only [add_zero] at hfDD
  constructor
  · apply ((hfDD.sub hdg).add_const 1).congr_deriv
    dsimp only [properUsedQ, supportQ]
    ring
  · apply ((hgDD.add hdf).sub_const 1).congr_deriv
    dsimp only [properUsedP, supportP]
    ring

theorem IsJointCapMaximizer.properReflected_momenta_absolutelyContinuous
    {U : Set Plane} {α m K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K) :
    AbsolutelyContinuousOnInterval (properReflectedP U m ρ) (Real.pi / 2 - α) (Real.pi / 2) ∧
      AbsolutelyContinuousOnInterval (properReflectedQ U m ρ) (Real.pi / 2 - α) (Real.pi / 2) := by
  have h := hU.properUsed_momenta_absolutelyContinuous (m := m) hρ hρ0 hρK
  constructor
  · simpa only [sub_zero, properReflectedP] using
      (absolutelyContinuousOnInterval_comp_const_sub h.2 hU.angle_pos.le (Real.pi / 2)).neg
  · simpa only [sub_zero, properReflectedQ] using
      (absolutelyContinuousOnInterval_comp_const_sub h.1 hU.angle_pos.le (Real.pi / 2)).neg

theorem IsJointCapMaximizer.properReflected_momenta_ae_derivatives
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    ∀ᵐ r ∂volume.restrict (Ioo (Real.pi / 2 - α) (Real.pi / 2)),
      HasDerivAt (properReflectedP U m ρ)
        (properReflectedFirstDensity m ρ r - 1 - properReflectedQ U m ρ r) r ∧
      HasDerivAt (properReflectedQ U m ρ)
        (properReflectedSecondDensity ρ r - 1 + properReflectedP U m ρ r) r := by
  have h := hU.properUsed_momenta_ae_derivatives
    hLargest hproper hheight haffine hρ hρ0 hρK heq
  have hp := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2) (h.mono (fun _ ht => ht.1))
  have hq := ae_hasDerivAt_comp_const_sub (c := Real.pi / 2) (h.mono (fun _ ht => ht.2))
  simp only [sub_zero] at hp hq
  filter_upwards [hp, hq] with r hp hq
  constructor
  · apply hq.neg.congr_deriv
    dsimp only [properReflectedFirstDensity, properReflectedQ]
    ring
  · apply hp.neg.congr_deriv
    dsimp only [properReflectedSecondDensity, properReflectedP]
    ring

theorem IsJointCapMaximizer.properUsed_momenta_eq_actual_after_affine
    {U : Set Plane} {α m c K t : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t)))
    (ht : t ∈ Ico (0 : ℝ) α) (hmt : Real.arctan m ≤ t) :
    properUsedP U m ρ t = -secondCornerVelocity U t ∧
      properUsedQ U m ρ t = firstCornerVelocity U t := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hmatch := hU.isCap.companionSupport_and_tangent_leftCut_after_affine
    ha hb hab haffine hmt ht.1 (ht.2.trans hproper)
  have hfirst := hU.proper_first_density_of_regular hLargest hproper hheight haffine heq
  have hsecond := hU.proper_leftCompanion_density_of_regular hproper haffine heq
  have hfd := hU.isCap.closedSupportDerivative_eq_supportTangent_on_arc hρ hρ0 hρK
    hfirst Subset.rfl ht.1 ht.2
  have hgd := hU.isCap_properLeftCompanion.closedSupportDerivative_eq_supportTangent
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2) hsecond
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith only [hs.2]⟩)
    ht.1 (ht.2.trans hproper)
  constructor
  · dsimp only [properUsedP, supportP]
    rw [hfd, hmatch.1]
    dsimp only [supportTangent, secondCornerVelocity, angleSupport]
    ring
  · dsimp only [properUsedQ, supportQ]
    rw [hgd, hmatch.2]
    dsimp only [supportTangent, firstCornerVelocity, angleSupport]
    ring

/-- Both initial reflected values are computed at actual supporting
endpoints. The second value contains the whole terminal atom. -/
theorem IsJointCapMaximizer.properReflected_terminal_values
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    properReflectedP U m ρ (Real.pi / 2 - α) =
        1 + (terminalReflectedHeight U α - 1) * Real.sin α - terminalReflectedSpan U α * Real.cos α ∧
      properReflectedQ U m ρ (Real.pi / 2 - α) + 1 =
        terminalReflectedSpan U α * Real.sin α +
          (terminalReflectedHeight U α - 1) * Real.cos α + Imported.sigmaAt U α := by
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints
    (show 0 < capWidth U by linarith only [hU.width_bounds.1, one_lt_M])
  have hmα : Real.arctan m ≤ α := by
    have h := hU.middle_normal_lt_terminal_companion haffine
    unfold affineNormalAngle at h
    linarith only [h]
  have hmatch := hU.isCap.companionSupport_and_tangent_leftCut_after_affine
    ha hb hab haffine hmα hU.angle_pos.le hproper
  have hfirst := hU.proper_first_density_of_regular hLargest hproper hheight haffine heq
  have hsecond := hU.proper_leftCompanion_density_of_regular hproper haffine heq
  have hfd := hU.isCap.closedSupportDerivative_at_arc_end hρ hρ0 hρK
    hfirst hU.angle_pos Subset.rfl
  have hgd := hU.isCap_properLeftCompanion.closedSupportDerivative_eq_supportTangent
    (measurable_leftCompanionWingDensity hρ m)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).1)
    (fun s => (leftCompanionWingDensity_bounds hρ0 hρK s).2) hsecond
    (d := Real.pi / 2) (by intro s hs; exact ⟨hs.1, by linarith only [hs.2]⟩)
    hU.angle_pos.le hproper
  have hcomp := hU.terminal_companion_vplus hproper haffine
  have hfs : angleSupport U α = (terminalTailPoint U α).1 * Real.cos α +
      (terminalTailPoint U α).2 * Real.sin α := (Imported.dot_vplus_uvec U α).symm
  have hgs : angleSupport U (α + Real.pi / 2) =
      -horizontalLeft U * Real.sin α + capRoof U (horizontalLeft U) * Real.cos α := by
    rw [← Imported.dot_vplus_uvec, hcomp]
    simp only [Imported.dot, Imported.uvec, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    ring
  have hgt : supportTangent U (α + Real.pi / 2) =
      -horizontalLeft U * Real.cos α - capRoof U (horizontalLeft U) * Real.sin α := by
    rw [supportTangent, hcomp]
    simp only [Imported.dot, Imported.vvec, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    ring
  have hft : Imported.dot (Imported.vminus U α) (Imported.vvec α) =
      -(terminalTailPoint U α).1 * Real.sin α +
        (terminalTailPoint U α).2 * Real.cos α - Imported.sigmaAt U α := by
    have h := Imported.sigmaAt_eq_dot_sub hU.isCap.imported_isConvexBody α
    dsimp only [Imported.dot, Imported.vvec] at h
    dsimp only [Imported.dot, Imported.vvec, terminalTailPoint]
    linarith only [h]
  constructor
  · dsimp only [properReflectedP, properUsedQ, supportQ]
    rw [sub_sub_cancel, hgd, hmatch.2, hgt, hfs]
    dsimp only [terminalReflectedHeight, terminalReflectedSpan]
    ring
  · dsimp only [properReflectedQ, properUsedP, supportP]
    rw [sub_sub_cancel, hfd, hft, hmatch.1, hgs]
    dsimp only [terminalReflectedHeight, terminalReflectedSpan]
    ring

theorem IsJointCapMaximizer.properReflected_terminal_impulse
    {U : Set Plane} {α m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    properReflectedP U m ρ (Real.pi / 2 - α) =
        Analysis.initialFloorCircleP (terminalReflectedSpan U α)
          (terminalReflectedHeight U α - 1) (Real.pi / 2 - α) ∧
      properReflectedQ U m ρ (Real.pi / 2 - α) =
        Analysis.initialFloorCircleQ (terminalReflectedSpan U α)
          (terminalReflectedHeight U α - 1) (Real.pi / 2 - α) + Imported.sigmaAt U α := by
  have h := hU.properReflected_terminal_values hLargest hproper hheight haffine hρ hρ0 hρK heq
  simp only [Analysis.initialFloorCircleP, Analysis.initialFloorCircleQ,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  exact ⟨h.1, by linarith only [h.2]⟩

end AmbidextrousSofa
