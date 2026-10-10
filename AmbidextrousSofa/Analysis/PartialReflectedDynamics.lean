import AmbidextrousSofa.Analysis.PartialReflectedControls
import AmbidextrousSofa.Analysis.CornerArcExcess

/-!
# The actual proper cap supplies the reflected arc dynamics

All differential, curvature, arm and shadowing fields are discharged
from the prescribed largest-angle maximizer and its actual curvature
density. The active arc ends at the affine cutoff. Its remaining
companion source is already identically zero almost everywhere.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

theorem IsJointCapMaximizer.properReflected_cornerArcDynamics
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hproper : α < Real.pi / 2)
    (hl : horizontalLeft U = -2 * C) (hr : horizontalRight U = 2 * C)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
    (hκ : ∀ t, ρ t ≤ sourceKappa (upperCornerVelocity U t))
    (heq : (upperCurvature U).restrict (regularProperCurvatureDomain α m) =
      (volume.restrict (regularProperCurvatureDomain α m)).withDensity
        (fun t => ENNReal.ofReal (ρ t))) :
    CornerArcDynamics (properReflectedP U m ρ) (properReflectedQ U m ρ)
      (properReflectedFirstDensity m ρ) (properReflectedSecondDensity ρ)
      (Real.pi / 2 - α) (properReflectedActiveEnd m) := by
  have hends := hU.properReflected_active_interval haffine
  have hwhole : Real.pi / 2 - α ≤ Real.pi / 2 := by linarith only [hU.angle_pos]
  have hsub : Ioo (Real.pi / 2 - α) (properReflectedActiveEnd m) ⊆
      Ioo (Real.pi / 2 - α) (Real.pi / 2) := Ioo_subset_Ioo le_rfl hends.2
  have hsubcc : uIcc (Real.pi / 2 - α) (properReflectedActiveEnd m) ⊆
      uIcc (Real.pi / 2 - α) (Real.pi / 2) := by
    rw [uIcc_of_le hends.1.le, uIcc_of_le hwhole]
    exact Icc_subset_Icc le_rfl hends.2
  have hac := hU.properReflected_momenta_absolutelyContinuous (m := m) hρ hρ0 hρK
  have hode := ae_restrict_of_ae_restrict_of_subset hsub
    (hU.properReflected_momenta_ae_derivatives
      hLargest hproper hheight haffine hρ hρ0 hρK heq)
  have hsource := ae_restrict_of_ae_restrict_of_subset hsub
    (hU.properReflected_source_controls hLargest hproper hl hr hheight haffine hρ hρ0 hρK hκ heq)
  have harms := hU.properReflected_arm_bounds hLargest hproper hheight haffine hρ hρ0 hρK heq
  refine ⟨hends.1.le, hac.1.mono hsubcc, hac.2.mono hsubcc, hode, ?_, ?_,
    fun t ht => (harms t ht).2, ?_, ?_⟩
  · filter_upwards [hsource] with t ht
    exact ⟨ht.2.2.1, ht.2.2.2.1⟩
  · exact hsource.mono (fun _ ht => ht.2.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Or.inl (harms t (Ioo_subset_Icc_self ht)).1
  · exact hsource.mono (fun _ ht => ht.2.2.2.2.1)

end AmbidextrousSofa
