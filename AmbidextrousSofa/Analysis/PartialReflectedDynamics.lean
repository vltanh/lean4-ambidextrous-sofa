module

public import AmbidextrousSofa.Analysis.PartialReflectedControls
public import AmbidextrousSofa.Analysis.CornerArcExcess

@[expose] public section

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

theorem IsJointCapMaximizer.properReflected_cornerArcDynamics_of_tail_regime
    {U : Set Plane} {α C m c K : ℝ} {ρ : ℝ → ℝ} (hU : IsJointCapMaximizer U α)
    (hregime : ProperTailRegime U α m)
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
    CornerArcDynamics (properReflectedP U m ρ) (properReflectedQ U ρ)
      (properReflectedFirstDensity m ρ) (properReflectedSecondDensity ρ)
      (Real.pi / 2 - α) (properReflectedActiveEnd m) := by
  have hends := hU.properReflected_active_interval haffine
  have hsub := Ioo_subset_Ioo (le_refl (Real.pi / 2 - α)) hends.2
  have hsubcc := uIcc_subset_uIcc left_mem_uIcc (mem_uIcc_of_le hends.1.le hends.2)
  have hac := hU.properReflected_momenta_absolutelyContinuous (m := m) hρ hρ0 hρK
  have hsource := ae_restrict_of_ae_restrict_of_subset hsub
    (hU.properReflected_source_controls_of_tail_regime hregime hproper hl hr hheight haffine hρ
      hρ0 hρK hκ heq)
  have harms := hU.properReflected_arm_bounds_of_tail_regime hregime hproper haffine hρ hρ0 hρK heq
  exact ⟨hends.1.le, hac.1.mono hsubcc, hac.2.mono hsubcc, ae_restrict_of_ae_restrict_of_subset hsub
    (hU.properReflected_momenta_ae_derivatives_of_tail_regime hregime hproper haffine hρ hρ0 hρK
      heq), hsource.mono fun _ ht => ⟨ht.2.2.1, ht.2.2.2.1⟩,
    hsource.mono fun _ ht => ht.2.1, fun t ht => (harms t ht).2,
    (ae_restrict_mem measurableSet_Ioo).mono fun t ht => .inl (harms t (Ioo_subset_Icc_self ht)).1,
    hsource.mono fun _ ht => ht.2.2.2.2.1⟩

end AmbidextrousSofa
