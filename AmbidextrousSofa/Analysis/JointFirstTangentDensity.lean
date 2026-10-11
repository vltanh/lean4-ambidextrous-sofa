module

public import AmbidextrousSofa.Analysis.JointBranchProjection
public import AmbidextrousSofa.Analysis.JointBranchDensity
public import AmbidextrousSofa.Analysis.JointSourcePositive
public import AmbidextrousSofa.Analysis.TangencyMeasurable

@[expose] public section

/-!
# The actual first tangent occupation density

The first branch is a restriction of the common joint source measure.
Its sine-weighted graph projection is dominated by horizontal length,
so its angular density is at most the first tangent speed. The source
abscissae lie strictly in the middle window, which also proves that the
first branch has zero density wherever its actual tangent lies beyond
that window. Both statements use the Radon--Nikodym representative of
the literal branch.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c K : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (hρ : Measurable ρ) (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_first_tangent_source_graph :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      z.2 = (firstTangency target z.1).1 :=
  (J.ae_first_tangent_source_contact hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK
    heq).mono fun _ hz => congrArg Prod.fst hz.2

include hTarget hheight m haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_first_tangent_density_le_one_sub
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (firstTangentSource target) 0 t ≤ 1 - ρ t := by
  have hD := ((hTarget.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain hρ hρ0 hρK
    heq).filter_mono (ae_mono (Measure.restrict_mono_ae
      (ae_regularCornerDomain_of_mem_quarter m)))).mono fun t h => h.1
  filter_upwards [J.ae_sourceBranchDensity_mul_sin_le_abs_deriv_on hTarget hheight haffine
    hTargetBox hleft hright heq (measurableSet_firstTangentSource hTarget.isCap.isCompact) 0
    hTarget.isCap.measurable_firstTangency_fst
    (by simpa only [sub_zero] using J.ae_first_tangent_source_graph hTarget hheight haffine
          hTargetBox hleft hright hρ hρ0 hρK heq) measurableSet_Ioo hD, hunit,
    ae_restrict_mem measurableSet_Ioo] with t hb hu ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  rw [add_zero, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hu) hs.le)] at hb
  exact (mul_le_mul_iff_left₀ hs).mp hb

include hTarget hheight haffine hTargetBox hleft hright hρ hρ0 hρK heq in
theorem ae_first_tangent_density_eq_zero_after_middle {C : ℝ}
    (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C) :
    ∀ᵐ t ∂volume, C ≤ (firstTangency target t).1 →
      J.sourceBranchDensity (firstTangentSource target) 0 t = 0 := by
  refine J.ae_sourceBranchDensity_eq_zero_on (E := _ ⁻¹' Ici C) hTarget hheight haffine hTargetBox
    hleft hright heq (measurableSet_Ici.preimage hTarget.isCap.measurable_firstTangency_fst) ?_
  filter_upwards [J.ae_first_tangent_source_graph hTarget hheight haffine hTargetBox hleft hright
    hρ hρ0 hρK heq, ae_restrict_of_ae (J.ae_spatial_mem_open_middle hTarget.isCap)] with z hg hm
  rw [mem_preimage, mem_Ici, sub_zero, ← hg, not_le]
  linarith [hm.2, show capWidth target = 4 * C by unfold capWidth; linarith]

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
