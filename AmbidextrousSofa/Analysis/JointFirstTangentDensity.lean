import AmbidextrousSofa.Analysis.JointBranchProjection
import AmbidextrousSofa.Analysis.JointBranchDensity
import AmbidextrousSofa.Analysis.JointSourcePositive
import AmbidextrousSofa.Analysis.TangencyMeasurable

/-!
# The actual first tangent occupation density

The first branch is a restriction of the common joint source measure.
Its sine-weighted graph projection is dominated by horizontal length,
so its angular density is at most the first tangent speed. The source
abscissae lie strictly in the middle window, which also proves that the
first branch has zero density wherever its actual tangent lies outside
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

theorem ae_first_tangent_source_graph :
    ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      z.2 = (firstTangency target z.1).1 := by
  filter_upwards [J.ae_first_tangent_source_contact hTarget hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq] with z hz
  exact congrArg Prod.fst hz.2

theorem ae_first_tangent_density_le_one_sub
    (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (firstTangentSource target) 0 t ≤ 1 - ρ t := by
  have hDregular := (ae_restrict_iff'
    (isOpen_regularCornerDomain m).measurableSet).mp
      (hTarget.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain
        hρ hρ0 hρK heq)
  have hD : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      HasDerivAt (fun s => (firstTangency target s).1) ((1 - ρ t) * Real.sin t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (ae_regularCornerDomain_of_mem_quarter m),
      ae_restrict_of_ae hDregular] with t ht hr hd
    exact (hd (hr ht)).1
  have hgraph : ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target),
      z.2 = (firstTangency target (z.1 - 0)).1 := by
    simpa only [sub_zero] using J.ae_first_tangent_source_graph hTarget hheight haffine
      hTargetBox hleft hright hρ hρ0 hρK heq
  have hbound := J.ae_sourceBranchDensity_mul_sin_le_abs_deriv_on hTarget hheight haffine
    hTargetBox hleft hright heq (measurableSet_firstTangentSource hTarget.isCap.isCompact)
    0 hTarget.isCap.measurable_firstTangency_fst hgraph measurableSet_Ioo hD
  filter_upwards [hbound, hunit, ae_restrict_mem measurableSet_Ioo] with t hb hu ht
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith only [ht.2, Real.pi_pos])
  rw [add_zero, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hu) hs.le)] at hb
  exact (mul_le_mul_right hs).mp hb

theorem ae_first_tangent_density_eq_zero_outside_middle :
    ∀ᵐ t ∂volume,
      (firstTangency target t).1 ∉
        Ioo (horizontalLeft target + capWidth target / 4)
          (horizontalRight target - capWidth target / 4) →
        J.sourceBranchDensity (firstTangentSource target) 0 t = 0 := by
  let E : Set ℝ := {t | (firstTangency target t).1 ∉
    Ioo (horizontalLeft target + capWidth target / 4)
      (horizontalRight target - capWidth target / 4)}
  have hE : MeasurableSet E :=
    (measurableSet_Ioo.preimage hTarget.isCap.measurable_firstTangency_fst).compl
  have hz : ∀ᵐ z ∂J.sourceBranchMeasure (firstTangentSource target), z.1 - 0 ∉ E := by
    filter_upwards [J.ae_first_tangent_source_graph hTarget hheight haffine
      hTargetBox hleft hright hρ hρ0 hρK heq,
      ae_restrict_of_ae (J.ae_spatial_mem_open_middle hTarget.isCap)] with z hg hm
    simpa only [E, mem_setOf_eq, sub_zero, not_not, ← hg] using hm
  exact J.ae_sourceBranchDensity_eq_zero_on hTarget hheight haffine hTargetBox
    hleft hright heq hE hz

theorem ae_first_tangent_density_eq_zero_after_middle {C : ℝ}
    (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C) :
    ∀ᵐ t ∂volume, C ≤ (firstTangency target t).1 →
      J.sourceBranchDensity (firstTangentSource target) 0 t = 0 := by
  have hR : horizontalRight target - capWidth target / 4 = C := by
    unfold capWidth
    rw [hl, hr]
    ring
  filter_upwards [J.ae_first_tangent_density_eq_zero_outside_middle hTarget hheight haffine
    hTargetBox hleft hright hρ hρ0 hρK heq] with t ht
  intro hx
  apply ht
  intro hm
  rw [hR] at hm
  exact (not_lt_of_ge hx) hm.2

end ActualDensity
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
