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

variable {target : Set Plane} {a b C h m c K : ℝ} {ρ : ℝ → ℝ}
  (J : SelectedJointSourceLimit target a b) (H : IsTiltedFirstUnitTarget target a b C h m c ρ K)
include H

theorem ae_first_tangent_density_le_one_sub :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)),
      J.sourceBranchDensity (firstTangentSource target) 0 t ≤ 1 - ρ t := by
  have hD := ((H.hU.isCap.ae_hasDerivAt_tangency_coordinates_on_regularCornerDomain H.hρ H.hρ0
    H.hρK H.heq).filter_mono (ae_mono (Measure.restrict_mono_ae
      (ae_regularCornerDomain_of_mem_quarter m)))).mono fun t h => h.1
  filter_upwards [J.ae_sourceBranchDensity_mul_sin_le_abs_deriv_on
    (J.angularMeasure_absolutelyContinuous H)
    (measurableSet_firstTangentSource H.hU.isCap.isCompact) 0
    H.hU.isCap.measurable_tangency_coordinates.1
    (by simpa only [sub_zero] using J.ae_first_tangent_source_graph H) measurableSet_Ioo hD,
    H.hunit, ae_restrict_mem measurableSet_Ioo] with t hb hu ht
  have hs := (sin_cos_pos_of_mem_quarter ht).1
  rw [add_zero, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hu) hs.le)] at hb
  exact (mul_le_mul_iff_left₀ hs).mp hb

theorem ae_first_tangent_density_eq_zero_after_middle :
    ∀ᵐ t ∂volume, C ≤ (firstTangency target t).1 →
      J.sourceBranchDensity (firstTangentSource target) 0 t = 0 := by
  refine J.ae_sourceBranchDensity_eq_zero_on (E := _ ⁻¹' Ici C)
    (J.angularMeasure_absolutelyContinuous H)
    (measurableSet_Ici.preimage H.hU.isCap.measurable_tangency_coordinates.1) ?_
  filter_upwards [J.ae_first_tangent_source_graph H,
    ae_restrict_of_ae (J.ae_spatial_mem_open_middle H.hU.isCap)] with z hg hm
  rw [mem_preimage, mem_Ici, sub_zero, ← hg, not_le]
  exact (H.middle_eq ▸ hm).2

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
