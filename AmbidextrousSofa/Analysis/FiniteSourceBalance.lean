module

public import AmbidextrousSofa.Analysis.FiniteGraphGreen
public import AmbidextrousSofa.Analysis.EndpointPositivity
public import AmbidextrousSofa.Analysis.GridCounting

@[expose] public section

/-!
# Quantitative balance of actual selected finite sources

The normalized exposure defect is the literal central source length minus
the two charged outer lengths. Its negative part is bounded by the actual
selection error. The two erosion moments control its absolute horizontal
normal moment. The neighboring-wall estimate also bounds the total inner
source mass uniformly, including near the axes and top. These estimates
allow weighted source identities to pass to the prescribed maximizer
without identifying a weak source limit with graph arclength.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem sum_weighted_abs_le_of_error {ι : Type*} [Fintype ι]
    (x e w : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hx : ∀ i, -e i ≤ x i)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) :
    (∑ i, w i * |x i|) ≤ (∑ i, w i * x i) + 2 * ∑ i, e i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h : |x i| ≤ x i + 2 * e i := abs_le.mpr ⟨by linarith [hx i], by linarith [he i]⟩
  linarith [mul_le_mul_of_nonneg_left h (hw0 i), mul_le_mul_of_nonneg_right (hw1 i) (he i)]

theorem max_self_zero_add_max_neg_eq_abs (x : ℝ) : max x 0 + max (-x) 0 = |x| :=
  max_zero_add_max_neg_zero_eq_abs_self x

namespace AngularGrid

open FinitePolygon

def normalizedExposureDefect (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ :=
  finiteExposureDefect U (normal grid) (pairList grid) none j / (normal grid j).2

def innerSourceMass (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ :=
  ∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4), innerDensity U grid j x

theorem innerSourceMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) : 0 ≤ innerSourceMass U grid j := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) (innerDensity_nonneg U grid j)

theorem normalizedExposureDefect_le_innerSourceMass {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    normalizedExposureDefect U grid j ≤ innerSourceMass U grid j := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [normalizedExposureDefect, innerSourceMass, finiteExposureDefect_div_eq_integrals hU, sub_sub]
  exact sub_le_self _ (add_nonneg
    (intervalIntegral.integral_nonneg_of_forall (by linarith) (outerDensity_nonneg U grid j))
    (intervalIntegral.integral_nonneg_of_forall (by linarith) (outerDensity_nonneg U grid j)))

theorem innerSourceMass_dyadic_le {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (j : SourceIndex (dyadic level)) :
    innerSourceMass U (dyadic level) j ≤ (4 * R + 12) * mesh level := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hhalf := tan_le_two_mul (show mesh level / 2 ∈ Icc (0 : ℝ) (Real.pi / 4) from
    ⟨by linarith [mesh_pos level], by linarith [mesh_le_pi_div_four level, Real.pi_pos]⟩)
  refine (integral_innerDensity_dyadic_le hU level j (by linarith)).trans
    ((add_le_add ((le_max_left _ _).trans (finiteCurvatureDensity_corner_le_box hU hR hbox level j))
      (max_le (c := 2 * mesh level) ?_ ?_)).trans_eq (by ring))
  · linarith [ENNReal.toReal_nonneg (a := upperCurvature U {fullAngle (dyadic level) j})]
  · linarith [mesh_pos level]

theorem sum_innerSourceMass_dyadic_le {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ) :
    (∑ j : SourceIndex (dyadic level), innerSourceMass U (dyadic level) j) ≤
      (4 * R + 12) * Real.pi := by
  refine (Finset.sum_le_sum fun j _ => innerSourceMass_dyadic_le hU hR hbox level j).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  simpa only [Finset.filter_true_of_mem fun j _ => (fullAngle_mem (dyadic level) j).2.le] using
    sum_mesh_right_sources_le level Real.pi_pos.le

theorem sum_cos_normalizedExposureDefect_eq_moments (U : Set Plane) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex grid, |(normal grid j).1| * normalizedExposureDefect U grid j) =
      finiteRightMoment U (normal grid) (pairList grid) none +
        finiteLeftMoment U (normal grid) (pairList grid) none := by
  rw [finiteRightMoment_eq_sum, finiteLeftMoment_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [normalizedExposureDefect, ← mul_add, ← add_div, max_zero_add_max_neg_zero_eq_abs_self]
  ring

theorem IsSelectedPolygon.sum_cos_abs_normalizedExposureDefect_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    (∑ j : SourceIndex (dyadic level), |(normal (dyadic level) j).1| *
      |normalizedExposureDefect U (dyadic level) j|) ≤
      finiteRightMoment U (normal (dyadic level)) (pairList (dyadic level)) none +
        finiteLeftMoment U (normal (dyadic level)) (pairList (dyadic level)) none +
          2 * ∑ j, selectionDefect target U level coefficient j := by
  rw [← sum_cos_normalizedExposureDefect_eq_moments]
  exact sum_weighted_abs_le_of_error _ _ _ (selectionDefect_nonneg target U level hc)
    (hU.exposure_defect_div_ge hc) (fun _ => abs_nonneg _)
    (fun j => by rw [normal_eq_unitNormal]; exact Real.abs_cos_le_one _)

theorem IsSelectedPolygon.sum_abs_normalizedExposureDefect_le {target U : Set Plane}
    {a b coefficient R : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) :
    (∑ j : SourceIndex (dyadic level), |normalizedExposureDefect U (dyadic level) j|) ≤
      (4 * R + 12) * Real.pi + ∑ j, selectionDefect target U level coefficient j := by
  refine (Finset.sum_le_sum fun j _ => abs_le.mpr (⟨?_, ?_⟩ : _ ∧ _ ≤
    innerSourceMass U (dyadic level) j + selectionDefect target U level coefficient j)).trans ?_
  · rw [normalizedExposureDefect]
    linarith [hU.exposure_defect_div_ge hc j, innerSourceMass_nonneg hU.isCap (dyadic level) j]
  · linarith [normalizedExposureDefect_le_innerSourceMass hU.isCap (dyadic level) j,
      selectionDefect_nonneg target U level hc j]
  · rw [Finset.sum_add_distrib]
    linarith [sum_innerSourceMass_dyadic_le hU.isCap hR hbox level]

end AngularGrid

end AmbidextrousSofa
