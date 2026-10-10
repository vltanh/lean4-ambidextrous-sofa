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

theorem abs_le_self_add_two_error {x e : ℝ} (he : 0 ≤ e) (hx : -e ≤ x) :
    |x| ≤ x + 2 * e := by
  apply abs_le.mpr
  constructor <;> linarith

theorem sum_weighted_abs_le_of_error {ι : Type*} [Fintype ι]
    (x e w : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hx : ∀ i, -e i ≤ x i)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∀ i, w i ≤ 1) :
    (∑ i, w i * |x i|) ≤ (∑ i, w i * x i) + 2 * ∑ i, e i := by
  calc
    _ ≤ ∑ i, (w i * x i + 2 * e i) := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_left (abs_le_self_add_two_error (he i) (hx i)) (hw0 i)
      have herr := mul_le_mul_of_nonneg_right (hw1 i) (he i)
      nlinarith
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

theorem max_self_zero_add_max_neg_eq_abs (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  by_cases hx : 0 ≤ x
  · simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), abs_of_nonneg hx, add_zero]
  · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
    simp only [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), abs_of_nonpos hx', zero_add]

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
  have hL := intervalIntegral.integral_nonneg_of_forall
    (show horizontalLeft U ≤ horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 by linarith)
    (outerDensity_nonneg U grid j)
  have hR := intervalIntegral.integral_nonneg_of_forall
    (show horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 ≤ horizontalRight U by linarith)
    (outerDensity_nonneg U grid j)
  unfold normalizedExposureDefect
  rw [finiteExposureDefect_div_eq_integrals hU]
  change _ ≤ ∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4), innerDensity U grid j x
  linarith

theorem innerSourceMass_dyadic_le {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (j : SourceIndex (dyadic level)) :
    innerSourceMass U (dyadic level) j ≤ (4 * R + 12) * mesh level := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hsource := integral_innerDensity_dyadic_le hU level j
    (show horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
      horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 by linarith)
  have hcoarse := finiteCurvatureDensity_corner_le_box hU hR hbox level j
  have hA := le_max_left
    (Real.tan (mesh level) * (|cornerSecant U level j| + Real.tan (mesh level / 2)))
    ((Real.tan (mesh level) * (|cornerSecant U level j| + Real.tan (mesh level / 2)) +
      2 * Real.tan (mesh level / 2)) / 2)
  change _ ≤ finiteCurvatureDensity (cornerSecant U level j) (mesh level) at hA
  have hhalf : Real.tan (mesh level / 2) ≤ mesh level := by
    have h := tan_le_two_mul (show mesh level / 2 ∈ Icc (0 : ℝ) (Real.pi / 4) from
      ⟨by linarith [mesh_pos level], by linarith [mesh_le_pi_div_four level, Real.pi_pos]⟩)
    linarith
  have hmax : max (2 * Real.tan (mesh level / 2) -
      (upperCurvature U {fullAngle (dyadic level) j}).toReal) 0 ≤ 2 * mesh level := by
    apply max_le
    · linarith [ENNReal.toReal_nonneg (a := upperCurvature U {fullAngle (dyadic level) j})]
    · linarith [mesh_pos level]
  change innerSourceMass U (dyadic level) j ≤ _ at hsource
  linarith

theorem sum_mesh_sources_le_pi (level : ℕ) :
    (∑ j : SourceIndex (dyadic level), mesh level) ≤ Real.pi := by
  classical
  have hfilter : Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
      fullAngle (dyadic level) j ≤ Real.pi) = Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (fullAngle_mem (dyadic level) j).2.le
  simpa only [hfilter] using sum_mesh_right_sources_le level Real.pi_pos.le

theorem sum_innerSourceMass_dyadic_le {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ) :
    (∑ j : SourceIndex (dyadic level), innerSourceMass U (dyadic level) j) ≤
      (4 * R + 12) * Real.pi := by
  calc
    _ ≤ ∑ j : SourceIndex (dyadic level), (4 * R + 12) * mesh level :=
      Finset.sum_le_sum (fun j _ => innerSourceMass_dyadic_le hU hR hbox level j)
    _ = (4 * R + 12) * ∑ j : SourceIndex (dyadic level), mesh level := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_mesh_sources_le_pi level) (by linarith)

theorem sum_cos_normalizedExposureDefect_eq_moments (U : Set Plane) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex grid, |(normal grid j).1| * normalizedExposureDefect U grid j) =
      finiteRightMoment U (normal grid) (pairList grid) none +
        finiteLeftMoment U (normal grid) (pairList grid) none := by
  rw [finiteRightMoment_eq_sum, finiteLeftMoment_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := max_self_zero_add_max_neg_eq_abs (normal grid j).1
  dsimp only [normalizedExposureDefect]
  rw [← mul_add, ← add_div, h]
  ring

theorem IsSelectedPolygon.sum_cos_abs_normalizedExposureDefect_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient) :
    (∑ j : SourceIndex (dyadic level), |(normal (dyadic level) j).1| *
      |normalizedExposureDefect U (dyadic level) j|) ≤
      finiteRightMoment U (normal (dyadic level)) (pairList (dyadic level)) none +
        finiteLeftMoment U (normal (dyadic level)) (pairList (dyadic level)) none +
          2 * ∑ j, selectionDefect target U level coefficient j := by
  have h := sum_weighted_abs_le_of_error (normalizedExposureDefect U (dyadic level))
    (selectionDefect target U level coefficient) (fun j => |(normal (dyadic level) j).1|)
    (selectionDefect_nonneg target U level hc) (hU.exposure_defect_div_ge hc)
    (fun _ => abs_nonneg _) (fun j => by
      rw [normal_eq_unitNormal]
      exact Real.abs_cos_le_one _)
  rwa [sum_cos_normalizedExposureDefect_eq_moments] at h

theorem IsSelectedPolygon.sum_abs_normalizedExposureDefect_le {target U : Set Plane}
    {a b coefficient R : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hc : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) :
    (∑ j : SourceIndex (dyadic level), |normalizedExposureDefect U (dyadic level) j|) ≤
      (4 * R + 12) * Real.pi + ∑ j, selectionDefect target U level coefficient j := by
  calc
    _ ≤ ∑ j : SourceIndex (dyadic level),
        (innerSourceMass U (dyadic level) j + selectionDefect target U level coefficient j) := by
      apply Finset.sum_le_sum
      intro j _
      have hlo := hU.exposure_defect_div_ge hc j
      have hhi := normalizedExposureDefect_le_innerSourceMass hU.isCap (dyadic level) j
      have hN := innerSourceMass_nonneg hU.isCap (dyadic level) j
      have he := selectionDefect_nonneg target U level hc j
      change -selectionDefect target U level coefficient j ≤
        normalizedExposureDefect U (dyadic level) j at hlo
      apply abs_le.mpr
      constructor <;> linarith
    _ = (∑ j : SourceIndex (dyadic level), innerSourceMass U (dyadic level) j) +
        ∑ j, selectionDefect target U level coefficient j := Finset.sum_add_distrib
    _ ≤ _ := add_le_add_right (sum_innerSourceMass_dyadic_le hU.isCap hR hbox level) _

end AngularGrid

end AmbidextrousSofa
