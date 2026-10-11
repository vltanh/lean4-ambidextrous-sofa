module

public import AmbidextrousSofa.Analysis.JointBranchDensity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Integrating literal source branches in their angular density

These changes of variables use the branch's actual angular marginal.
They retain arbitrary measurable spatial tests and do not assume that
the graph coordinate is injective. Injectivity is needed only later,
when the two opposing corner fluxes are pulled back together.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)
  (hac : J.angularMeasure ≪ volume)
include hac

theorem ae_sourceBranch_property {S : Set Plane} {d : ℝ} {P : ℝ → Prop}
    (hP : MeasurableSet {t | P t})
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, P (z.1 - d)) :
    ∀ᵐ t ∂volume, J.sourceBranchDensity S d t ≠ 0 → P t := by
  have hmap : ∀ᵐ t ∂J.sourceBranchAngular S d, P t :=
    (ae_map_iff (measurable_fst.sub_const d).aemeasurable hP).mpr hsource
  rw [J.sourceBranchAngular_eq_density hac,
    ae_withDensity_iff (J.measurable_sourceBranchDensity S d).ennreal_ofReal] at hmap
  filter_upwards [hmap] with t ht hn
  exact ht (ENNReal.ofReal_pos.2 ((J.sourceBranchDensity_nonneg S d t).lt_of_ne' hn)).ne'

theorem ae_sourceBranchDensity_mul_eq {S : Set Plane} {d : ℝ} {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, f (z.1 - d) = g (z.1 - d)) :
    ∀ᵐ t ∂volume,
      J.sourceBranchDensity S d t * f t = J.sourceBranchDensity S d t * g t := by
  filter_upwards [J.ae_sourceBranch_property hac (measurableSet_eq_fun hf hg) hsource] with t ht
    using mul_eq_mul_left_iff.2 (or_iff_not_imp_right.2 ht)

theorem integrable_sourceBranchDensity_mul_of_ae_eq
    {S : Set Plane} {d : ℝ} {R : Plane → ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) (hR : Integrable R (J.sourceBranchMeasure S))
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, R z = f (z.1 - d)) :
    Integrable (fun t => J.sourceBranchDensity S d t * f t) volume := by
  have hi : Integrable f (J.sourceBranchAngular S d) := (integrable_map_measure
    hf.aestronglyMeasurable (measurable_fst.sub_const d).aemeasurable).mpr (hR.congr hsource)
  rw [J.sourceBranchAngular_eq_density hac,
    integrable_withDensity_iff_integrable_smul'
      (J.measurable_sourceBranchDensity S d).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hi
  simpa only [ENNReal.toReal_ofReal (J.sourceBranchDensity_nonneg S d _), smul_eq_mul] using hi

theorem setIntegral_sourceBranch_eq_graph
    {S : Set Plane} {d : ℝ} {X f : ℝ → ℝ} {R : Plane → ℝ}
    (hX : Measurable X) (hf : Measurable f)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, R z = f (z.1 - d))
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, R z ∂J.sourceBranchMeasure S) =
      ∫ t in X ⁻¹' E, J.sourceBranchDensity S d t * f t := by
  calc
    _ = ∫ t in X ⁻¹' E, f t ∂J.sourceBranchAngular S d := by
      rw [sourceBranchAngular, setIntegral_map (hX hE) hf.aestronglyMeasurable
        (measurable_fst.sub_const d).aemeasurable]
      refine (setIntegral_congr_set ?_).trans (integral_congr_ae (ae_restrict_of_ae hsource))
      filter_upwards [hgraph] with z hz
      simp [hz]
    _ = _ := by
      rw [J.sourceBranchAngular_eq_density hac,
        setIntegral_withDensity_eq_setIntegral_toReal_smul
          (J.measurable_sourceBranchDensity S d).ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f (hX hE)]
      simp only [ENNReal.toReal_ofReal (J.sourceBranchDensity_nonneg S d _), smul_eq_mul]

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
