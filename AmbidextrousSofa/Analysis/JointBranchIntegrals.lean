import AmbidextrousSofa.Analysis.JointBranchDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

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
  (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

theorem ae_sourceBranch_property {S : Set Plane} {d : ℝ} {P : ℝ → Prop}
    (hP : MeasurableSet {t | P t})
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, P (z.1 - d)) :
    ∀ᵐ t ∂volume, J.sourceBranchDensity S d t ≠ 0 → P t := by
  have hmap : ∀ᵐ t ∂J.sourceBranchAngular S d, P t :=
    (ae_map_iff (measurable_fst.sub_const d).aemeasurable hP).mpr hsource
  rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq]
    at hmap
  have hw := (ae_withDensity_iff (J.measurable_sourceBranchDensity S d).ennreal_ofReal).mp hmap
  filter_upwards [hw] with t ht
  intro hn
  apply ht
  intro he
  exact hn (le_antisymm (ENNReal.ofReal_eq_zero.mp he) (J.sourceBranchDensity_nonneg S d t))

theorem ae_sourceBranchDensity_mul_eq {S : Set Plane} {d : ℝ} {f g : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, f (z.1 - d) = g (z.1 - d)) :
    ∀ᵐ t ∂volume,
      J.sourceBranchDensity S d t * f t = J.sourceBranchDensity S d t * g t := by
  filter_upwards [J.ae_sourceBranch_property hTarget hheight haffine hTargetBox hleft hright
    heq (measurableSet_eq_fun hf hg) hsource] with t ht
  by_cases hn : J.sourceBranchDensity S d t = 0
  · simp only [hn, zero_mul]
  · rw [ht hn]

theorem integrable_sourceBranchDensity_mul_of_ae_eq
    {S : Set Plane} {d : ℝ} {R : Plane → ℝ} {f : ℝ → ℝ}
    (hf : Measurable f) (hR : Integrable R (J.sourceBranchMeasure S))
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, R z = f (z.1 - d)) :
    Integrable (fun t => J.sourceBranchDensity S d t * f t) volume := by
  have hcomp : Integrable (f ∘ (fun z : Plane => z.1 - d)) (J.sourceBranchMeasure S) :=
    hR.congr hsource
  have hi : Integrable f (J.sourceBranchAngular S d) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (measurable_fst.sub_const d).aemeasurable).mpr hcomp
  rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq]
    at hi
  have hw := (integrable_withDensity_iff_integrable_smul'
    (J.measurable_sourceBranchDensity S d).ennreal_ofReal
    (ae_of_all volume (fun _ => ENNReal.ofReal_lt_top))).mp hi
  apply hw.congr
  exact ae_of_all _ (fun t => by
    rw [ENNReal.toReal_ofReal (J.sourceBranchDensity_nonneg S d t), smul_eq_mul])

theorem setIntegral_sourceBranch_eq_graph
    {S : Set Plane} {d : ℝ} {X f : ℝ → ℝ} {R : Plane → ℝ}
    (hX : Measurable X) (hf : Measurable f)
    (hgraph : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    (hsource : ∀ᵐ z ∂J.sourceBranchMeasure S, R z = f (z.1 - d))
    {E : Set ℝ} (hE : MeasurableSet E) :
    (∫ z in univ ×ˢ E, R z ∂J.sourceBranchMeasure S) =
      ∫ t in X ⁻¹' E, J.sourceBranchDensity S d t * f t := by
  have hXE : MeasurableSet (X ⁻¹' E) := hX hE
  have hsets : univ ×ˢ E =ᵐ[J.sourceBranchMeasure S]
      (fun z : Plane => z.1 - d) ⁻¹' (X ⁻¹' E) := by
    filter_upwards [hgraph] with z hz
    apply propext
    simp only [mem_prod, mem_univ, true_and, mem_preimage, hz]
  calc
    _ = ∫ z in (fun z : Plane => z.1 - d) ⁻¹' (X ⁻¹' E), R z
        ∂J.sourceBranchMeasure S := setIntegral_congr_set hsets
    _ = ∫ z in (fun z : Plane => z.1 - d) ⁻¹' (X ⁻¹' E), f (z.1 - d)
        ∂J.sourceBranchMeasure S := integral_congr_ae (ae_restrict_of_ae hsource)
    _ = ∫ t in X ⁻¹' E, f t ∂J.sourceBranchAngular S d :=
      (setIntegral_map hXE hf.aestronglyMeasurable
        (measurable_fst.sub_const d).aemeasurable).symm
    _ = ∫ t in X ⁻¹' E, J.sourceBranchDensity S d t * f t := by
      rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
        setIntegral_withDensity_eq_setIntegral_toReal_smul
          (J.measurable_sourceBranchDensity S d).ennreal_ofReal
          (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) f hXE]
      apply integral_congr_ae
      exact ae_of_all _ (fun t => by
        rw [ENNReal.toReal_ofReal (J.sourceBranchDensity_nonneg S d t), smul_eq_mul])

end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
