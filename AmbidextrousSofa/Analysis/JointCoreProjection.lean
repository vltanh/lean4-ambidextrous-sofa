module

public import AmbidextrousSofa.Analysis.JointBranchProjection
public import AmbidextrousSofa.Analysis.JointCoreSourceGeometry

@[expose] public section

/-!
# One horizontal budget for the two corner source branches

The two corner restrictions are disjoint parts of the same source
measure. Their sine-weighted projections are therefore added before
using horizontal domination. Transport along their common corner
graph gives a bound on the sum of their angular densities, with the
actual strictly negative core velocity on the right-hand side.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace AngularGrid.SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

section ActualDensity

variable (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
  {m c : ℝ} {ρ : ℝ → ℝ}
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem sourceBranch_density_sine_eq (S : Set Plane) (d : ℝ) :
    (J.sourceBranchAngular S d).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + d))) =
      volume.withDensity (fun t => ENNReal.ofReal
        (J.sourceBranchDensity S d t * Real.sin (t + d))) := by
  rw [J.sourceBranchAngular_eq_density hTarget hheight haffine hTargetBox hleft hright heq,
    ← withDensity_mul volume (g := fun t => ENNReal.ofReal (Real.sin (t + d)))
      (J.measurable_sourceBranchDensity S d).ennreal_ofReal
      (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal]
  exact congrArg _ (funext fun t => (ENNReal.ofReal_mul (J.sourceBranchDensity_nonneg S d t)).symm)

end ActualDensity

section ActualCore

variable (hU : IsFullCapMaximizer target) {C h m c : ℝ}
  (hl : horizontalLeft target = -2 * C) (hr : horizontalRight target = 2 * C)
  (hC : 1 / 2 < C) (hm : 0 < m) (hheight : capHeight target = 1)
  (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
    capRoof target x = m * x + c)
  (hlow : capRoof target (-C) = 1 - h) (hhigh : capRoof target C = 1) (hh : 0 < h)
  {ρ : ℝ → ℝ} {K : ℝ} (hρ : Measurable ρ)
  (hρ0 : ∀ t, 0 ≤ ρ t) (hρK : ∀ t, ρ t ≤ K)
  (heq : (upperCurvature target).restrict (regularCurvatureDomain m) =
    (volume.restrict (regularCurvatureDomain m)).withDensity (fun t => ENNReal.ofReal (ρ t)))
  (hunit : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (Real.pi / 2)), ρ t ≤ 1)
  (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
  (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)

local notation "F" => fullTiltedSupportQuarterPair hU hm.le haffine hρ hρ0 hρK heq
set_option quotPrecheck false in
local notation "Z" => innerCornerPoint (F).f (F).g
set_option quotPrecheck false in
local notation "p" => supportP (F).fD (F).g
set_option quotPrecheck false in
local notation "q" => supportQ (F).gD (F).f
set_option quotPrecheck false in
local notation "X" => (fun t => (Z t).1)
local notation "XD" => (fun t => p t * Real.cos t - q t * Real.sin t)
local notation "aZ" => J.sourceBranchDensity (firstCornerSource target) 0
local notation "aW" => J.sourceBranchDensity (secondCornerSource target) (Real.pi / 2)

include hl hr hC hheight hlow hhigh hh hunit hTargetBox hleft hright in
theorem ae_corner_source_weighted_sum_le_core_speed {α η : ℝ}
    (hphase : StrictCornerSignPhases p q (Real.pi / 2) α η) :
    ∀ᵐ t ∂volume.restrict (Ioo α η),
      aZ t * Real.sin t + aW t * Real.cos t ≤
        q t * Real.sin t - p t * Real.cos t := by
  have hX : Measurable X := (fullTiltedSupportQuarterPair_core_continuous_global
    hU hm.le haffine hρ hρ0 hρK heq).1.measurable
  have hw (S : Set Plane) (d : ℝ) :
      Measurable fun t => J.sourceBranchDensity S d t * Real.sin (t + d) :=
    (J.measurable_sourceBranchDensity S d).mul
      (Real.measurable_sin.comp (measurable_id.add_const d))
  have hsub : Ioo α η ⊆ Ioo 0 (Real.pi / 2) := fun t ht =>
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hphase.second_mem.2⟩
  -- Along the corner graph, each weighted angular density pushes forward to the
  -- weighted horizontal projection of its branch.
  have hgraph {S : Set Plane} {d : ℝ} (hS : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d)) :
      (volume.withDensity fun t =>
        ENNReal.ofReal (J.sourceBranchDensity S d t * Real.sin (t + d))).map X =
        ((J.sourceBranchMeasure S).withDensity fun z =>
          ENNReal.ofReal (Real.sin z.1)).map Prod.snd := by
    rw [← J.sourceBranch_density_sine_eq hU hheight haffine hTargetBox hleft hright heq]
    simpa only [sourceBranchAngular, sub_add_cancel] using (graph_weighted_map_eq
      (W := fun t => ENNReal.ofReal (Real.sin (t + d))) (measurable_fst.sub_const d) hX
      (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal hS).symm
  have hfirst : ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target), z.2 = X (z.1 - 0) :=
    (J.ae_first_corner_core_geometry hU hl hr hC hm hheight haffine hlow hhigh hh hρ hρ0 hρK
      heq hunit hleft hright hphase).mono fun z hz => by simpa only [sub_zero] using hz.2.1
  have hsecond := (J.ae_second_corner_core_geometry hU hl hr hC hm hheight haffine hlow hhigh
    hh hρ hρ0 hρK heq hunit hleft hright hphase).mono fun z hz => hz.2.1
  -- The two disjoint corner branches share one horizontal budget.
  have hmap : ((volume.restrict (Ioo α η)).withDensity fun t => ENNReal.ofReal
      (aZ t * Real.sin (t + 0) + aW t * Real.sin (t + Real.pi / 2))).map X ≤ volume := by
    have hT := measurableSet_secondCornerSource hU.isCap.isCompact
    have hST : Disjoint (firstCornerSource target) (secondCornerSource target) :=
      disjoint_sourceSlices.mono inter_subset_left inter_subset_left
    rw [← restrict_withDensity measurableSet_Ioo]
    calc _ ≤ (volume.withDensity ((fun t => ENNReal.ofReal (aZ t * Real.sin (t + 0))) +
          fun t => ENNReal.ofReal (aW t * Real.sin (t + Real.pi / 2)))).map X :=
        Measure.map_mono (Measure.restrict_le_self.trans
          (withDensity_mono (ae_of_all _ fun _ => ENNReal.ofReal_add_le))) hX
      _ = ((J.sourceBranchMeasure _).withDensity fun z =>
          ENNReal.ofReal (Real.sin z.1)).map Prod.snd := by
        rw [withDensity_add_left (hw _ 0).ennreal_ofReal, Measure.map_add _ _ hX, hgraph hfirst,
          hgraph hsecond, ← Measure.map_add _ _ measurable_snd, ← withDensity_add_measure]
        unfold sourceBranchMeasure
        rw [Measure.restrict_union hST hT]
      _ ≤ volume := J.sourceBranch_sine_spatial_le
        ((measurableSet_firstCornerSource hU.isCap.isCompact).union hT)
  have hD : ∀ᵐ t ∂volume.restrict (Ioo α η), HasDerivAt X (XD t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht using
      (fullTiltedSupportQuarterPair_core_hasDerivAt hU hm.le haffine hρ hρ0 hρK heq (hsub ht)).1
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_weight_le_abs_hasDerivAt_of_map_le_volume measurableSet_Ioo
      ((hw _ 0).fun_add (hw _ (Real.pi / 2))).aemeasurable hX.aemeasurable hD hmap] with t ht hb
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (hsub ht).1
    (by linarith only [(hsub ht).2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [(hsub ht).1, Real.pi_pos], (hsub ht).2⟩
  have hneg : XD t < 0 := sub_neg.mpr
    ((mul_neg_of_neg_of_pos (hphase.core_signs t ht).1 hc).trans
      (mul_pos (hphase.core_signs t ht).2 hs))
  simpa only [add_zero, Real.sin_add_pi_div_two, abs_of_nonpos hneg.le, neg_sub] using hb

end ActualCore
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
