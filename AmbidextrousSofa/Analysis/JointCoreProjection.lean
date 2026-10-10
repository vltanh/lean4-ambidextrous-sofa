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

theorem sourceBranches_sine_spatial_add_le {S T : Set Plane}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : Disjoint S T) :
    ((J.sourceBranchMeasure S).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd +
      ((J.sourceBranchMeasure T).withDensity
        (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd ≤ volume := by
  rw [← Measure.map_add _ _ measurable_snd, ← withDensity_add_measure]
  change (((J.measure : Measure Plane).restrict S +
    (J.measure : Measure Plane).restrict T).withDensity
      (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd ≤ volume
  rw [← Measure.restrict_union hST hT]
  exact J.sourceBranch_sine_spatial_le (hS.union hT)

theorem sourceBranches_sine_graph_add_le {S T : Set Plane}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : Disjoint S T)
    (d e : ℝ) {X : ℝ → ℝ} (hX : Measurable X)
    (hgraphS : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    (hgraphT : ∀ᵐ z ∂J.sourceBranchMeasure T, z.2 = X (z.1 - e)) :
    ((J.sourceBranchAngular S d).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + d)))).map X +
      ((J.sourceBranchAngular T e).withDensity
        (fun t => ENNReal.ofReal (Real.sin (t + e)))).map X ≤ volume := by
  have hfirst : ((J.sourceBranchAngular S d).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + d)))).map X =
      ((J.sourceBranchMeasure S).withDensity
        (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd := by
    simpa only [sourceBranchAngular, sub_add_cancel] using
      (graph_weighted_map_eq (W := fun t => ENNReal.ofReal (Real.sin (t + d)))
        (measurable_fst.sub_const d) hX
        (Real.measurable_sin.comp (measurable_id.add_const d)).ennreal_ofReal hgraphS).symm
  have hsecond : ((J.sourceBranchAngular T e).withDensity
      (fun t => ENNReal.ofReal (Real.sin (t + e)))).map X =
      ((J.sourceBranchMeasure T).withDensity
        (fun z => ENNReal.ofReal (Real.sin z.1))).map Prod.snd := by
    simpa only [sourceBranchAngular, sub_add_cancel] using
      (graph_weighted_map_eq (W := fun t => ENNReal.ofReal (Real.sin (t + e)))
        (measurable_fst.sub_const e) hX
        (Real.measurable_sin.comp (measurable_id.add_const e)).ennreal_ofReal hgraphT).symm
  rw [hfirst, hsecond]
  exact J.sourceBranches_sine_spatial_add_le hS hT hST

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
  congr 1
  funext t
  exact (ENNReal.ofReal_mul (J.sourceBranchDensity_nonneg S d t)).symm

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem sourceBranches_density_sine_graph_add_le {S T : Set Plane}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : Disjoint S T)
    (d e : ℝ) {X : ℝ → ℝ} (hX : Measurable X)
    (hgraphS : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    (hgraphT : ∀ᵐ z ∂J.sourceBranchMeasure T, z.2 = X (z.1 - e)) :
    (volume.withDensity (fun t => ENNReal.ofReal
      (J.sourceBranchDensity S d t * Real.sin (t + d) +
        J.sourceBranchDensity T e t * Real.sin (t + e)))).map X ≤ volume := by
  let f := fun t => J.sourceBranchDensity S d t * Real.sin (t + d)
  let g := fun t => J.sourceBranchDensity T e t * Real.sin (t + e)
  have hf : Measurable f := (J.measurable_sourceBranchDensity S d).mul
    (Real.measurable_sin.comp (measurable_id.add_const d))
  have hraw := J.sourceBranches_sine_graph_add_le hS hT hST d e hX hgraphS hgraphT
  rw [J.sourceBranch_density_sine_eq hTarget hheight haffine hTargetBox hleft hright heq S d,
    J.sourceBranch_density_sine_eq hTarget hheight haffine hTargetBox hleft hright heq T e]
    at hraw
  change (volume.withDensity (fun t => ENNReal.ofReal (f t + g t))).map X ≤ volume
  calc
    _ ≤ (volume.withDensity
        ((fun t => ENNReal.ofReal (f t)) + (fun t => ENNReal.ofReal (g t)))).map X :=
      Measure.map_mono (withDensity_mono (ae_of_all volume
        (fun _ => ENNReal.ofReal_add_le))) hX
    _ = (volume.withDensity (fun t => ENNReal.ofReal (f t))).map X +
        (volume.withDensity (fun t => ENNReal.ofReal (g t))).map X := by
      rw [withDensity_add_left hf.ennreal_ofReal, Measure.map_add _ _ hX]
    _ ≤ volume := hraw

include hTarget hheight haffine hTargetBox hleft hright heq in
theorem ae_sourceBranchDensities_mul_sin_add_le_abs_deriv_on
    {S T : Set Plane} (hS : MeasurableSet S) (hT : MeasurableSet T) (hST : Disjoint S T)
    (d e : ℝ) {X XD : ℝ → ℝ} (hX : Measurable X)
    (hgraphS : ∀ᵐ z ∂J.sourceBranchMeasure S, z.2 = X (z.1 - d))
    (hgraphT : ∀ᵐ z ∂J.sourceBranchMeasure T, z.2 = X (z.1 - e))
    {E : Set ℝ} (hE : MeasurableSet E)
    (hD : ∀ᵐ t ∂volume.restrict E, HasDerivAt X (XD t) t) :
    ∀ᵐ t ∂volume.restrict E,
      J.sourceBranchDensity S d t * Real.sin (t + d) +
        J.sourceBranchDensity T e t * Real.sin (t + e) ≤ |XD t| := by
  have hfull := J.sourceBranches_density_sine_graph_add_le hTarget hheight haffine hTargetBox
    hleft hright heq hS hT hST d e hX hgraphS hgraphT
  have hrestricted : ((volume.restrict E).withDensity (fun t => ENNReal.ofReal
      (J.sourceBranchDensity S d t * Real.sin (t + d) +
        J.sourceBranchDensity T e t * Real.sin (t + e)))).map X ≤ volume := by
    rw [← restrict_withDensity hE]
    exact (Measure.map_mono Measure.restrict_le_self hX).trans hfull
  have hweight : Measurable (fun t => J.sourceBranchDensity S d t * Real.sin (t + d) +
      J.sourceBranchDensity T e t * Real.sin (t + e)) :=
    ((J.measurable_sourceBranchDensity S d).mul
      (Real.measurable_sin.comp (measurable_id.add_const d))).add
      ((J.measurable_sourceBranchDensity T e).mul
        (Real.measurable_sin.comp (measurable_id.add_const e)))
  exact ae_weight_le_abs_hasDerivAt_of_map_le_volume hE hweight.aemeasurable
    hX.aemeasurable hD hrestricted

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
  have hfirst : ∀ᵐ z ∂J.sourceBranchMeasure (firstCornerSource target),
      z.2 = X (z.1 - 0) := by
    filter_upwards [J.ae_first_corner_core_geometry hU hl hr hC hm hheight haffine hlow
      hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase] with z hz
    simpa only [sub_zero] using hz.2.1
  have hsecond : ∀ᵐ z ∂J.sourceBranchMeasure (secondCornerSource target),
      z.2 = X (z.1 - Real.pi / 2) := by
    filter_upwards [J.ae_second_corner_core_geometry hU hl hr hC hm hheight haffine hlow
      hhigh hh hρ hρ0 hρK heq hunit hleft hright hphase] with z hz
    exact hz.2.1
  have hD : ∀ᵐ t ∂volume.restrict (Ioo α η), HasDerivAt X (XD t) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (fullTiltedSupportQuarterPair_core_hasDerivAt hU hm.le haffine hρ hρ0 hρK heq
      ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hphase.second_mem.2⟩).1
  have hdisjoint : Disjoint (firstCornerSource target) (secondCornerSource target) :=
    disjoint_sourceSlices.mono inter_subset_left inter_subset_left
  have hbound := J.ae_sourceBranchDensities_mul_sin_add_le_abs_deriv_on hU hheight haffine
    hTargetBox hleft hright heq (measurableSet_firstCornerSource hU.isCap.isCompact)
    (measurableSet_secondCornerSource hU.isCap.isCompact) hdisjoint
    0 (Real.pi / 2) hX hfirst hsecond measurableSet_Ioo hD
  filter_upwards [ae_restrict_mem measurableSet_Ioo, hbound] with t ht hb
  have htq : t ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hphase.first_mem.1.trans ht.1, ht.2.trans hphase.second_mem.2⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi htq.1
    (by linarith only [htq.2, Real.pi_pos])
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [htq.1, Real.pi_pos], htq.2⟩
  have hneg : XD t < 0 := sub_neg.mpr
    ((mul_neg_of_neg_of_pos (hphase.core_signs t ht).1 hc).trans
      (mul_pos (hphase.core_signs t ht).2 hs))
  simpa only [add_zero, Real.sin_add_pi_div_two, abs_of_nonpos hneg.le, neg_sub] using hb

end ActualCore
end AngularGrid.SelectedJointSourceLimit
end AmbidextrousSofa
