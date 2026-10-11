module

public import AmbidextrousSofa.Analysis.PartialHorizontalCutoff
public import AmbidextrousSofa.Analysis.PositiveNicheLimit

@[expose] public section

/-!
# Positive proper-barrier length in the actual selected limit

Intersect the finite positive set with the target positive set. These
bounded indicators converge at every target positive point by the actual
rescaled barrier limit. The changing middle-window indicators converge
almost everywhere, so ordinary dominated convergence gives the lower
length estimate without asserting any convergence of zero sets.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def positiveBarrierOverlap (target U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) : ℝ → ℝ :=
  (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < partialBarrier target α x} ∩
    {x : ℝ | 0 < finiteBarrier U (normal α grid) (pairList α grid)
      (some (terminalIndex α hαL grid)) x}).indicator (fun _ => 1)

theorem measurableSet_positiveBarrier {target : Set Plane} (hTarget : IsDownwardCap target) :
    MeasurableSet (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
      {x : ℝ | 0 < partialBarrier target α x}) :=
  (measurableSet_middleHalfInterval _ _).inter (measurableSet_lt measurable_const
    (measurable_partialBarrier hTarget.isCompact (TerminalAngle.pos α) α.property.2))

theorem integral_positiveBarrierOverlap_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (grid : Finset QuarterAngle) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      positiveBarrierOverlap target U α hαL grid x) ≤
    finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
      (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) := by
  change (∫ x in Icc (horizontalLeft U + capWidth U / 4)
    (horizontalRight U - capWidth U / 4), positiveBarrierOverlap target U α hαL grid x) ≤ _
  rw [integral_Icc_eq_integral_Ioc, positiveBarrierOverlap, setIntegral_indicator
    ((measurableSet_positiveBarrier hTarget).inter (measurableSet_lt measurable_const
      (continuous_finiteBarrier U _ _ _).measurable)), setIntegral_const, smul_eq_mul, mul_one]
  exact measureReal_mono (fun x hx => ⟨hx.1, hx.2.2⟩)
    ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top).ne

/-- Uniform finite-wall convergence is used only at target points where
the niche is strictly positive. Zero-height components may disappear. -/
theorem integral_positiveBarrierOverlap_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsDownwardCap (U n)) (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => ∫ x in middleHalfInterval
      (horizontalLeft (U n)) (horizontalRight (U n)),
        positiveBarrierOverlap target (U n) α hαL (dyadic (level n)) x) atTop
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
        {x : ℝ | 0 < partialBarrier target α x}))) := by
  let P : Set ℝ := middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < partialBarrier target α x}
  have hP : MeasurableSet P := measurableSet_positiveBarrier hTarget
  have hflim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => positiveBarrierOverlap target (U n) α hαL (dyadic (level n)) x)
        atTop (𝓝 (P.indicator (fun _ => 1) x)) := by
    refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    by_cases hx : x ∈ P
    · have hxB : x ∈ Icc a b := (hTarget.projection_subset_Icc_of_box hTargetBox)
        (middleHalfInterval_subset
          (horizontalLeft_le_horizontalRight hTarget.nonempty hTarget.isCompact) hx.1)
      filter_upwards [(finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hTarget
        hlevel hbox (fun _ => hxB) tendsto_const_nhds).eventually (Ioi_mem_nhds hx.2)] with n hn
      rw [indicator_of_mem hx, positiveBarrierOverlap, indicator_of_mem]
      exact ⟨hx, hn⟩
    · filter_upwards with n
      rw [indicator_of_notMem hx, positiveBarrierOverlap, indicator_of_notMem]
      exact fun hm => hx hm.1
  have h := tendsto_setIntegral_moving_domain (fun n => measurable_const.indicator
    (hP.inter (measurableSet_lt measurable_const (continuous_finiteBarrier _ _ _ _).measurable)))
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    hflim (hHausdorff.middle_membership_ae hU hTarget) zero_le_one
    (fun n => (middleHalfInterval_subset (horizontalLeft_le_horizontalRight (hU n).nonempty
      (hU n).isCompact)).trans ((hU n).projection_subset_Icc_of_box (hbox n)))
    (fun n x _ => (norm_indicator_le_norm_self _ _).trans_eq norm_one)
  rwa [setIntegral_indicator hP, setIntegral_const, smul_eq_mul, mul_one, inter_eq_right.2
    (show P ⊆ middleHalfInterval _ _ from inter_subset_left)] at h

end PartialGrid
end AmbidextrousSofa
