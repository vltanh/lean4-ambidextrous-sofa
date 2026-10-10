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
    {x : ℝ | 0 < finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x}).indicator
      (fun _ => 1)

theorem measurable_positiveBarrierOverlap {target : Set Plane} (hTarget : IsDownwardCap target)
    (U : Set Plane) (grid : Finset QuarterAngle) :
    Measurable (positiveBarrierOverlap target U α hαL grid) := by
  apply measurable_const.indicator
  exact ((measurableSet_middleHalfInterval _ _).inter
    (measurableSet_lt measurable_const (measurable_partialBarrier hTarget.isCompact (TerminalAngle.pos α) α.property.2))).inter
    (measurableSet_lt measurable_const (continuous_finiteBarrier U _ _ _).measurable)

theorem positiveBarrierOverlap_bounds (target U : Set Plane) (grid : Finset QuarterAngle) (x : ℝ) :
    0 ≤ positiveBarrierOverlap target U α hαL grid x ∧ positiveBarrierOverlap target U α hαL grid x ≤ 1 := by
  unfold positiveBarrierOverlap
  by_cases hx : x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
      {x : ℝ | 0 < partialBarrier target α x} ∩
      {x : ℝ | 0 < finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x}
  · simp only [indicator_of_mem hx, zero_le_one, le_refl, and_self]
  · simp only [indicator_of_notMem hx, le_refl, zero_le_one, and_self]

theorem integral_positiveBarrierOverlap_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (grid : Finset QuarterAngle) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      positiveBarrierOverlap target U α hαL grid x) ≤
    finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
      (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) := by
  have hP : MeasurableSet (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
      {x : ℝ | 0 < partialBarrier target α x} ∩
      {x : ℝ | 0 < finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x}) :=
    ((measurableSet_middleHalfInterval _ _).inter
      (measurableSet_lt measurable_const (measurable_partialBarrier hTarget.isCompact (TerminalAngle.pos α) α.property.2))).inter
      (measurableSet_lt measurable_const (continuous_finiteBarrier U _ _ _).measurable)
  change (∫ x in Icc (horizontalLeft U + capWidth U / 4)
    (horizontalRight U - capWidth U / 4), positiveBarrierOverlap target U α hαL grid x) ≤ _
  rw [integral_Icc_eq_integral_Ioc, positiveBarrierOverlap, setIntegral_indicator hP,
    setIntegral_const, smul_eq_mul, mul_one]
  unfold finitePositiveLength
  apply measureReal_mono
  · exact fun x hx => ⟨hx.1, hx.2.2⟩
  · apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono inter_subset_left)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)

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
  have hP : MeasurableSet P := (measurableSet_middleHalfInterval _ _).inter
    (measurableSet_lt measurable_const (measurable_partialBarrier hTarget.isCompact (TerminalAngle.pos α) α.property.2))
  have hflim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => positiveBarrierOverlap target (U n) α hαL (dyadic (level n)) x)
        atTop (𝓝 (P.indicator (fun _ => 1) x)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ P
    · have hxB : x ∈ Icc a b := (hTarget.projection_subset_Icc_of_box hTargetBox)
        (middleHalfInterval_subset
          (horizontalLeft_le_horizontalRight hTarget.nonempty hTarget.isCompact) hx.1)
      have hN := finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hTarget hlevel hbox
        (fun _ => hxB) (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))
      have hpos := hN.eventually (Ioi_mem_nhds hx.2)
      rw [indicator_of_mem hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [hpos] with n hn
      exact (indicator_of_mem (show x ∈ P ∩ {x : ℝ | 0 < finiteBarrier (U n)
        (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))) x} from ⟨hx, hn⟩)
        (fun _ => (1 : ℝ))).symm
    · rw [indicator_of_notMem hx]
      apply tendsto_const_nhds.congr'
      apply Eventually.of_forall
      intro n
      exact (indicator_of_notMem (show x ∉ P ∩ {x : ℝ | 0 < finiteBarrier (U n)
        (normal α (dyadic (level n))) (pairList α (dyadic (level n))) (some (terminalIndex α hαL (dyadic (level n)))) x} from
        fun hm => hx hm.1) (fun _ => (1 : ℝ))).symm
  have hwindow (n : ℕ) :
      middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆ Icc a b :=
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight (hU n).nonempty
      (hU n).isCompact)).trans ((hU n).projection_subset_Icc_of_box (hbox n))
  have h := tendsto_setIntegral_moving_domain
    (fun n => measurable_positiveBarrierOverlap (α := α) (hαL := hαL) hTarget (U n) (dyadic (level n)))
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    hflim (hHausdorff.middle_membership_ae hU hTarget) zero_le_one hwindow
    (fun n x _ => by
      rw [Real.norm_of_nonneg (positiveBarrierOverlap_bounds (α := α) (hαL := hαL) target (U n) (dyadic (level n)) x).1]
      exact (positiveBarrierOverlap_bounds (α := α) (hαL := hαL) target (U n) (dyadic (level n)) x).2)
  have hIntegral :
      (∫ x in middleHalfInterval (horizontalLeft target) (horizontalRight target),
        P.indicator (fun _ => (1 : ℝ)) x) = volume.real P := by
    rw [setIntegral_indicator hP, setIntegral_const, smul_eq_mul, mul_one,
      Set.inter_eq_right.mpr (show P ⊆ middleHalfInterval
        (horizontalLeft target) (horizontalRight target) from inter_subset_left)]
  simpa only [hIntegral] using h


end PartialGrid
end AmbidextrousSofa
