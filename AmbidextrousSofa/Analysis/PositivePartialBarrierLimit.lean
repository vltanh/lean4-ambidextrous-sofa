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
length estimate without asserting any convergence of zero sets. Both
estimates are the general positive-overlap statements of the full-angle
niche, applied to the partial barrier.
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

theorem integral_positiveBarrierOverlap_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (grid : Finset QuarterAngle) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      positiveBarrierOverlap target U α hαL grid x) ≤
    finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
      (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) :=
  integral_positiveOverlap_le target U
    (measurable_partialBarrier hTarget.isCompact (TerminalAngle.pos α) α.property.2)
    (continuous_finiteBarrier U _ _ _)

theorem integral_positiveBarrierOverlap_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsDownwardCap (U n)) (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => ∫ x in middleHalfInterval
      (horizontalLeft (U n)) (horizontalRight (U n)),
        positiveBarrierOverlap target (U n) α hαL (dyadic (level n)) x) atTop
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
        {x : ℝ | 0 < partialBarrier target α x}))) :=
  integral_positiveOverlap_tendsto hTarget hTargetBox hU hbox hHausdorff
    (measurable_partialBarrier hTarget.isCompact (TerminalAngle.pos α) α.property.2)
    (fun _ => continuous_finiteBarrier _ _ _ _) fun _ hx =>
      finiteBarrier_dyadic_tendsto (α := α) (hαL := hαL) hHausdorff hU hTarget hlevel hbox
        (fun _ => hx) tendsto_const_nhds

end PartialGrid
end AmbidextrousSofa
