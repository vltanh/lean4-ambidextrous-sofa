module

public import AmbidextrousSofa.Analysis.PartialEndpointPositivity
public import AmbidextrousSofa.Analysis.PartialSourceMass
public import AmbidextrousSofa.Analysis.FiniteSourceBalance

@[expose] public section

/-!
# Vanishing horizontal moment of actual proper source errors

The normalized defect uses the literal proper barrier, including the
whole terminal source. Its negative part is bounded by the actual
selection error. Both actual endpoint erosion moments vanish, hence the
absolute cosine-weighted source defect vanishes as well.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

def normalizedExposureDefect (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) (j : SourceIndex α grid) : ℝ :=
  finiteExposureDefect U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) j /
    (normal α grid j).2

theorem sum_cos_normalizedExposureDefect_eq_moments (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex α grid, |(normal α grid j).1| * normalizedExposureDefect U α hαL grid j) =
      finiteRightMoment U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) +
        finiteLeftMoment U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) := by
  rw [finiteRightMoment_eq_sum, finiteLeftMoment_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := max_self_zero_add_max_neg_eq_abs (normal α grid j).1
  dsimp only [normalizedExposureDefect]
  rw [← mul_add, ← add_div, h]
  ring

theorem IsSelectedPolygon.sum_cos_abs_normalizedExposureDefect_le {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient) :
    (∑ j : SourceIndex α (dyadic level), |(normal α (dyadic level) j).1| *
      |normalizedExposureDefect U α hαL (dyadic level) j|) ≤
      finiteRightMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) +
        finiteLeftMoment U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level))) +
          2 * ∑ j, selectionDefect target U α level coefficient j := by
  have h := sum_weighted_abs_le_of_error (normalizedExposureDefect U α hαL (dyadic level))
    (selectionDefect target U α level coefficient) (fun j => |(normal α (dyadic level) j).1|)
    (selectionDefect_nonneg target U α level hc) (hU.exposure_defect_div_ge hc)
    (fun _ => abs_nonneg _) (fun j => by
      rw [normal_eq_unitNormal]
      exact Real.abs_cos_le_one _)
  rwa [sum_cos_normalizedExposureDefect_eq_moments] at h

theorem sum_cos_abs_normalizedExposureDefect_tendsto_zero_of_canonical_maximum
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsJointCapMaximizer target α) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target α hαL a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b) :
    Tendsto (fun n => ∑ j : SourceIndex α (dyadic (level n)),
      |(normal α (dyadic (level n)) j).1| *
        |normalizedExposureDefect (U n) α hαL (dyadic (level n)) j|) atTop (𝓝 0) := by
  have hD := erosionMoments_tendsto_zero_of_canonical_maximum hTarget hheight haffine
    hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have herr := selectionDefect_sum_tendsto (α := α) hTarget.isCap (fun n => (hU n).isCap)
    hc hrate hHausdorff
  apply squeeze_zero
    (fun n => Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    (fun n => (hU n).sum_cos_abs_normalizedExposureDefect_le (hc n))
  simpa only [zero_add, mul_zero] using (hD.1.add hD.2).add (herr.const_mul 2)


end PartialGrid
end AmbidextrousSofa
