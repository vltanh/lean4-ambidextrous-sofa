module

public import AmbidextrousSofa.Analysis.FiniteRoofVariation
public import AmbidextrousSofa.Analysis.ErosionMoments

@[expose] public section

/-!
# Finite niche oscillation and the actual erosion moments

Adding the right and left erosion velocities gives minus the absolute
spatial slope of each wall. Thus the sum of the literal erosion moments
is the inner absolute-slope mass minus the two outer masses. Combining
the finite peak inequality with the concave-roof variation bound gives
a pointwise estimate on every sampled physical niche, including all
ties and floor segments.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem affineGraph_barrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    (barrierExpr corners terminal).affineGraph (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))) =
      finiteBarrier U normal corners terminal := by
  funext x
  simpa only [WallExpr.affineEnvelope, WallExpr.affineGraph, zero_mul, add_zero] using
    congrFun (affineEnvelope_barrier_zero U normal corners terminal (fun _ => 0)) x

theorem erosionMoments_add_eq_neg_absolute_variation [Fintype ι] (U : Set Plane)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2) (corners : List (ι × ι))
    (terminal : Option ι) :
    finiteRightMoment U normal corners terminal + finiteLeftMoment U normal corners terminal =
      -finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
        (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
        (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
        (horizontalLeft U) (horizontalRight U) (fun i => |wallSlope normal i|)
        (fun i => |wallSlope normal i|) := by
  have hv : (fun i => rightErosionVelocity normal i + leftErosionVelocity normal i) =
      fun i => -|wallSlope normal i| := by
    funext i
    rcases i with _ | i
    · simp [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope]
    · simp only [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope, abs_div,
        abs_neg, abs_of_pos (hnormal i), ← max_zero_add_max_neg_zero_eq_abs_self (normal i).1]
      ring
  rw [finiteRightMoment, finiteLeftMoment, ← finiteSourceVariation_add, hv,
    finiteSourceVariation_neg]

theorem finiteBarrier_peak_le_end_heights_and_moments [Fintype ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hinjective : Function.Injective (wallSlope normal))
    (hpoly : U = circumscription U normal) (corners : List (ι × ι)) (terminal : Option ι)
    (hwidth : 0 < capWidth U) {x : ℝ}
    (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) :
    2 * finiteBarrier U normal corners terminal x -
      finiteBarrier U normal corners terminal
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) -
      finiteBarrier U normal corners terminal
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ≤
      2 - |capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)| -
        capRoof U (horizontalLeft U) - capRoof U (horizontalRight U) +
        finiteRightMoment U normal corners terminal + finiteLeftMoment U normal corners terminal := by
  have hlr : horizontalLeft U < horizontalRight U := sub_pos.mp hwidth
  have houter := roof_outer_absSlope_integrals_le (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hinjective (H := 1)
    (show horizontalLeft U ≤ horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 by
      linarith)
    (show _ < horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 by linarith)
    (show _ ≤ horizontalRight U by linarith)
    (fun z _ => (roofExpr_eval_le _ none).trans_eq (by simp [wallSlope, roofIntercept]))
  have hroof : ∀ z ∈ Icc (horizontalLeft U) (horizontalRight U), (roofExpr (ι := ι)).affineGraph
      (wallSlope normal) (roofIntercept normal (fun i => support U (normal i))) z = capRoof U z :=
    eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  rw [hroof _ ⟨by linarith only [hlr], by linarith only [hlr]⟩,
    hroof _ ⟨by linarith only [hlr], by linarith only [hlr]⟩,
    hroof _ ⟨le_rfl, hlr.le⟩, hroof _ ⟨hlr.le, le_rfl⟩] at houter
  have hpeak := (barrierExpr corners terminal).peak_le_integral_abs_sourceSlope
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i))) hinjective
    hx.1 hx.2
  rw [affineGraph_barrier] at hpeak
  have hbalance := erosionMoments_add_eq_neg_absolute_variation U normal hnormal corners terminal
  rw [finiteSourceVariation_eq_integrals _ _ _ _ _ _ _ _ hlr.le] at hbalance
  linarith

end FinitePolygon

end AmbidextrousSofa
