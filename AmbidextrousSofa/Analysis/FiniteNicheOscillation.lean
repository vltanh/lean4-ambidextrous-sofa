import AmbidextrousSofa.Analysis.FiniteRoofVariation
import AmbidextrousSofa.Analysis.ErosionMoments

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

theorem erosionVelocity_add (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2) :
    (fun i => rightErosionVelocity normal i + leftErosionVelocity normal i) =
      fun i => -|wallSlope normal i| := by
  funext i
  cases i with
  | none => simp [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope]
  | some i =>
    simp only [rightErosionVelocity, leftErosionVelocity, heightVelocity, wallSlope,
      abs_div, abs_neg, abs_of_pos (hnormal i)]
    by_cases hx : 0 ≤ (normal i).1
    · simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), neg_zero,
        zero_div, add_zero, abs_of_nonneg hx, neg_div]
    · have hx' : (normal i).1 ≤ 0 := (lt_of_not_ge hx).le
      simp only [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), neg_zero,
        zero_div, zero_add, neg_neg, abs_of_nonpos hx', neg_div]

theorem affineGraph_barrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    (barrierExpr corners terminal).affineGraph (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))) =
      finiteBarrier U normal corners terminal := by
  simpa only [WallExpr.affineEnvelope, WallExpr.affineGraph, zero_mul, add_zero] using
    affineEnvelope_barrier_zero U normal corners terminal (fun _ => 0)

theorem erosionMoments_add_eq_absolute_source_integrals [Fintype ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (corners : List (ι × ι)) (terminal : Option ι) :
    finiteRightMoment U normal corners terminal + finiteLeftMoment U normal corners terminal =
      (∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
          (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4),
        (barrierExpr corners terminal).sourceDensity (wallSlope normal)
          (barrierIntercept normal (fun i => support U (normal i)))
          (fun i => |wallSlope normal i|) x) -
      ((∫ x in horizontalLeft U..(horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4),
        (roofExpr (ι := ι)).sourceDensity (wallSlope normal)
          (roofIntercept normal (fun i => support U (normal i)))
          (fun i => |wallSlope normal i|) x) +
       ∫ x in (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)..horizontalRight U,
        (roofExpr (ι := ι)).sourceDensity (wallSlope normal)
          (roofIntercept normal (fun i => support U (normal i)))
          (fun i => |wallSlope normal i|) x) := by
  unfold finiteRightMoment finiteLeftMoment
  rw [← finiteSourceVariation_add]
  rw [erosionVelocity_add normal hnormal, finiteSourceVariation_neg,
    finiteSourceVariation_eq_integrals _ _ _ _ _ _ _ _
      (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]
  ring

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
  let l := horizontalLeft U
  let r := horizontalRight U
  let u := l + (r - l) / 4
  let v := r - (r - l) / 4
  have hlr : l < r := by simpa only [l, r, capWidth, sub_pos] using hwidth
  have hlu : l ≤ u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hvr : v ≤ r := by dsimp [v]; linarith
  have hx' : x ∈ Icc u v := hx
  have hpeak := (barrierExpr corners terminal).peak_le_integral_abs_sourceSlope
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    hinjective hx'.1 hx'.2
  rw [affineGraph_barrier] at hpeak
  have hH : ∀ z ∈ Icc l r, (roofExpr (ι := ι)).affineGraph (wallSlope normal)
      (roofIntercept normal (fun i => support U (normal i))) z ≤ 1 := by
    intro z _
    simpa only [wallSlope, roofIntercept, zero_mul, zero_add] using
      roofExpr_eval_le
        (fun i => wallSlope normal i * z + roofIntercept normal (fun j => support U (normal j)) i)
        none
  have houter := roof_outer_absSlope_integrals_le
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    hinjective hlu huv hvr hH
  have hroof := eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  change _ ≤ 2 * 1 - |roofEnvelope normal (fun i => support U (normal i)) v -
    roofEnvelope normal (fun i => support U (normal i)) u| -
    roofEnvelope normal (fun i => support U (normal i)) l -
    roofEnvelope normal (fun i => support U (normal i)) r at houter
  rw [hroof ⟨hlu.trans huv.le, hvr⟩, hroof ⟨hlu, huv.le.trans hvr⟩,
    hroof ⟨le_rfl, hlr.le⟩, hroof ⟨hlr.le, le_rfl⟩] at houter
  have hbalance := erosionMoments_add_eq_absolute_source_integrals hU normal hnormal corners terminal
  change 2 * finiteBarrier U normal corners terminal x - finiteBarrier U normal corners terminal u -
      finiteBarrier U normal corners terminal v ≤
    2 - |capRoof U v - capRoof U u| - capRoof U l - capRoof U r +
      finiteRightMoment U normal corners terminal + finiteLeftMoment U normal corners terminal
  change finiteRightMoment U normal corners terminal + finiteLeftMoment U normal corners terminal =
      (∫ z in u..v, (barrierExpr corners terminal).sourceDensity (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))) (fun i => |wallSlope normal i|) z) -
      ((∫ z in l..u, (roofExpr (ι := ι)).sourceDensity (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (fun i => |wallSlope normal i|) z) +
       ∫ z in v..r, (roofExpr (ι := ι)).sourceDensity (wallSlope normal)
        (roofIntercept normal (fun i => support U (normal i))) (fun i => |wallSlope normal i|) z)
    at hbalance
  linarith

end FinitePolygon

end AmbidextrousSofa
