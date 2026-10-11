module

public import AmbidextrousSofa.Analysis.TopInsertion

@[expose] public section

/-!
# Strict gain from an actual charged roof point

For nested caps with the same projection, a strict roof increase at any
point of either charged wing gives a strict score increase whenever the
whole middle barrier is unchanged. Continuity turns the pointwise strict
inequality into a genuine integral gain; no area-gain premise is used.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem IsDownwardCap.capScore_lt_of_charged_roof_gain {U V : Set Plane}
    (hU : IsDownwardCap U) (hV : IsDownwardCap V) (hUV : U ⊆ V)
    (hproj : horizontalProjection V = horizontalProjection U)
    (hwidth : 0 < capWidth U) {α x₀ : ℝ}
    (hniche : EqOn (partialBarrier V α) (partialBarrier U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)))
    (hx₀ : x₀ ∈ Icc (horizontalLeft U)
        (horizontalLeft U + capWidth U / 4) ∪
      Icc (horizontalRight U - capWidth U / 4) (horizontalRight U))
    (hgain : capRoof U x₀ < capRoof V x₀) : capScore U α < capScore V α := by
  have hleft : horizontalLeft V = horizontalLeft U := congrArg sInf hproj
  have hright : horizontalRight V = horizontalRight U := congrArg sSup hproj
  have hcU := hU.continuousOn_capRoof_Icc
  have hcV := hV.continuousOn_capRoof_Icc
  rw [hleft, hright] at hcV
  set l := horizontalLeft U
  set r := horizontalRight U
  have hw : 0 < r - l := hwidth
  have hle {c d} (hc : l ≤ c) (hcd : c ≤ d) (hd : d ≤ r) :
      (∫ x in c..d, capRoof U x) ≤ ∫ x in c..d, capRoof V x :=
    intervalIntegral.integral_mono_on hcd
      ((hcU.mono (Icc_subset_Icc hc hd)).intervalIntegrable_of_Icc hcd)
      ((hcV.mono (Icc_subset_Icc hc hd)).intervalIntegrable_of_Icc hcd)
      fun x _ => hU.capRoof_mono hV hUV x
  have hlt {c d} (hc : l ≤ c) (hcd : c < d) (hd : d ≤ r) (hx : x₀ ∈ Icc c d) :
      (∫ x in c..d, capRoof U x) < ∫ x in c..d, capRoof V x :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcd
      (hcU.mono (Icc_subset_Icc hc hd)) (hcV.mono (Icc_subset_Icc hc hd))
      (fun x _ => hU.capRoof_mono hV hUV x) ⟨x₀, hx, hgain⟩
  have hmid : (∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), partialBarrier V α x) =
      ∫ x in (l + (r - l) / 4)..(r - (r - l) / 4), partialBarrier U α x :=
    intervalIntegral.integral_congr fun x hx => hniche (by rwa [uIcc_of_le (by linarith)] at hx)
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore, hleft, hright,
    intervalSpatialScore, intervalSpatialScore, hmid]
  have := hle le_rfl (by linarith : l ≤ l + (r - l) / 4) (by linarith)
  have := hle (by linarith) (by linarith : r - (r - l) / 4 ≤ r) le_rfl
  rcases hx₀ with hx₀ | hx₀
  · linarith [hlt le_rfl (by linarith : l < l + (r - l) / 4) (by linarith) hx₀]
  · linarith [hlt (by linarith) (by linarith : r - (r - l) / 4 < r) le_rfl hx₀]

end AmbidextrousSofa
