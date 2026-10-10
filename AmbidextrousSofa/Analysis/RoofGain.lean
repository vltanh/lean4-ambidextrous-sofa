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
  let l := horizontalLeft U
  let r := horizontalRight U
  let a := l + (r - l) / 4
  let b := r - (r - l) / 4
  have hlr : l < r := by change 0 < r - l at hwidth; linarith
  have hla : l < a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbr : b < r := by dsimp [b]; linarith
  have hleft : horizontalLeft V = l := congrArg sInf hproj
  have hright : horizontalRight V = r := congrArg sSup hproj
  have hprojU : horizontalProjection U = Icc l r :=
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
  have hcU : ContinuousOn (capRoof U) (Icc l r) := by
    rw [← hprojU]; exact hU.continuousOn_capRoof
  have hcV : ContinuousOn (capRoof V) (Icc l r) := by
    rw [← hprojU, ← hproj]; exact hV.continuousOn_capRoof
  have hcUL := hcU.mono (Icc_subset_Icc le_rfl (hab.trans hbr.le))
  have hcVL := hcV.mono (Icc_subset_Icc le_rfl (hab.trans hbr.le))
  have hcUR := hcU.mono (Icc_subset_Icc (hla.le.trans hab) le_rfl)
  have hcVR := hcV.mono (Icc_subset_Icc (hla.le.trans hab) le_rfl)
  have hleftInt : (∫ x in l..a, capRoof U x) ≤ ∫ x in l..a, capRoof V x :=
    intervalIntegral.integral_mono_on hla.le
      (hcUL.intervalIntegrable_of_Icc hla.le)
      (hcVL.intervalIntegrable_of_Icc hla.le)
      (fun x _ => hU.capRoof_mono hV hUV x)
  have hrightInt : (∫ x in b..r, capRoof U x) ≤ ∫ x in b..r, capRoof V x :=
    intervalIntegral.integral_mono_on hbr.le
      (hcUR.intervalIntegrable_of_Icc hbr.le)
      (hcVR.intervalIntegrable_of_Icc hbr.le)
      (fun x _ => hU.capRoof_mono hV hUV x)
  have hmiddle : (∫ x in a..b, partialBarrier V α x) =
      ∫ x in a..b, partialBarrier U α x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hniche hx
  rw [hU.capScore_eq_intervalSpatialScore, hV.capScore_eq_intervalSpatialScore,
    hleft, hright]
  change (∫ x in l..a, capRoof U x) + (∫ x in b..r, capRoof U x) -
      (∫ x in a..b, partialBarrier U α x) <
    (∫ x in l..a, capRoof V x) + (∫ x in b..r, capRoof V x) -
      (∫ x in a..b, partialBarrier V α x)
  rw [hmiddle]
  rcases hx₀ with hx₀ | hx₀
  · have hstrict : (∫ x in l..a, capRoof U x) < ∫ x in l..a, capRoof V x :=
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hla hcUL hcVL (fun x _ => hU.capRoof_mono hV hUV x) ⟨x₀, hx₀, hgain⟩
    linarith
  · have hstrict : (∫ x in b..r, capRoof U x) < ∫ x in b..r, capRoof V x :=
      intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        hbr hcUR hcVR (fun x _ => hU.capRoof_mono hV hUV x) ⟨x₀, hx₀, hgain⟩
    linarith

end AmbidextrousSofa
