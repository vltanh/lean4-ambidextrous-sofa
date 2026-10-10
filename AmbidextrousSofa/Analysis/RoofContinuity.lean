import AmbidextrousSofa.Analysis.Chord

/-!
# Continuity of an actual cap roof on its whole projection

Concavity gives continuity in the projection interior. At either endpoint
the full endpoint chord is a continuous lower support that agrees with the
roof. Compactness supplies the opposite, upper semicontinuous bound. The
argument includes zero-width caps and does not assume endpoint continuity.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem continuousWithinAt_of_upperSemicontinuousWithinAt_of_lower_support
    {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ}
    (hupper : UpperSemicontinuousWithinAt f s x)
    (hg : ContinuousAt g x) (hvalue : g x = f x)
    (hlower : ∀ y ∈ s, g y ≤ f y) : ContinuousWithinAt f s x := by
  apply continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr
  refine ⟨?_, hupper⟩
  intro c hc
  have hcg : c < g x := by rw [hvalue]; exact hc
  have hglower := hg.continuousWithinAt.lowerSemicontinuousWithinAt
  filter_upwards [hglower c hcg, self_mem_nhdsWithin] with y hy hys
  exact hy.trans_le (hlower y hys)

theorem IsDownwardCap.continuousOn_capRoof_Icc {U : Set Plane}
    (hU : IsDownwardCap U) :
    ContinuousOn (capRoof U) (Icc (horizontalLeft U) (horizontalRight U)) := by
  let l := horizontalLeft U
  let r := horizontalRight U
  have hlr : l ≤ r := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rcases eq_or_lt_of_le hlr with heq | hlt
  · change ContinuousOn (capRoof U) (Icc l r)
    rw [heq, Icc_self]
    exact continuousOn_singleton _ _
  · have hproj : horizontalProjection U = Icc l r :=
      horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex
    have hconcave : ConcaveOn ℝ (Icc l r) (capRoof U) := by
      rw [← hproj]
      exact hU.concaveOn_capRoof
    have hl : l ∈ horizontalProjection U := horizontalLeft_mem hU.nonempty hU.isCompact
    have hr : r ∈ horizontalProjection U := horizontalRight_mem hU.nonempty hU.isCompact
    have hbelow : ∀ x ∈ Icc l r, roofChord (capRoof U) l r x ≤ capRoof U x :=
      fun x hx => hU.concaveOn_capRoof.roofChord_le hl hr hlt hx
    have hleft : ContinuousWithinAt (capRoof U) (Icc l r) l :=
      continuousWithinAt_of_upperSemicontinuousWithinAt_of_lower_support
        ((hU.upperSemicontinuous_capRoof l).upperSemicontinuousWithinAt (Icc l r))
        (continuous_roofChord _ _ _).continuousAt (roofChord_left _ _ _) hbelow
    have hright : ContinuousWithinAt (capRoof U) (Icc l r) r :=
      continuousWithinAt_of_upperSemicontinuousWithinAt_of_lower_support
        ((hU.upperSemicontinuous_capRoof r).upperSemicontinuousWithinAt (Icc l r))
        (continuous_roofChord _ _ _).continuousAt (roofChord_right _ hlt) hbelow
    exact hconcave.continuousOn_Icc hlt
      ((continuousWithinAt_Icc_iff_Ici hlt).mp hleft)
      ((continuousWithinAt_Icc_iff_Iic hlt).mp hright)

/-- Relative continuity includes both actual projection endpoints. -/
theorem IsDownwardCap.continuousOn_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) : ContinuousOn (capRoof U) (horizontalProjection U) := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact hU.continuousOn_capRoof_Icc

end AmbidextrousSofa
