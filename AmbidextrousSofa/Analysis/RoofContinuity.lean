module

public import AmbidextrousSofa.Analysis.Chord

@[expose] public section

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

theorem IsDownwardCap.continuousOn_capRoof_Icc {U : Set Plane}
    (hU : IsDownwardCap U) :
    ContinuousOn (capRoof U) (Icc (horizontalLeft U) (horizontalRight U)) := by
  rcases (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact).eq_or_lt with heq | hlt
  · rw [heq, Icc_self]
    exact continuousOn_singleton _ _
  have hbelow (x) (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U)) :=
    ConcaveOn.roofChord_le hU.concaveOn_capRoof (horizontalLeft_mem hU.nonempty hU.isCompact)
      (horizontalRight_mem hU.nonempty hU.isCompact) hlt hx
  -- At an endpoint the chord is a continuous lower support touching the roof.
  have hg := continuous_roofChord (capRoof U) (horizontalLeft U) (horizontalRight U)
  have key {x} (hx : roofChord (capRoof U) (horizontalLeft U) (horizontalRight U) x = capRoof U x) :
      ContinuousWithinAt (capRoof U) (Icc (horizontalLeft U) (horizontalRight U)) x :=
    continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr ⟨fun c hc => by
      filter_upwards [hg.continuousAt.continuousWithinAt.lowerSemicontinuousWithinAt c
        (by simpa only [hx] using hc), self_mem_nhdsWithin] with y hy hys
      exact hy.trans_le (hbelow y hys),
      hU.upperSemicontinuous_capRoof.upperSemicontinuousWithinAt _ _⟩
  exact (hU.horizontalProjection_eq_Icc ▸
    hU.concaveOn_capRoof).continuousOn_Icc hlt
    ((continuousWithinAt_Icc_iff_Ici hlt).mp (key (roofChord_left _ _ _)))
    ((continuousWithinAt_Icc_iff_Iic hlt).mp (key (roofChord_right _ hlt)))

/-- Relative continuity includes both actual projection endpoints. -/
theorem IsDownwardCap.continuousOn_capRoof {U : Set Plane}
    (hU : IsDownwardCap U) : ContinuousOn (capRoof U) (horizontalProjection U) :=
  hU.horizontalProjection_eq_Icc ▸ hU.continuousOn_capRoof_Icc

end AmbidextrousSofa
