module

public import AmbidextrousSofa.Analysis.CapMaximum
public import AmbidextrousSofa.Analysis.CapTranslation
public import AmbidextrousSofa.Analysis.WideCap
public import AmbidextrousSofa.Analysis.Chord
public import AmbidextrousSofa.Reference.Value

@[expose] public section

/-!
# Global existence and canonicalization of full cap maxima

The reference cap supplies a concrete comparison value. Every cap of width
at least six has a strictly smaller score; every narrower cap can be
translated into one fixed compact box. A maximum in that box is therefore
a maximum over the entire original cap domain. The actual chord and height
operations then give a height-one maximizer affine on its middle window.
The sharp value of that maximum is not presumed here.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

def IsFullCapMaximizer (U : Set Plane) : Prop :=
  IsDownwardCap U ∧ ∀ V : Set Plane, IsDownwardCap V →
    capScore V (Real.pi / 2) ≤ capScore U (Real.pi / 2)

theorem IsFullCapMaximizer.isCap {U : Set Plane} (hU : IsFullCapMaximizer U) :
    IsDownwardCap U := hU.1

theorem IsFullCapMaximizer.reference_le {U : Set Plane} (hU : IsFullCapMaximizer U) :
    M / 2 ≤ capScore U (Real.pi / 2) :=
  Reference.capScore_referenceCap ▸ hU.2 _ Reference.isDownwardCap_referenceCap

theorem IsFullCapMaximizer.width_bounds {U : Set Plane} (hU : IsFullCapMaximizer U) :
    M ≤ capWidth U ∧ capWidth U < 6 :=
  hU.isCap.competitive_width_bounds (by linarith [Real.pi_pos]) le_rfl hU.reference_le

/-- Existence over all compact downward caps, with no symmetry or
regularity restriction. The final representative lies in a fixed box. -/
theorem exists_fullCapMaximizer :
    ∃ U : Set Plane, IsFullCapMaximizer U ∧ U ⊆ Icc (-3, 0) (3, 1) := by
  have hRef := Reference.isDownwardCap_referenceCap
  have hbox {V : Set Plane} (hV : IsDownwardCap V) (h : M / 2 ≤ capScore V (Real.pi / 2)) :
      centeredCap V ⊆ Icc (-3, 0) (3, 1) := centeredCap_subset_box_of_width_le hV <| by
    linarith [(hV.competitive_width_bounds (by linarith [Real.pi_pos]) le_rfl h).2]
  have hRefBox := hbox hRef Reference.capScore_referenceCap.ge
  obtain ⟨K, hK, hKB, hmax⟩ :=
    exists_capScore_max_of_compact_containment isCompact_Icc hRef.centeredCap hRefBox
  have hKRef := hmax _ hRef.centeredCap hRefBox
  rw [capScore_centeredCap hRef, Reference.capScore_referenceCap] at hKRef
  refine ⟨K, ⟨hK, fun V hV => ?_⟩, hKB⟩
  rcases le_total (capScore V (Real.pi / 2)) (M / 2) with h | h
  · exact h.trans hKRef
  · simpa [capScore_centeredCap hV] using hmax _ hV.centeredCap (hbox hV h)

theorem IsFullCapMaximizer.of_score_le {U V : Set Plane}
    (hU : IsFullCapMaximizer U) (hV : IsDownwardCap V)
    (hscore : capScore U (Real.pi / 2) ≤ capScore V (Real.pi / 2)) :
    IsFullCapMaximizer V :=
  ⟨hV, fun W hW => (hU.2 W hW).trans hscore⟩

/-- Every global cap maximum admits the actual middle-chord and height
reduction, still at the global maximum and with its original projection. -/
theorem IsFullCapMaximizer.exists_heightOne_affine_middle
    {U : Set Plane} (hU : IsFullCapMaximizer U) :
    ∃ V : Set Plane, IsFullCapMaximizer V ∧
      horizontalProjection V = horizontalProjection U ∧ capHeight V = 1 ∧
      capScore V (Real.pi / 2) = capScore U (Real.pi / 2) ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V),
        capRoof V x = m * x + c := by
  obtain ⟨V, hV, hproj, hheight, hscore, m, c, haffine⟩ :=
    hU.isCap.exists_heightOne_affine_middle (by linarith [hU.width_bounds.1, one_lt_M])
      (by positivity) le_rfl
  refine ⟨V, hU.of_score_le hV hscore, hproj, hheight,
    le_antisymm (hU.2 V hV) hscore, m, c, ?_⟩
  simpa only [horizontalLeft, horizontalRight, hproj] using haffine

end AmbidextrousSofa
