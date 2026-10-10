import AmbidextrousSofa.Analysis.CapMaximum
import AmbidextrousSofa.Analysis.CapTranslation
import AmbidextrousSofa.Analysis.WideCap
import AmbidextrousSofa.Analysis.Chord
import AmbidextrousSofa.Reference.Value

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
    M / 2 ≤ capScore U (Real.pi / 2) := by
  have h := hU.2 Reference.referenceCap Reference.isDownwardCap_referenceCap
  rwa [Reference.capScore_referenceCap] at h

theorem IsFullCapMaximizer.width_bounds {U : Set Plane} (hU : IsFullCapMaximizer U) :
    M ≤ capWidth U ∧ capWidth U < 6 :=
  hU.isCap.competitive_width_bounds (by linarith [Real.pi_pos]) le_rfl hU.reference_le

/-- Existence over all compact downward caps, with no symmetry or
regularity restriction. The final representative lies in a fixed box. -/
theorem exists_fullCapMaximizer :
    ∃ U : Set Plane, IsFullCapMaximizer U ∧ U ⊆ Icc (-3, 0) (3, 1) := by
  have hRef := Reference.isDownwardCap_referenceCap
  have hRefScore : M / 2 ≤ capScore Reference.referenceCap (Real.pi / 2) :=
    Reference.capScore_referenceCap.ge
  have hRefWidth := (hRef.competitive_width_bounds
    (by linarith [Real.pi_pos]) le_rfl hRefScore).2
  have hRefBox : centeredCap Reference.referenceCap ⊆ Icc (-3, 0) (3, 1) :=
    centeredCap_subset_box_of_width_le hRef (by linarith)
  obtain ⟨K, hK, hKB, hmax⟩ := exists_capScore_max_of_compact_containment
    (isCompact_Icc : IsCompact (Icc (-3, 0) (3, 1))) hRef.centeredCap hRefBox
  have hKRef : M / 2 ≤ capScore K (Real.pi / 2) := by
    have h := hmax _ hRef.centeredCap hRefBox
    rwa [capScore_centeredCap hRef, Reference.capScore_referenceCap] at h
  refine ⟨K, ⟨hK, ?_⟩, hKB⟩
  intro V hV
  by_cases hwide : 6 ≤ capWidth V
  · exact (hV.capScore_lt_half_M_of_six_le_width
      (by linarith [Real.pi_pos]) le_rfl hwide).le.trans hKRef
  · have hVbox : centeredCap V ⊆ Icc (-3, 0) (3, 1) :=
      centeredCap_subset_box_of_width_le hV (by linarith [lt_of_not_ge hwide])
    have h := hmax _ hV.centeredCap hVbox
    rwa [capScore_centeredCap hV] at h

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
  have hwidth : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  obtain ⟨V, hV, hproj, hheight, hscore, m, c, haffine⟩ :=
    hU.isCap.exists_heightOne_affine_middle hwidth (by linarith [Real.pi_pos]) le_rfl
  have hleft : horizontalLeft V = horizontalLeft U := by unfold horizontalLeft; rw [hproj]
  have hright : horizontalRight V = horizontalRight U := by unfold horizontalRight; rw [hproj]
  refine ⟨V, hU.of_score_le hV hscore, hproj, hheight,
    le_antisymm (hU.2 V hV) hscore, m, c, ?_⟩
  simpa only [hleft, hright] using haffine

theorem exists_canonical_fullCapMaximizer :
    ∃ U : Set Plane, IsFullCapMaximizer U ∧ capHeight U = 1 ∧
      M ≤ capWidth U ∧ capWidth U < 6 ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
        capRoof U x = m * x + c := by
  obtain ⟨U, hU, _⟩ := exists_fullCapMaximizer
  obtain ⟨V, hV, _, hheight, _, haffine⟩ := hU.exists_heightOne_affine_middle
  exact ⟨V, hV, hheight, hV.width_bounds.1, hV.width_bounds.2, haffine⟩

end AmbidextrousSofa
