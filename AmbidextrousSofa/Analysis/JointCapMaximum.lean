module

public import AmbidextrousSofa.Analysis.PartialCapContinuity
public import AmbidextrousSofa.Analysis.GlobalCapMaximum

@[expose] public section

/-!
# Actual maxima over caps and terminal angles

The terminal parameter varies over the entire closed interval from `π/4`
to `π/2`. Joint continuity supplies a maximum in a compact box. The same
width bound used for the full problem applies to every one of these angles,
so horizontal translation turns that boxed maximum into a maximum over all
actual downward caps. A second compact maximum selects the largest terminal
angle among global maxima.

The chord and height operations preserve the chosen angle and the attained
score. In particular, the largest-angle choice survives canonicalization.
No sharp upper bound or terminal variational law is assumed here.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

/-- A maximum over every actual cap and every allowed terminal angle. -/
def IsJointCapMaximizer (U : Set Plane) (α : ℝ) : Prop :=
  IsDownwardCap U ∧ α ∈ Icc (Real.pi / 4) (Real.pi / 2) ∧
    ∀ V : Set Plane, ∀ β : ℝ, IsDownwardCap V →
      β ∈ Icc (Real.pi / 4) (Real.pi / 2) → capScore V β ≤ capScore U α

theorem IsJointCapMaximizer.isCap {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : IsDownwardCap U := hU.1

theorem IsJointCapMaximizer.angle_mem {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : α ∈ Icc (Real.pi / 4) (Real.pi / 2) := hU.2.1

theorem IsJointCapMaximizer.angle_pos {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : 0 < α := hU.angle_mem.1.trans_lt' (by positivity)

theorem IsJointCapMaximizer.score_le {U V : Set Plane} {α β : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsDownwardCap V)
    (hβ : β ∈ Icc (Real.pi / 4) (Real.pi / 2)) : capScore V β ≤ capScore U α :=
  hU.2.2 V β hV hβ

theorem IsJointCapMaximizer.score_le_same_angle {U V : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsDownwardCap V) :
    capScore V α ≤ capScore U α := hU.score_le hV hU.angle_mem

theorem IsJointCapMaximizer.reference_le {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : M / 2 ≤ capScore U α :=
  Reference.capScore_referenceCap.ge.trans
    (hU.score_le Reference.isDownwardCap_referenceCap ⟨by linarith [Real.pi_pos], le_rfl⟩)

theorem IsJointCapMaximizer.width_bounds {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : M ≤ capWidth U ∧ capWidth U < 6 :=
  hU.isCap.competitive_width_bounds hU.angle_mem.1 hU.angle_mem.2 hU.reference_le

theorem IsJointCapMaximizer.of_score_le {U V : Set Plane} {α β : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsDownwardCap V)
    (hβ : β ∈ Icc (Real.pi / 4) (Real.pi / 2))
    (hscore : capScore U α ≤ capScore V β) : IsJointCapMaximizer V β :=
  ⟨hV, hβ, fun _ _ hW hγ => (hU.score_le hW hγ).trans hscore⟩

/-- Extreme-value selection in the boxed cap-and-angle domain. The reference cap and the
actual wide-cap estimate remove the artificial box from the extreme-value conclusion. -/
theorem exists_jointCapMaximizer :
    ∃ U : Set Plane, ∃ α : ℝ, IsJointCapMaximizer U α ∧ U ⊆ Icc (-3, 0) (3, 1) := by
  have hB : IsCompact (Icc ((-3, 0) : Plane) (3, 1)) := isCompact_Icc
  have := isCompact_iff_compactSpace.mp (isCompact_boxedCaps hB)
  have hRef := Reference.isDownwardCap_referenceCap
  have hπ : Real.pi / 2 ∈ Icc (Real.pi / 4) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hRefW := (hRef.competitive_width_bounds hπ.1 hπ.2 Reference.capScore_referenceCap.ge).2
  have hbox {V : Set Plane} (hV : IsDownwardCap V) (hw : capWidth V < 6) :
      centeredCap V ⊆ Icc (-3, 0) (3, 1) := centeredCap_subset_box_of_width_le hV (by linarith)
  obtain ⟨z, hz⟩ := (continuous_partialCapScore_on_box hB).exists_forall_ge'
    (⟨hRef.centeredCap.toCompactCap, hbox hRef hRefW⟩, ⟨_, hπ⟩) (by simp)
  have hle {V : Set Plane} {β : ℝ} (hV : IsDownwardCap V)
      (hβ : β ∈ Icc (Real.pi / 4) (Real.pi / 2)) (hw : capWidth V < 6) :
      capScore V β ≤ capScore z.1.val.carrier z.2 :=
    (capScore_centeredCap hV β).symm.trans_le
      (hz (⟨hV.centeredCap.toCompactCap, hbox hV hw⟩, ⟨β, hβ⟩))
  refine ⟨_, _, ⟨z.1.val.isCap, z.2.2, fun V β hV hβ => ?_⟩, z.1.2⟩
  by_cases hwide : 6 ≤ capWidth V
  · exact (hV.capScore_lt_half_M_of_six_le_width hβ.1 hβ.2 hwide).le.trans
      (Reference.capScore_referenceCap.ge.trans (hle hRef hπ hRefW))
  · exact hle hV hβ (not_le.mp hwide)

/-- A compact score level set gives a largest terminal angle among all
global maximizing pairs. Every competing pair is recentered only after
its width bound has been proved. -/
theorem exists_jointCapMaximizer_largest_angle :
    ∃ U : Set Plane, ∃ α : ℝ, IsJointCapMaximizer U α ∧ U ⊆ Icc (-3, 0) (3, 1) ∧
      ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α := by
  obtain ⟨K, γ, hK, hKB⟩ := exists_jointCapMaximizer
  have hB : IsCompact (Icc ((-3, 0) : Plane) (3, 1)) := isCompact_Icc
  have := isCompact_iff_compactSpace.mp (isCompact_boxedCaps hB)
  obtain ⟨z, hz, hmax⟩ := (isClosed_eq (continuous_partialCapScore_on_box hB)
    (continuous_const (y := capScore K γ))).isCompact.exists_isMaxOn
    ⟨(⟨hK.isCap.toCompactCap, hKB⟩, ⟨γ, hK.angle_mem⟩), rfl⟩
    (continuous_subtype_val.comp continuous_snd).continuousOn
  refine ⟨_, _, hK.of_score_le z.1.val.isCap z.2.2 hz.ge, z.1.2, fun V β hV => ?_⟩
  exact isMaxOn_iff.1 hmax (⟨hV.isCap.centeredCap.toCompactCap, centeredCap_subset_box_of_width_le
    hV.isCap (by linarith [hV.width_bounds.2])⟩, ⟨β, hV.angle_mem⟩)
    ((capScore_centeredCap hV.isCap β).trans
      (le_antisymm (hK.score_le hV.isCap hV.angle_mem) (hV.score_le hK.isCap hK.angle_mem)))

/-- Chord replacement and height extrusion are literal cap operations at
the selected terminal angle, so global maximality forces score equality. -/
theorem IsJointCapMaximizer.exists_heightOne_affine_middle
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    ∃ V : Set Plane, IsJointCapMaximizer V α ∧
      horizontalProjection V = horizontalProjection U ∧ capHeight V = 1 ∧
      capScore V α = capScore U α ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V),
        capRoof V x = m * x + c := by
  obtain ⟨V, hV, hproj, hheight, hscore, m, c, haffine⟩ :=
    hU.isCap.exists_heightOne_affine_middle (by linarith [hU.width_bounds.1, one_lt_M])
      hU.angle_pos hU.angle_mem.2
  refine ⟨V, hU.of_score_le hV hU.angle_mem hscore, hproj, hheight,
    le_antisymm (hU.score_le_same_angle hV) hscore, m, c, ?_⟩
  simpa only [horizontalLeft, horizontalRight, hproj] using haffine

end AmbidextrousSofa
