import AmbidextrousSofa.Analysis.PartialCapContinuity
import AmbidextrousSofa.Analysis.GlobalCapMaximum

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
    (hU : IsJointCapMaximizer U α) : 0 < α := by
  linarith [hU.angle_mem.1, Real.pi_pos]

theorem IsJointCapMaximizer.score_le {U V : Set Plane} {α β : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsDownwardCap V)
    (hβ : β ∈ Icc (Real.pi / 4) (Real.pi / 2)) : capScore V β ≤ capScore U α :=
  hU.2.2 V β hV hβ

theorem IsJointCapMaximizer.score_le_same_angle {U V : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsDownwardCap V) :
    capScore V α ≤ capScore U α := hU.score_le hV hU.angle_mem

theorem IsJointCapMaximizer.reference_le {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : M / 2 ≤ capScore U α := by
  have h := hU.score_le Reference.isDownwardCap_referenceCap
    (show Real.pi / 2 ∈ Icc (Real.pi / 4) (Real.pi / 2) from
      ⟨by linarith [Real.pi_pos], le_rfl⟩)
  rwa [Reference.capScore_referenceCap] at h

theorem IsJointCapMaximizer.width_bounds {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) : M ≤ capWidth U ∧ capWidth U < 6 :=
  hU.isCap.competitive_width_bounds hU.angle_mem.1 hU.angle_mem.2 hU.reference_le

theorem IsJointCapMaximizer.of_score_le {U V : Set Plane} {α β : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsDownwardCap V)
    (hβ : β ∈ Icc (Real.pi / 4) (Real.pi / 2))
    (hscore : capScore U α ≤ capScore V β) : IsJointCapMaximizer V β :=
  ⟨hV, hβ, fun W γ hW hγ => (hU.score_le hW hγ).trans hscore⟩

theorem IsJointCapMaximizer.score_eq {U V : Set Plane} {α β : ℝ}
    (hU : IsJointCapMaximizer U α) (hV : IsJointCapMaximizer V β) :
    capScore U α = capScore V β :=
  le_antisymm (hV.score_le hU.isCap hU.angle_mem) (hU.score_le hV.isCap hV.angle_mem)

theorem IsJointCapMaximizer.isFull_of_angle_eq {U : Set Plane} {α : ℝ}
    (hU : IsJointCapMaximizer U α) (hα : α = Real.pi / 2) : IsFullCapMaximizer U := by
  subst α
  exact ⟨hU.isCap, fun V hV => hU.score_le_same_angle hV⟩

/-- Extreme-value selection in the original boxed cap-and-angle domain. -/
theorem exists_boxed_jointCapScore_max {B : Set Plane} (hB : IsCompact B)
    {V : Set Plane} (hV : IsDownwardCap V) (hVB : V ⊆ B) :
    ∃ K : Set Plane, ∃ α : ℝ, IsDownwardCap K ∧ K ⊆ B ∧
      α ∈ Icc (Real.pi / 4) (Real.pi / 2) ∧
      ∀ U : Set Plane, ∀ β : ℝ, IsDownwardCap U → U ⊆ B →
        β ∈ Icc (Real.pi / 4) (Real.pi / 2) → capScore U β ≤ capScore K α := by
  letI : CompactSpace (boxedCaps B) := isCompact_iff_compactSpace.mp (isCompact_boxedCaps hB)
  let z₀ : boxedCaps B × TerminalAngle :=
    (⟨hV.toCompactCap, hVB⟩, ⟨Real.pi / 2, by linarith [Real.pi_pos], le_rfl⟩)
  obtain ⟨z, _, hmax⟩ := (isCompact_univ : IsCompact (univ : Set
    (boxedCaps B × TerminalAngle))).exists_isMaxOn
      ⟨z₀, mem_univ z₀⟩ (continuous_partialCapScore_on_box hB).continuousOn
  refine ⟨z.1.val.carrier, z.2, z.1.val.isCap, z.1.property, z.2.property, ?_⟩
  intro U β hU hUB hβ
  exact hmax (mem_univ (⟨hU.toCompactCap, hUB⟩, (⟨β, hβ⟩ : TerminalAngle)))

/-- The reference cap and the actual wide-cap estimate remove the
artificial box from the extreme-value conclusion. -/
theorem exists_jointCapMaximizer :
    ∃ U : Set Plane, ∃ α : ℝ, IsJointCapMaximizer U α ∧ U ⊆ Icc (-3, 0) (3, 1) := by
  have hRef := Reference.isDownwardCap_referenceCap
  have hRefScore : M / 2 ≤ capScore Reference.referenceCap (Real.pi / 2) :=
    Reference.capScore_referenceCap.ge
  have hRefWidth := (hRef.competitive_width_bounds
    (by linarith [Real.pi_pos]) le_rfl hRefScore).2
  have hRefBox : centeredCap Reference.referenceCap ⊆ Icc (-3, 0) (3, 1) :=
    centeredCap_subset_box_of_width_le hRef (by linarith)
  obtain ⟨K, α, hK, hKB, hα, hmax⟩ := exists_boxed_jointCapScore_max
    (isCompact_Icc : IsCompact (Icc (-3, 0) (3, 1))) hRef.centeredCap hRefBox
  have hKRef : M / 2 ≤ capScore K α := by
    have h := hmax _ _ hRef.centeredCap hRefBox
      (show Real.pi / 2 ∈ Icc (Real.pi / 4) (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], le_rfl⟩)
    rwa [capScore_centeredCap hRef, Reference.capScore_referenceCap] at h
  refine ⟨K, α, ⟨hK, hα, ?_⟩, hKB⟩
  intro V β hV hβ
  by_cases hwide : 6 ≤ capWidth V
  · exact (hV.capScore_lt_half_M_of_six_le_width hβ.1 hβ.2 hwide).le.trans hKRef
  · have hVbox : centeredCap V ⊆ Icc (-3, 0) (3, 1) :=
      centeredCap_subset_box_of_width_le hV (by linarith [lt_of_not_ge hwide])
    have h := hmax _ β hV.centeredCap hVbox hβ
    rwa [capScore_centeredCap hV] at h

/-- A compact score level set gives a largest terminal angle among all
global maximizing pairs. Every competing pair is recentered only after
its width bound has been proved. -/
theorem exists_jointCapMaximizer_largest_angle :
    ∃ U : Set Plane, ∃ α : ℝ, IsJointCapMaximizer U α ∧ U ⊆ Icc (-3, 0) (3, 1) ∧
      ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α := by
  obtain ⟨K, γ, hK, hKB⟩ := exists_jointCapMaximizer
  let B : Set Plane := Icc (-3, 0) (3, 1)
  have hB : IsCompact B := isCompact_Icc
  letI : CompactSpace (boxedCaps B) := isCompact_iff_compactSpace.mp (isCompact_boxedCaps hB)
  let Z : Set (boxedCaps B × TerminalAngle) :=
    {p | capScore p.1.val.carrier p.2 = capScore K γ}
  have hZ : IsCompact Z :=
    (isClosed_eq (continuous_partialCapScore_on_box hB) continuous_const).isCompact
  let z₀ : boxedCaps B × TerminalAngle :=
    (⟨hK.isCap.toCompactCap, hKB⟩, ⟨γ, hK.angle_mem⟩)
  have hz₀ : z₀ ∈ Z := rfl
  have hangle : Continuous (fun p : boxedCaps B × TerminalAngle => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  obtain ⟨z, hz, hmax⟩ := hZ.exists_isMaxOn ⟨z₀, hz₀⟩ hangle.continuousOn
  have hzscore : capScore z.1.val.carrier z.2 = capScore K γ := hz
  refine ⟨z.1.val.carrier, z.2,
    hK.of_score_le z.1.val.isCap z.2.property hzscore.ge, z.1.property, ?_⟩
  intro V β hV
  have hVbox : centeredCap V ⊆ B :=
    centeredCap_subset_box_of_width_le hV.isCap (by linarith [hV.width_bounds.2])
  let w : boxedCaps B × TerminalAngle :=
    (⟨hV.isCap.centeredCap.toCompactCap, hVbox⟩, ⟨β, hV.angle_mem⟩)
  have hw : w ∈ Z := by
    change capScore (centeredCap V) β = capScore K γ
    rw [capScore_centeredCap hV.isCap]
    exact hV.score_eq hK
  exact hmax hw

/-- Chord replacement and height extrusion are literal cap operations at
the selected terminal angle, so global maximality forces score equality. -/
theorem IsJointCapMaximizer.exists_heightOne_affine_middle
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α) :
    ∃ V : Set Plane, IsJointCapMaximizer V α ∧
      horizontalProjection V = horizontalProjection U ∧ capHeight V = 1 ∧
      capScore V α = capScore U α ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft V) (horizontalRight V),
        capRoof V x = m * x + c := by
  have hwidth : 0 < capWidth U := by linarith [hU.width_bounds.1, one_lt_M]
  obtain ⟨V, hV, hproj, hheight, hscore, m, c, haffine⟩ :=
    hU.isCap.exists_heightOne_affine_middle hwidth hU.angle_pos hU.angle_mem.2
  have hleft : horizontalLeft V = horizontalLeft U := by unfold horizontalLeft; rw [hproj]
  have hright : horizontalRight V = horizontalRight U := by unfold horizontalRight; rw [hproj]
  refine ⟨V, hU.of_score_le hV hU.angle_mem hscore, hproj, hheight,
    le_antisymm (hU.score_le_same_angle hV) hscore, m, c, ?_⟩
  simpa only [hleft, hright] using haffine

/-- The actual joint maximum can be chosen canonical while retaining the
largest-angle property needed for one-sided terminal variations. -/
theorem exists_canonical_jointCapMaximizer_largest_angle :
    ∃ U : Set Plane, ∃ α : ℝ, IsJointCapMaximizer U α ∧ capHeight U = 1 ∧
      M ≤ capWidth U ∧ capWidth U < 6 ∧
      (∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α) ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
        capRoof U x = m * x + c := by
  obtain ⟨U, α, hU, _, hmax⟩ := exists_jointCapMaximizer_largest_angle
  obtain ⟨V, hV, _, hheight, _, haffine⟩ := hU.exists_heightOne_affine_middle
  exact ⟨V, α, hV, hheight, hV.width_bounds.1, hV.width_bounds.2, hmax, haffine⟩

end AmbidextrousSofa
