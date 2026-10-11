module

public import AmbidextrousSofa.Analysis.TerminalLeftComparison
public import AmbidextrousSofa.Analysis.PartialSharpCurvatureDensity
public import AmbidextrousSofa.Analysis.TerminalTopProjection

@[expose] public section

/-!
# Actual initial data in the proper companion comparison

The left cut starts at the lesser of the original top abscissa and the
left middle endpoint. Thus its horizontal moment starts at the literal
quarter-width minus the actual left top overhang. The height and right
support derivative also retain the original low middle endpoint.

The cosine cut `73 cos² α ≤ 9` follows from the proved initial-angle
exclusion.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa

/-- These are the actual support height and one-sided derivative in
every sign of the middle slope, including the low positive-tilt start. -/
theorem IsJointCapMaximizer.leftCompanion_actual_initial_data
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    let V := leftCompanionCap U (horizontalLeft U + capWidth U / 4)
    capHeight V = capRoof U (horizontalLeft U + capWidth U / 4) ∧
      companionInitialOffset V = capWidth U / 4 - topOverhangLeft U ∧
      companionInitialDeficit V = 1 - capRoof U (horizontalLeft U + capWidth U / 4) ∧
      HasDerivWithinAt (fun t => angleSupport V (t + Real.pi / 2))
        (-(horizontalLeft U + capWidth U / 4) + topOverhangLeft U) (Ici 0) 0 := by
  intro V
  have hwidth : 0 < capWidth U := by linarith only [hU.width_bounds.1, one_lt_M]
  obtain ⟨ha, hb, hab⟩ := hU.isCap.middleChord_endpoints hwidth
  have hV := hU.isCap.leftCompanionCap ha
  -- The top point of `V` is the original top point or the cut point, whichever lies left.
  have key : capHeight V = capRoof U (horizontalLeft U + capWidth U / 4) ∧
      (MovingSofaOptimality.vplus V (Real.pi / 2)).1 =
        horizontalLeft U + capWidth U / 4 - topOverhangLeft U := by
    unfold topOverhangLeft
    rcases le_or_gt m 0 with hm | hm
    · have htop := hU.isCap.vplus_leftCompanionCap_eq_of_affine (t := Real.pi / 2) ha hb hab
        haffine (by simp) (by simpa using hm)
      have hxa := (MovingSofaOptimality.vplus_mem_edge hV.imported_isConvexBody
        (Real.pi / 2)).1.2.2
      rw [htop] at hxa ⊢
      rw [max_eq_left (sub_nonneg.2 hxa), ← top_vplus_snd_eq_capHeight, htop,
        top_vplus_snd_eq_capHeight, hheight, hU.middle_left_eq_one_of_affine_nonpos hheight hm
          haffine]
      exact ⟨rfl, by ring⟩
    · obtain ⟨hh, htop⟩ := hU.isCap.top_leftCompanionCap_of_positive_affine ha hb hab hm haffine
      set p := MovingSofaOptimality.vplus U (Real.pi / 2)
      have hp : p ∈ U := (MovingSofaOptimality.vplus_mem_edge hU.isCap.imported_isConvexBody _).1
      have := (le_capRoof (x := p.1) (y := p.2) hU.isCap.isCompact hp).trans
        (hU.isCap.capRoof_le_affine_of_affine_segment ha hb hab haffine _ ⟨p, hp, rfl⟩)
      have := hU.isCap.snd_le_capHeight (capRoof_mem hU.isCap.isCompact ha)
      have := top_vplus_snd_eq_capHeight U
      have := haffine (horizontalLeft U + capWidth U / 4) ⟨le_rfl, hab.le⟩
      have : horizontalLeft U + capWidth U / 4 ≤ p.1 := le_of_mul_le_mul_left (by linarith) hm
      rw [htop, max_eq_right (by linarith)]
      exact ⟨hh, by ring⟩
  obtain ⟨hh, hx⟩ := key
  refine ⟨hh, ?_, by rw [companionInitialDeficit, hh], ?_⟩
  · rw [companionInitialOffset, horizontalLeft_leftCompanionCap hU.isCap ha, hx]
    ring
  · exact hV.hasDerivWithinAt_companionSupport_zero.congr_deriv (by rw [hx]; ring)

theorem IsJointCapMaximizer.terminal_cosine_square_cut
    {U : Set Plane} {α : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2) : 73 * Real.cos α ^ 2 ≤ 9 :=
  terminal_cos_sq_le_of_initialAngle hU.terminal_angle_gt_arctan_eight_thirds.le hproper

end AmbidextrousSofa
