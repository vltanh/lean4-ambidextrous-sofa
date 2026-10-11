module

public import AmbidextrousSofa.Analysis.TerminalHistory

@[expose] public section

/-!
# A literal fixed-cap increase of terminal angle

The saturated actual support has a nonempty unvisited interval after a
proper terminal angle. Its first supports there are attained at the same
actual upper terminal-face endpoint. If the terminal face is overlong,
the historical shadow has a uniform strict gap on a compact spatial
interval. Below that interval, the fixed-point first wall decreases;
above it, the new first wall is nonpositive.

This proves an actual increase of terminal angle with the cap, projection,
middle window and partial score unchanged. The construction does not need
the outgoing zero to lie in the middle window. A largest-angle maximizer
therefore satisfies the terminal face-width bound as soon as its actual
corner lies before its shifted upper endpoint.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The used-support representation itself supplies a short fixed-vertex
first-support tail, for every sign of the middle slope. -/
theorem IsJointCapMaximizer.exists_fixed_terminal_support_interval
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∃ β ∈ Ioo α (Real.pi / 2), ∀ t ∈ Icc α β,
      angleSupport U t = coordDot (terminalTailPoint U α) (unitNormal t) := by
  obtain ⟨β, hβ, hgap⟩ : ∃ β ∈ Ioo α (Real.pi / 2), affineNormalAngle m ∉ Ioo α β := by
    by_cases h : α < affineNormalAngle m
    · obtain ⟨β, hαβ, hβ⟩ := exists_between (lt_min hαL h)
      exact ⟨β, ⟨hαβ, hβ.trans_le (min_le_left _ _)⟩,
        fun hm => lt_asymm (hβ.trans_le (min_le_right _ _)) hm.2⟩
    · obtain ⟨β, hβ⟩ := exists_between hαL
      exact ⟨β, hβ, fun hm => h hm.1⟩
  have h := hU.support_vertices_first_unused_gap haffine le_rfl hβ.2.le hβ.1 hgap
  exact ⟨β, hβ, fun t ht => by rw [terminalTailPoint, h.1]; exact h.2.1 t ht⟩

/-- The actual new first walls are dominated by the actual old history
on a whole nonempty angular interval. The compact historical-gap interval
is allowed to extend outside the prescribed spatial window. -/
theorem IsDownwardCap.exists_right_wall_interval_of_overlong_facet
    {U : Set Plane} (hU : IsDownwardCap U) {α β₀ l r : ℝ}
    (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) (hαL : α < Real.pi / 2)
    (hβ₀ : β₀ ∈ Ioo α (Real.pi / 2))
    (hsupport : ∀ t ∈ Icc α β₀,
      angleSupport U t = coordDot (terminalTailPoint U α) (unitNormal t))
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α)
    (hOld : ∀ x ∈ Icc l r, firstWall U α x ≤ sweptNiche U α x) :
    ∃ β ∈ Ioo α (Real.pi / 2), ∀ t ∈ Icc α β, ∀ x ∈ Icc l r,
      firstWall U t x ≤ sweptNiche U α x := by
  let b := (terminalTailPoint U α).1
  let H := (terminalTailPoint U α).2
  have hα0 : 0 < α := by linarith only [hα.1, Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi hα0 (by linarith only [hαL, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, Real.pi_pos], hαL⟩
  have hB : terminalFirstRightAbscissa U α = b - Real.cos α := rfl
  have hR : terminalTailReserve U α = Real.cos α - terminalTailInset U α := rfl
  have hL := terminalFirstLeftAbscissa_eq_right_add_width U α
  obtain ⟨ρ, hzeroρ, hρL⟩ :=
    exists_between (show b - terminalTailInset U α < terminalFirstLeftAbscissa U α by
      linarith only [hB, hR, hL, hfacet])
  have hfixed {t : ℝ} (ht : t ∈ Icc α β₀) (x : ℝ) :
      firstWall U t x = H + ((b - x) * Real.cos t - 1) / Real.sin t :=
    firstWall_eq_fixedPoint_of_support (Real.sin_pos_of_pos_of_lt_pi (hα0.trans_le ht.1)
      (by linarith only [ht.2, hβ₀.2, Real.pi_pos])).ne'
      (by simpa only [coordDot, unitNormal] using hsupport t ht) x
  have hjoint (x : ℝ) : ContinuousAt (fun p : ℝ × ℝ => firstWall U p.1 p.2) (α, x) :=
    ((((continuous_angleSupport hU.isCompact).comp continuous_fst).sub continuous_const).sub
      (continuous_snd.mul (Real.continuous_cos.comp continuous_fst))).continuousAt.div
      (Real.continuous_sin.comp continuous_fst).continuousAt hs.ne'
  have hgap : ∀ᶠ t in 𝓝 α, ∀ x ∈ Icc (terminalFirstRightAbscissa U α) ρ,
      firstWall U t x < sweptNiche U α x :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun x hx =>
      (hjoint x).eventually_lt
        ((hU.continuous_sweptNiche_terminalAngle hα).comp continuous_snd).continuousAt
        (hU.firstWall_lt_history_between_corner_and_left_endpoint hα0 hαL
          (hcorner.trans_le hx.1) (hx.2.trans_lt hρL))
  have hzero : ∀ᶠ t in 𝓝 α, b - ρ < (1 - H * Real.sin t) / Real.cos t :=
    Tendsto.eventually_const_lt (sub_lt_comm.mp hzeroρ)
      (show ContinuousAt (fun t => (1 - H * Real.sin t) / Real.cos t) α by
        fun_prop (disch := exact hc.ne')).tendsto
  obtain ⟨β, hαβ, hβ⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp
    (inter_mem (Ico_mem_nhdsGE hβ₀.1) (nhdsWithin_le_nhds (hgap.and hzero)))
  refine ⟨β, ⟨hαβ, (hβ ⟨hαβ.le, le_rfl⟩).1.2.trans hβ₀.2⟩, fun t ht x hx => ?_⟩
  obtain ⟨⟨htα, htβ₀⟩, hgapt, hzerot⟩ := hβ ht
  have hst := Real.sin_pos_of_pos_of_lt_pi (hα0.trans_le htα)
    (by linarith only [htβ₀, hβ₀.2, Real.pi_pos])
  have hct := Real.cos_pos_of_mem_Ioo ⟨by linarith only [hα0, htα, Real.pi_pos], htβ₀.trans hβ₀.2⟩
  rcases le_or_gt x (terminalFirstRightAbscissa U α) with hxB | hxB
  · rw [hfixed ⟨htα, htβ₀.le⟩]
    exact (fixedPoint_firstWall_le_initial hα0 htα (by linarith only [htβ₀, hβ₀.2])
      (by linarith only [hxB, hB])).trans
      ((hfixed ⟨le_rfl, hβ₀.1.le⟩ x).symm.trans_le (hOld x hx))
  rcases le_or_gt x ρ with hxρ | hxρ
  · exact (hgapt x ⟨hxB.le, hxρ⟩).le
  rw [lt_div_iff₀ hct] at hzerot
  have : ((b - x) * Real.cos t - 1) / Real.sin t ≤ -H := by
    rw [div_le_iff₀ hst]
    linarith only [hzerot, mul_le_mul_of_nonneg_right hxρ.le hct.le]
  rw [hfixed ⟨htα, htβ₀.le⟩]
  linarith only [this, sweptNiche_nonneg U α x]

-- The height bound `hH` is not needed by the construction.
set_option linter.unusedVariables false in
/-- An overlong terminal facet gives a single, literal same-cap angle
increase at a canonical joint maximizer. This statement itself has no
largest-angle premise, so it also supports the later equality argument. -/
theorem IsJointCapMaximizer.exists_same_cap_angle_extension_of_overlong_facet
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hαL : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hH : Real.sin α < (terminalTailPoint U α).2)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α) :
    ∃ β ∈ Ioo α (Real.pi / 2), IsJointCapMaximizer U β ∧
      EqOn (partialBarrier U β) (partialBarrier U α)
        (middleHalfInterval (horizontalLeft U) (horizontalRight U)) := by
  obtain ⟨β₀, hβ₀, hsupport⟩ := hU.exists_fixed_terminal_support_interval hαL haffine
  obtain ⟨β, hβ, hNew⟩ := hU.isCap.exists_right_wall_interval_of_overlong_facet
    hU.angle_mem hαL hβ₀ hsupport hcorner hfacet
    (fun x hx => hU.firstWall_le_history_of_overlong_facet hαL hcorner hfacet hx)
  have hN (x : ℝ) : sweptNiche U α x ≤ partialBarrier U β x :=
    (sweptNiche_mono_terminalAngle hU.isCap.isCompact hU.angle_pos hβ.1.le hβ.2.le x).trans
      (le_max_left _ _)
  have heq : EqOn (partialBarrier U β) (partialBarrier U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) := fun x hx =>
    (partialBarrier_le_of_firstWall_bound_after hU.isCap.isCompact hU.angle_pos hβ.1.le hβ.2.le
      (le_max_left _ _) fun t ht => (hNew t ht x hx).trans (le_max_left _ _)).antisymm
      (max_le (hN x) ((hNew α ⟨le_rfl, hβ.1.le⟩ x hx).trans (hN x)))
  have hscore : capScore U β = capScore U α := by
    rw [capScore_eq_integrals, capScore_eq_integrals,
      setIntegral_congr_fun (measurableSet_middleHalfInterval _ _) heq]
  exact ⟨β, hβ, hU.of_score_le hU.isCap ⟨hU.angle_mem.1.trans hβ.1.le, hβ.2.le⟩ hscore.ge, heq⟩

end AmbidextrousSofa
