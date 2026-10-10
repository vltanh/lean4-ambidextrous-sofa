import AmbidextrousSofa.Analysis.TerminalHistory

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
  let d := if α < affineNormalAngle m then min (affineNormalAngle m) (Real.pi / 2)
    else Real.pi / 2
  have hαd : α < d := by
    dsimp [d]
    split_ifs with h
    · exact lt_min h hαL
    · exact hαL
  have hdL : d ≤ Real.pi / 2 := by
    dsimp [d]
    split_ifs
    · exact min_le_right _ _
    · exact le_rfl
  obtain ⟨β, hαβ, hβd⟩ := exists_between hαd
  have hβL : β < Real.pi / 2 := hβd.trans_le hdL
  have hgap : affineNormalAngle m ∉ Ioo α β := by
    intro hm
    have hdm : d ≤ affineNormalAngle m := by
      dsimp [d]
      rw [if_pos hm.1]
      exact min_le_left _ _
    exact (not_lt_of_ge (hβd.trans_le hdm).le) hm.2
  have hsupport := hU.support_vertices_first_unused_gap haffine le_rfl hβL.le hαβ hgap
  refine ⟨β, ⟨hαβ, hβL⟩, ?_⟩
  intro t ht
  have h := hsupport.2.1 t ht
  rw [← hsupport.1] at h
  exact h

theorem IsDownwardCap.firstWall_joint_continuousAt {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hs : Real.sin α ≠ 0) (x : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => firstWall U p.1 p.2) (α, x) := by
  have hsupport : Continuous (fun p : ℝ × ℝ => support U (unitNormal p.1)) :=
    (continuous_support hU.isCompact).comp (continuous_unitNormal.comp continuous_fst)
  have hcos : Continuous (fun p : ℝ × ℝ => Real.cos p.1) :=
    Real.continuous_cos.comp continuous_fst
  have hsin : Continuous (fun p : ℝ × ℝ => Real.sin p.1) :=
    Real.continuous_sin.comp continuous_fst
  exact ((hsupport.continuousAt.sub continuousAt_const).sub
    (continuous_snd.continuousAt.mul hcos.continuousAt)).div hsin.continuousAt hs

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
    (hreserve : 0 < terminalTailReserve U α)
    (hfacet : terminalTailReserve U α < terminalFaceWidth U α)
    (hOld : ∀ x ∈ Icc l r, firstWall U α x ≤ sweptNiche U α x) :
    ∃ β ∈ Ioo α (Real.pi / 2), ∀ t ∈ Icc α β, ∀ x ∈ Icc l r,
      firstWall U t x ≤ sweptNiche U α x := by
  let b := (terminalTailPoint U α).1
  let H := (terminalTailPoint U α).2
  have hα0 : 0 < α := by linarith [hα.1, Real.pi_pos]
  have hs : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0
    (by linarith [Real.pi_pos])
  have hc : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hαL⟩
  have hBzero : terminalFirstRightAbscissa U α < terminalTailZero U α := by
    unfold terminalFirstRightAbscissa terminalTailZero terminalTailReserve at *
    dsimp only [terminalTailPoint] at *
    linarith
  have hzeroLeft : terminalTailZero U α < terminalFirstLeftAbscissa U α := by
    rw [terminalFirstLeftAbscissa_eq_right_add_width]
    unfold terminalFirstRightAbscissa terminalTailZero terminalTailReserve at *
    dsimp only [terminalTailPoint] at *
    linarith
  obtain ⟨ζ, hcornerζ, hζB⟩ := exists_between hcorner
  obtain ⟨rstar, hzeroStar, hstarLeft⟩ := exists_between hzeroLeft
  have hζstar : ζ < rstar := hζB.trans (hBzero.trans hzeroStar)
  have hfixed {t : ℝ} (ht : t ∈ Icc α β₀) :
      angleSupport U t = b * Real.cos t + H * Real.sin t := by
    simpa only [coordDot, unitNormal] using hsupport t ht
  have hfirstα (x : ℝ) : firstWall U α x =
      H + ((b - x) * Real.cos α - 1) / Real.sin α :=
    firstWall_eq_fixedPoint_of_support hs.ne' (hfixed ⟨le_rfl, hβ₀.1.le⟩) x
  have hN := hU.continuous_sweptNiche_terminalAngle hα
  have hgapEvent : ∀ᶠ t in 𝓝 α, ∀ x ∈ Icc ζ rstar,
      firstWall U t x < sweptNiche U α x := by
    apply (isCompact_Icc : IsCompact (Icc ζ rstar)).eventually_forall_of_forall_eventually
    intro x hx
    exact (hU.firstWall_joint_continuousAt hs.ne' x).tendsto.eventually_lt
      ((hN.comp continuous_snd).continuousAt.tendsto)
      (hU.firstWall_lt_history_between_corner_and_left_endpoint hα0 hαL
        (hcornerζ.trans_le hx.1) (hx.2.trans_lt hstarLeft))
  have hzeroCont : ContinuousAt (fun t : ℝ => b - (1 - H * Real.sin t) / Real.cos t) α :=
    continuousAt_const.sub ((continuousAt_const.sub
      (continuousAt_const.mul Real.continuous_sin.continuousAt)).div
        Real.continuous_cos.continuousAt hc.ne')
  have hzeroEvent : ∀ᶠ t in 𝓝 α, b - (1 - H * Real.sin t) / Real.cos t < rstar :=
    Filter.Tendsto.eventually_lt_const hzeroStar hzeroCont.tendsto
  have hNew : ∀ᶠ t in 𝓝[>] α, ∀ x ∈ Icc l r,
      firstWall U t x ≤ sweptNiche U α x := by
    filter_upwards [Ioo_mem_nhdsGT hβ₀.1,
      hgapEvent.filter_mono nhdsWithin_le_nhds,
      hzeroEvent.filter_mono nhdsWithin_le_nhds] with t ht hgap hzero
    have htL : t < Real.pi / 2 := ht.2.trans hβ₀.2
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi (hα0.trans ht.1)
      (by linarith [Real.pi_pos])
    have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hα0, ht.1, Real.pi_pos], htL⟩
    have hfirst (x : ℝ) : firstWall U t x =
        H + ((b - x) * Real.cos t - 1) / Real.sin t :=
      firstWall_eq_fixedPoint_of_support hst.ne' (hfixed ⟨ht.1.le, ht.2.le⟩) x
    intro x hx
    by_cases hxζ : x ≤ ζ
    · have hdistance : Real.cos α ≤ b - x := by
        unfold terminalFirstRightAbscissa at hζB
        dsimp only [b, terminalTailPoint]
        linarith
      calc
        firstWall U t x = H + ((b - x) * Real.cos t - 1) / Real.sin t := hfirst x
        _ ≤ H + ((b - x) * Real.cos α - 1) / Real.sin α :=
          fixedPoint_firstWall_le_initial hα0 ht.1.le htL.le hdistance
        _ = firstWall U α x := (hfirstα x).symm
        _ ≤ sweptNiche U α x := hOld x hx
    · by_cases hxstar : x ≤ rstar
      · exact (hgap x ⟨(lt_of_not_ge hxζ).le, hxstar⟩).le
      · have hdist : b - x ≤ (1 - H * Real.sin t) / Real.cos t := by
          linarith [lt_of_not_ge hxstar]
        have hnum : (b - x) * Real.cos t - 1 ≤ -H * Real.sin t := by
          have h := (le_div_iff₀ hct).mp hdist
          nlinarith only [h]
        have hwall : firstWall U t x ≤ 0 := by
          rw [hfirst]
          have h := (div_le_iff₀ hst).mpr hnum
          linarith
        exact hwall.trans (sweptNiche_nonneg U α x)
  obtain ⟨c, hαc, hlocal⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hNew
  obtain ⟨β, hαβ, hβ⟩ := exists_between (lt_min hαc hβ₀.1)
  have hβL : β < Real.pi / 2 :=
    (hβ.trans_le (min_le_right _ _)).trans hβ₀.2
  refine ⟨β, ⟨hαβ, hβL⟩, ?_⟩
  intro t ht x hx
  by_cases hta : t = α
  · simpa only [hta] using hOld x hx
  · exact hlocal ⟨lt_of_le_of_ne ht.1 (Ne.symm hta),
      ht.2.trans_lt (hβ.trans_le (min_le_left _ _))⟩ x hx

/-- Keeping the cap and the whole spatial window fixed, a controlled
interval of new first walls gives identical old and new partial barriers. -/
theorem IsDownwardCap.partialBarrier_eq_of_new_firstWalls_le_history
    {U : Set Plane} (hU : IsDownwardCap U) {α β l r : ℝ}
    (hα0 : 0 < α) (hαβ : α ≤ β) (hβL : β ≤ Real.pi / 2)
    (hNew : ∀ t ∈ Icc α β, ∀ x ∈ Icc l r, firstWall U t x ≤ sweptNiche U α x) :
    EqOn (partialBarrier U β) (partialBarrier U α) (Icc l r) := by
  intro x hx
  have hOld : partialBarrier U α x = sweptNiche U α x :=
    max_eq_left (hNew α ⟨le_rfl, hαβ⟩ x hx)
  rw [hOld]
  apply le_antisymm
  · exact partialBarrier_le_of_firstWall_bound_after hU.isCompact hα0 hαβ hβL
      le_rfl (fun t ht => hNew t ht x hx)
  · exact (sweptNiche_mono_terminalAngle hU.isCompact hα0 hαβ hβL x).trans
      (le_max_left _ _)

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
  obtain ⟨_, _, hreserve, _, _⟩ :=
    hU.isCap.terminalTailInset_bounds hU.angle_pos hαL hH
  obtain ⟨β, hβ, hNew⟩ := hU.isCap.exists_right_wall_interval_of_overlong_facet
    hU.angle_mem hαL hβ₀ hsupport hcorner hreserve hfacet
    (fun x hx => hU.firstWall_le_history_of_overlong_facet hαL hcorner hfacet hx)
  have heq := hU.isCap.partialBarrier_eq_of_new_firstWalls_le_history
    hU.angle_pos hβ.1.le hβ.2.le hNew
  have hscore : capScore U β = capScore U α := by
    rw [capScore_eq_integrals, capScore_eq_integrals]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_middleHalfInterval _ _)] with x hx
    exact heq hx
  exact ⟨β, hβ, hU.of_score_le hU.isCap
    ⟨hU.angle_mem.1.trans hβ.1.le, hβ.2.le⟩ hscore.ge, heq⟩

/-- The largest-angle contradiction uses only an actual same-cap
competitor; no terminal source-mass identity is presumed. -/
theorem IsJointCapMaximizer.terminalFaceWidth_le_reserve_of_corner_lt
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hLargest : ∀ V : Set Plane, ∀ β : ℝ, IsJointCapMaximizer V β → β ≤ α)
    (hαL : α < Real.pi / 2) (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hcorner : (attachedCorner U α).1 < terminalFirstRightAbscissa U α) :
    terminalFaceWidth U α ≤ terminalTailReserve U α := by
  by_contra h
  have hfacet : terminalTailReserve U α < terminalFaceWidth U α := lt_of_not_ge h
  have hH := (hU.terminalTailPoint_bounds hLargest hαL hheight haffine).2.1
  obtain ⟨β, hβ, hmax, _⟩ :=
    hU.exists_same_cap_angle_extension_of_overlong_facet hαL haffine hH hcorner hfacet
  exact (not_le_of_gt hβ.1) (hLargest U β hmax)

end AmbidextrousSofa
