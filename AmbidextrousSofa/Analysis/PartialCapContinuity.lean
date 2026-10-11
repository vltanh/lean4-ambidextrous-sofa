module

public import AmbidextrousSofa.Analysis.CapMaximum

@[expose] public section

/-!
# Joint continuity for the entire partial barrier

The open swept interval has the same clipped supremum as its closed
interval: continuity at the terminal angle supplies the additional endpoint.
Rescaling that interval to `[0,1]` makes the parameter domain fixed and
compact. The resulting maximum is jointly continuous in the actual cap,
terminal angle and horizontal coordinate. The whole first terminal wall
is then retained as a separate continuous term, including at `π/2`.

Compact bounds and moving-domain dominated convergence give continuity of
the actual partial score on every boxed cap domain. No regularity or
stationarity hypothesis is imposed on these caps.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

abbrev TerminalAngle := Icc (Real.pi / 4) (Real.pi / 2)

theorem TerminalAngle.pos (α : TerminalAngle) : 0 < (α : ℝ) := by
  linarith [α.property.1, Real.pi_pos]

/-- Closing the visited angular interval adds no positive height to its
supremum, even when the terminal corner itself is positive. -/
theorem fullWallClip_le_sweptNiche_of_mem_Icc (U : CompactCap) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) {t : ℝ} (ht : t ∈ Icc 0 α) :
    fullWallClip U x t ≤ sweptNiche U.carrier α x := by
  have hcl := closure_Ioo hα0.ne
  refine le_on_closure (fun θ hθ => max_le (cornerWall_le_sweptNiche
    (sweptWallValues_bddAbove U.isCap.isCompact hα x) hθ) (sweptNiche_nonneg _ _ _))
    (hcl ▸ fun θ hθ => ((continuousAt_fullWallClip (z := ((U, x), θ)) ⟨hθ.1, hθ.2.trans hα⟩).comp
      (f := fun θ => ((U, x), θ)) (by fun_prop)).continuousWithinAt) continuousOn_const (hcl ▸ ht)

theorem continuous_rescaledFullWallClip :
    Continuous (fun p : ((CompactCap × TerminalAngle) × ℝ) × Icc (0 : ℝ) 1 =>
      fullWallClip p.1.1.1 p.1.2 ((p.1.1.2 : ℝ) * (p.2 : ℝ))) :=
  continuous_iff_continuousAt.2 fun p => (continuousAt_fullWallClip
    (z := ((p.1.1.1, p.1.2), (p.1.1.2 : ℝ) * (p.2 : ℝ)))
    ⟨mul_nonneg (TerminalAngle.pos _).le p.2.2.1,
      (mul_le_of_le_one_right (TerminalAngle.pos _).le p.2.2.2).trans p.1.1.2.2.2⟩).comp
    (f := fun q : ((CompactCap × TerminalAngle) × ℝ) × Icc (0 : ℝ) 1 =>
      ((q.1.1.1, q.1.2), (q.1.1.2 : ℝ) * (q.2 : ℝ))) (by fun_prop)

theorem partialSweptNiche_eq_sSup_unit (U : CompactCap) (α : TerminalAngle) (x : ℝ) :
    sweptNiche U.carrier α x =
      sSup ((fun s : Icc (0 : ℝ) 1 => fullWallClip U x ((α : ℝ) * (s : ℝ))) '' univ) := by
  have hα := TerminalAngle.pos α
  have hle (s : Icc (0 : ℝ) 1) : fullWallClip U x ((α : ℝ) * (s : ℝ)) ≤
      sSup ((fun s : Icc (0 : ℝ) 1 => fullWallClip U x ((α : ℝ) * (s : ℝ))) '' univ) :=
    le_csSup (isCompact_univ.bddAbove_image (continuous_rescaledFullWallClip.comp
      (.prodMk_right ((U, α), x))).continuousOn) ⟨s, mem_univ _, rfl⟩
  refine le_antisymm (sweptNiche_le_of_forall hα ((le_max_right _ _).trans
    (hle ⟨0, le_rfl, zero_le_one⟩)) fun θ hθ => ?_) (csSup_le (univ_nonempty.image _) ?_)
  · have h := hle ⟨θ / α, div_nonneg hθ.1.le hα.le, (div_le_one hα).2 hθ.2.le⟩
    rw [mul_div_cancel₀ _ hα.ne'] at h
    exact (le_max_left _ _).trans h
  · rintro _ ⟨s, -, rfl⟩
    exact fullWallClip_le_sweptNiche_of_mem_Icc U hα α.2.2 x
      ⟨mul_nonneg hα.le s.2.1, mul_le_of_le_one_right hα.le s.2.2⟩

theorem continuous_partialCapSweptNiche :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      sweptNiche p.1.1.carrier p.1.2 p.2) := by
  simpa only [← partialSweptNiche_eq_sSup_unit] using isCompact_univ.continuous_sSup
    (f := fun (q : (CompactCap × TerminalAngle) × ℝ) (s : Icc (0 : ℝ) 1) =>
      fullWallClip q.1.1 q.2 ((q.1.2 : ℝ) * (s : ℝ))) continuous_rescaledFullWallClip

/-- The denominator of the first wall remains positive on the entire
allowed terminal interval, including its full-turn endpoint. -/
theorem continuous_partialCapFirstWall :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      firstWall p.1.1.carrier p.1.2 p.2) := by
  have := continuous_unitNormal
  have := continuous_capSupport.comp (f := fun p : (CompactCap × TerminalAngle) × ℝ =>
    (p.1.1, unitNormal p.1.2)) (by fun_prop)
  unfold firstWall
  fun_prop (disch := exact fun p => (Real.sin_pos_of_pos_of_lt_pi (TerminalAngle.pos _)
    (by linarith [p.1.2.2.2, Real.pi_pos])).ne')

theorem continuous_partialCapBarrier :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      partialBarrier p.1.1.carrier p.1.2 p.2) :=
  continuous_partialCapSweptNiche.max continuous_partialCapFirstWall

theorem IsDownwardCap.continuous_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    Continuous (partialBarrier U α) :=
  (continuous_partialCapBarrier.comp (.prodMk_right (hU.toCompactCap, (⟨α, hα⟩ : TerminalAngle))) :)

theorem CapHausdorffTendsto.middle_partialBarrier_integral_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {α : ℕ → TerminalAngle} {β : TerminalAngle} (hα : Tendsto α atTop (𝓝 β))
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => ∫ x in middleHalfInterval
      (horizontalLeft (U n)) (horizontalRight (U n)), partialBarrier (U n) (α n) x)
      atTop (𝓝 (∫ x in middleHalfInterval (horizontalLeft K) (horizontalRight K),
        partialBarrier K β x)) := by
  -- the barrier is bounded on the compact domain of boxed caps, angles and window abscissae
  obtain ⟨C, hC⟩ := (((isCompact_boxedCaps hB).prod (isCompact_univ (X := TerminalAngle))).prod
    (isCompact_Icc (a := horizontalLeft B) (b := horizontalRight B))).bddAbove_image
      continuous_partialCapBarrier.continuousOn
  have hwindow (n : ℕ) : middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆
      Icc (horizontalLeft B) (horizontalRight B) :=
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      (hU n).nonempty (hU n).isCompact)).trans
      ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  refine tendsto_setIntegral_moving_domain
    (fun n => measurable_partialBarrier (hU n).isCompact (TerminalAngle.pos (α n)) (α n).2.2)
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    (.of_forall fun x => ((continuous_partialCapBarrier.tendsto ((hK.toCompactCap, β), x)).comp
      (((IsDownwardCap.tendsto_toCompactCap hU hK h).prodMk_nhds hα).prodMk_nhds
        tendsto_const_nhds) :))
    (h.middle_membership_ae hU hK) (le_max_right C 0) hwindow fun n x hx => ?_
  rw [Real.norm_of_nonneg (partialBarrier_nonneg _ _ _)]
  exact le_max_of_le_left (hC ⟨(((hU n).toCompactCap, α n), x),
    ⟨⟨hsub n, mem_univ _⟩, hwindow n hx⟩, rfl⟩)

/-- Joint continuity on the whole compact cap-and-angle domain, retaining
zero-width and zero-height caps at its boundary. -/
theorem continuous_partialCapScore_on_box {B : Set Plane} (hB : IsCompact B) :
    Continuous (fun p : boxedCaps B × TerminalAngle => capScore p.1.val.carrier p.2) := by
  refine continuous_iff_seqContinuous.mpr fun U K hlim => ?_
  have h := CompactCap.tendsto_iff_hausdorff.mp
    ((continuous_subtype_val.tendsto K.1).comp hlim.fst_nhds)
  have hU n := (U n).1.val.isCap
  have hsub n := (U n).1.property
  simpa only [← capScore_eq_integrals, Function.comp_def] using
    (h.exterior_roof_integral_tendsto hU K.1.val.isCap hB hsub).sub
      (h.middle_partialBarrier_integral_tendsto hU K.1.val.isCap hlim.snd_nhds hB hsub)

end AmbidextrousSofa
