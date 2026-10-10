import AmbidextrousSofa.Analysis.CapMaximum

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

theorem TerminalAngle.sin_pos (α : TerminalAngle) : 0 < Real.sin (α : ℝ) :=
  Real.sin_pos_of_pos_of_lt_pi α.pos (by linarith [α.property.2, Real.pi_pos])

/-- Closing the visited angular interval adds no positive height to its
supremum, even when the terminal corner itself is positive. -/
theorem fullWallClip_le_sweptNiche_of_mem_Icc (U : CompactCap) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) (x : ℝ) {t : ℝ} (ht : t ∈ Icc 0 α) :
    fullWallClip U x t ≤ sweptNiche U.carrier α x := by
  have hcont : ContinuousOn (fun θ : ℝ => fullWallClip U x θ) (Icc 0 α) := by
    intro θ hθ
    exact ((continuousAt_fullWallClip (z := ((U, x), θ))
      ⟨hθ.1, hθ.2.trans hα⟩).comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hinside : ∀ θ ∈ Ioo (0 : ℝ) α,
      fullWallClip U x θ ≤ sweptNiche U.carrier α x := by
    intro θ hθ
    exact max_le (cornerWall_le_sweptNiche
      (sweptWallValues_bddAbove U.isCap.isCompact hα x) hθ)
      (sweptNiche_nonneg _ _ _)
  have hclosure : closure (Ioo (0 : ℝ) α) = Icc 0 α := closure_Ioo (ne_of_lt hα0)
  exact le_on_closure hinside (by simpa only [hclosure] using hcont)
    continuousOn_const (by simpa only [hclosure] using ht)

theorem continuous_rescaledFullWallClip :
    Continuous (fun p : ((CompactCap × TerminalAngle) × ℝ) × Icc (0 : ℝ) 1 =>
      fullWallClip p.1.1.1 p.1.2 ((p.1.1.2 : ℝ) * (p.2 : ℝ))) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hangle : (p.1.1.2 : ℝ) * (p.2 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    refine ⟨mul_nonneg p.1.1.2.pos.le p.2.property.1, ?_⟩
    have h : (p.1.1.2 : ℝ) * (p.2 : ℝ) ≤ (p.1.1.2 : ℝ) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left p.2.property.2 p.1.1.2.pos.le
    exact h.trans p.1.1.2.property.2
  exact (continuousAt_fullWallClip
    (z := ((p.1.1.1, p.1.2), (p.1.1.2 : ℝ) * (p.2 : ℝ))) hangle).comp
      (show ContinuousAt (fun q : ((CompactCap × TerminalAngle) × ℝ) × Icc (0 : ℝ) 1 =>
        ((q.1.1.1, q.1.2), (q.1.1.2 : ℝ) * (q.2 : ℝ))) p by fun_prop)

theorem partialSweptNiche_eq_sSup_unit (U : CompactCap) (α : TerminalAngle) (x : ℝ) :
    sweptNiche U.carrier α x =
      sSup ((fun s : Icc (0 : ℝ) 1 => fullWallClip U x ((α : ℝ) * (s : ℝ))) '' univ) := by
  let zero : Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
  have hcont : Continuous (fun s : Icc (0 : ℝ) 1 =>
      fullWallClip U x ((α : ℝ) * (s : ℝ))) :=
    continuous_rescaledFullWallClip.comp (continuous_const.prodMk continuous_id)
  have hbounded := (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) 1))).bddAbove_image
    hcont.continuousOn
  have hzero : 0 ≤ sSup ((fun s : Icc (0 : ℝ) 1 =>
      fullWallClip U x ((α : ℝ) * (s : ℝ))) '' univ) := by
    have h := le_csSup hbounded (mem_image_of_mem _ (mem_univ zero))
    simpa only [zero, mul_zero, fullWallClip_zero] using h
  apply le_antisymm
  · apply sweptNiche_le_of_forall α.pos hzero
    intro θ hθ
    let s : Icc (0 : ℝ) 1 := ⟨θ / α, div_nonneg hθ.1.le α.pos.le, by
      rw [div_le_iff₀ α.pos]
      simpa only [one_mul] using hθ.2.le⟩
    have heq : (α : ℝ) * (s : ℝ) = θ := by
      dsimp [s]
      field_simp [α.pos.ne'] <;> ring
    have h := le_csSup hbounded (mem_image_of_mem _ (mem_univ s))
    rw [heq] at h
    exact (le_max_left _ _).trans h
  · apply csSup_le ⟨fullWallClip U x ((α : ℝ) * (zero : ℝ)), zero, mem_univ _, rfl⟩
    rintro y ⟨s, _, rfl⟩
    apply fullWallClip_le_sweptNiche_of_mem_Icc U α.pos α.property.2 x
    refine ⟨mul_nonneg α.pos.le s.property.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left s.property.2 α.pos.le

theorem continuous_partialCapSweptNiche :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      sweptNiche p.1.1.carrier p.1.2 p.2) := by
  have h := (isCompact_univ : IsCompact (univ : Set (Icc (0 : ℝ) 1))).continuous_sSup
    continuous_rescaledFullWallClip
  simpa only [← partialSweptNiche_eq_sSup_unit] using h

/-- The denominator of the first wall remains positive on the entire
allowed terminal interval, including its full-turn endpoint. -/
theorem continuous_partialCapFirstWall :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      firstWall p.1.1.carrier p.1.2 p.2) := by
  have hangle : Continuous (fun p : (CompactCap × TerminalAngle) × ℝ => (p.1.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hsupport : Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      support p.1.1.carrier (unitNormal p.1.2)) :=
    continuous_capSupport.comp ((continuous_fst.comp continuous_fst).prodMk
      (continuous_unitNormal.comp hangle))
  exact ((hsupport.sub continuous_const).sub (continuous_snd.mul hangle.cos)).div
    hangle.sin (fun p => p.1.2.sin_pos.ne')

theorem continuous_partialCapBarrier :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ =>
      partialBarrier p.1.1.carrier p.1.2 p.2) :=
  continuous_partialCapSweptNiche.max continuous_partialCapFirstWall

theorem IsDownwardCap.continuous_partialBarrier {U : Set Plane}
    (hU : IsDownwardCap U) {α : ℝ} (hα : α ∈ Icc (Real.pi / 4) (Real.pi / 2)) :
    Continuous (partialBarrier U α) :=
  continuous_partialCapBarrier.comp
    (continuous_const.prodMk continuous_id :
      Continuous (fun x : ℝ => ((hU.toCompactCap, (⟨α, hα⟩ : TerminalAngle)), x)))

theorem CapHausdorffTendsto.partialBarrier_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {α : ℕ → TerminalAngle} {β : TerminalAngle} (hα : Tendsto α atTop (𝓝 β))
    {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => partialBarrier (U n) (α n) (x n)) atTop (𝓝 (partialBarrier K β y)) :=
  (continuous_partialCapBarrier.tendsto ((hK.toCompactCap, β), y)).comp
    (((IsDownwardCap.tendsto_toCompactCap hU hK h).prodMk_nhds hα).prodMk_nhds hx)

theorem exists_uniform_partialBarrier_bound {B : Set Plane} (hB : IsCompact B) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : CompactCap, U.carrier ⊆ B →
      ∀ α : TerminalAngle, ∀ x ∈ Icc l r, partialBarrier U.carrier α x ≤ C := by
  have hdomain : IsCompact ((boxedCaps B ×ˢ (univ : Set TerminalAngle)) ×ˢ Icc l r) :=
    ((isCompact_boxedCaps hB).prod isCompact_univ).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hdomain.bddAbove_image continuous_partialCapBarrier.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro U hUB α x hx
  exact (hC (mem_image_of_mem _ (show ((U, α), x) ∈
    (boxedCaps B ×ˢ (univ : Set TerminalAngle)) ×ˢ Icc l r from
      ⟨⟨hUB, mem_univ α⟩, hx⟩))).trans (le_max_left _ _)

theorem CapHausdorffTendsto.middle_partialBarrier_integral_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {α : ℕ → TerminalAngle} {β : TerminalAngle} (hα : Tendsto α atTop (𝓝 β))
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => ∫ x in middleHalfInterval
      (horizontalLeft (U n)) (horizontalRight (U n)), partialBarrier (U n) (α n) x)
      atTop (𝓝 (∫ x in middleHalfInterval (horizontalLeft K) (horizontalRight K),
        partialBarrier K β x)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_partialBarrier_bound hB
    (horizontalLeft B) (horizontalRight B)
  have hwindow : ∀ n, middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆
      Icc (horizontalLeft B) (horizontalRight B) := fun n =>
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      (hU n).nonempty (hU n).isCompact)).trans
      ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  apply tendsto_setIntegral_moving_domain
    (fun n => measurable_partialBarrier (hU n).isCompact (α n).pos (α n).property.2)
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    (Eventually.of_forall (fun x => h.partialBarrier_tendsto hU hK hα tendsto_const_nhds))
    (h.middle_membership_ae hU hK) hC hwindow
  intro n x hx
  rw [Real.norm_of_nonneg (partialBarrier_nonneg _ _ _)]
  exact hbound (hU n).toCompactCap (hsub n) (α n) x (hwindow n hx)

theorem CapHausdorffTendsto.partialCapScore_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {α : ℕ → TerminalAngle} {β : TerminalAngle} (hα : Tendsto α atTop (𝓝 β))
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => capScore (U n) (α n)) atTop (𝓝 (capScore K β)) := by
  have hlim := (h.exterior_roof_integral_tendsto hU hK hB hsub).sub
    (h.middle_partialBarrier_integral_tendsto hU hK hα hB hsub)
  have hScore (n : ℕ) := capScore_eq_integrals (U n) (α n)
  simpa only [← hScore, ← capScore_eq_integrals K β] using hlim

/-- Joint continuity on the whole compact cap-and-angle domain, retaining
zero-width and zero-height caps at its boundary. -/
theorem continuous_partialCapScore_on_box {B : Set Plane} (hB : IsCompact B) :
    Continuous (fun p : boxedCaps B × TerminalAngle => capScore p.1.val.carrier p.2) := by
  apply continuous_iff_seqContinuous.mpr
  intro U K hlim
  have hc : Tendsto (fun n => (U n).1.val) atTop (𝓝 K.1.val) :=
    (continuous_subtype_val.tendsto K.1).comp hlim.fst
  exact (CompactCap.tendsto_iff_hausdorff.mp hc).partialCapScore_tendsto
    (fun n => (U n).1.val.isCap) K.1.val.isCap hlim.snd hB (fun n => (U n).1.property)

end AmbidextrousSofa
