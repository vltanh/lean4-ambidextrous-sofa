import AmbidextrousSofa.Analysis.CapRoofConvergence
import AmbidextrousSofa.Analysis.CapNicheContinuity

/-!
# Continuity of the full spatial cap score

The exterior roof and middle niche are integrated on the cap's own moving
projection window. Membership in those intervals stabilizes almost
everywhere. The roof is bounded by one; compact containment supplies a
uniform niche bound. Dominated convergence therefore applies to both terms.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

/-- A moving measurable domain is handled by its actual indicator. -/
theorem tendsto_setIntegral_moving_domain
    {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {A : ℕ → Set ℝ} {D : Set ℝ}
    (hf : ∀ n, Measurable (f n)) (hA : ∀ n, MeasurableSet (A n))
    (hD : MeasurableSet D)
    (hflim : ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hAlim : ∀ᵐ x : ℝ ∂volume, ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ D))
    {l r C : ℝ} (hC : 0 ≤ C) (hsub : ∀ n, A n ⊆ Icc l r)
    (hbound : ∀ n, ∀ x ∈ A n, ‖f n x‖ ≤ C) :
    Tendsto (fun n => ∫ x in A n, f n x) atTop (𝓝 (∫ x in D, g x)) := by
  have hmeas : ∀ n, AEStronglyMeasurable ((A n).indicator (f n)) volume :=
    fun n => ((hf n).indicator (hA n)).aestronglyMeasurable
  have hint : Integrable ((Icc l r).indicator (fun _ => C)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hdom : ∀ n, ∀ᵐ x : ℝ ∂volume,
      ‖(A n).indicator (f n) x‖ ≤ (Icc l r).indicator (fun _ => C) x := by
    intro n
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ A n
    · simpa only [indicator_of_mem hx, indicator_of_mem (hsub n hx)] using hbound n x hx
    · by_cases hxI : x ∈ Icc l r <;> simp [hx, hxI, hC]
  have hlim : ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => (A n).indicator (f n) x)
      atTop (𝓝 (D.indicator g x)) := by
    filter_upwards [hflim, hAlim] with x hfx hAx
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx]
      apply hfx.congr'
      filter_upwards [hAx] with n hn
      simp only [indicator_of_mem (hn.mpr hx)]
    · rw [indicator_of_notMem hx]
      apply tendsto_const_nhds.congr'
      filter_upwards [hAx] with n hn
      simp only [indicator_of_notMem (fun hmem => hx (hn.mp hmem))]
  have h := tendsto_integral_of_dominated_convergence
    ((Icc l r).indicator (fun _ => C)) hmeas hint hdom hlim
  have hIntegral (n : ℕ) := integral_indicator (μ := (volume : Measure ℝ))
    (f := f n) (hA n)
  simpa only [hIntegral, integral_indicator hD] using h

theorem IsDownwardCap.projection_subset_bounds_of_subset
    {U B : Set Plane} (hU : IsDownwardCap U) (hB : IsCompact B) (hsub : U ⊆ B) :
    Icc (horizontalLeft U) (horizontalRight U) ⊆
      Icc (horizontalLeft B) (horizontalRight B) := by
  rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  rintro x ⟨p, hp, rfl⟩
  have hpB : p.1 ∈ horizontalProjection B := ⟨p, hsub hp, rfl⟩
  exact ⟨csInf_le (isCompact_horizontalProjection hB).bddBelow hpB,
    le_csSup (isCompact_horizontalProjection hB).bddAbove hpB⟩

/-- One compact containing set bounds every niche in a cap family. -/
theorem exists_uniform_sweptNiche_bound_of_compact_containment
    {U : ℕ → Set Plane} (hU : ∀ n, IsDownwardCap (U n))
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) (l r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ∀ x ∈ Icc l r, sweptNiche (U n) (Real.pi / 2) x ≤ C := by
  obtain ⟨C, hC, hsupport⟩ := exists_support_upper_bound_quarterTurn hB
  refine ⟨2 * (C + 1 + |l| + |r|), by positivity, ?_⟩
  intro n x hx
  have hpoint : sweptNiche (U n) (Real.pi / 2) x ≤ 2 * (C + 1 + |x|) := by
    apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) (by positivity)
    intro t ht
    have hb := hsupport t ⟨ht.1.le, ht.2.le⟩
    exact cornerWall_le_of_support_bounds hC ht
      ((support_mono (hsub n) (hU n).nonempty hB _).trans hb.1)
      ((support_mono (hsub n) (hU n).nonempty hB _).trans hb.2) x
  linarith [abs_le_endpoint_sum_of_mem_Icc hx]

theorem CapHausdorffTendsto.exterior_roof_integral_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => ∫ x in Icc (horizontalLeft (U n)) (horizontalRight (U n)) \
        middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)), capRoof (U n) x)
      atTop (𝓝 (∫ x in Icc (horizontalLeft K) (horizontalRight K) \
        middleHalfInterval (horizontalLeft K) (horizontalRight K), capRoof K x)) := by
  apply tendsto_setIntegral_moving_domain (fun n => (hU n).measurable_capRoof)
    (fun n => measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
    (measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
    (h.capRoof_tendsto_ae hU hK) ?_ (C := 1) zero_le_one
    (l := horizontalLeft B) (r := horizontalRight B)
  · filter_upwards [h.projection_membership_ae hU hK, h.middle_membership_ae hU hK]
      with x hxI hxJ
    filter_upwards [hxI, hxJ] with n hnI hnJ
    exact and_congr hnI (not_congr hnJ)
  · intro n
    exact sdiff_subset.trans ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  · intro n x _
    rw [Real.norm_of_nonneg (capRoof_nonneg (hU n).isCompact
      (fun p hp => ((hU n).inStrip hp).1) x)]
    exact capRoof_le_one (hU n).isCompact (hU n).inStrip x

theorem CapHausdorffTendsto.middle_niche_integral_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => ∫ x in middleHalfInterval
        (horizontalLeft (U n)) (horizontalRight (U n)), sweptNiche (U n) (Real.pi / 2) x)
      atTop (𝓝 (∫ x in middleHalfInterval (horizontalLeft K) (horizontalRight K),
        sweptNiche K (Real.pi / 2) x)) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_sweptNiche_bound_of_compact_containment
    hU hB hsub (horizontalLeft B) (horizontalRight B)
  have hwindow : ∀ n, middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆
      Icc (horizontalLeft B) (horizontalRight B) := fun n =>
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      (hU n).nonempty (hU n).isCompact)).trans
      ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  apply tendsto_setIntegral_moving_domain
    (fun n => measurable_sweptNiche (hU n).isCompact (by linarith [Real.pi_pos]) le_rfl)
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    (Eventually.of_forall (fun x => h.sweptNiche_tendsto hU hK tendsto_const_nhds))
    (h.middle_membership_ae hU hK) hC hwindow
  intro n x hx
  rw [Real.norm_of_nonneg (sweptNiche_nonneg _ _ _)]
  exact hbound n x (hwindow n hx)

theorem CapHausdorffTendsto.capScore_pi_div_two_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => capScore (U n) (Real.pi / 2)) atTop
      (𝓝 (capScore K (Real.pi / 2))) := by
  have hlim := (h.exterior_roof_integral_tendsto hU hK hB hsub).sub
    (h.middle_niche_integral_tendsto hU hK hB hsub)
  have hScore (n : ℕ) := (hU n).capScore_pi_div_two
  simpa only [← hScore,
    ← IsDownwardCap.capScore_pi_div_two hK] using hlim

end AmbidextrousSofa
