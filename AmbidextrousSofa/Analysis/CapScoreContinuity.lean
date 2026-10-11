module

public import AmbidextrousSofa.Analysis.CapRoofConvergence
public import AmbidextrousSofa.Analysis.CapNicheContinuity

@[expose] public section

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
  have hdom (n : ℕ) : ∀ᵐ x : ℝ ∂volume,
      ‖(A n).indicator (f n) x‖ ≤ (Icc l r).indicator (fun _ => C) x := by
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ A n
    · simpa only [indicator_of_mem hx, indicator_of_mem (hsub n hx)] using hbound n x hx
    · simp [hx, indicator_nonneg, hC]
  have hlim : ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => (A n).indicator (f n) x)
      atTop (𝓝 (D.indicator g x)) := by
    filter_upwards [hflim, hAlim] with x hfx hAx
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx]
      exact hfx.congr' (hAx.mono fun n hn => (indicator_of_mem (hn.2 hx) _).symm)
    · rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr'
        (hAx.mono fun n hn => (indicator_of_notMem (mt hn.1 hx) _).symm)
  simpa only [integral_indicator (hA _), integral_indicator hD] using
    tendsto_integral_of_dominated_convergence _
      (fun n => ((hf n).indicator (hA n)).aestronglyMeasurable)
      (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc) hdom hlim

theorem IsDownwardCap.projection_subset_bounds_of_subset
    {U B : Set Plane} (hU : IsDownwardCap U) (hB : IsCompact B) (hsub : U ⊆ B) :
    Icc (horizontalLeft U) (horizontalRight U) ⊆
      Icc (horizontalLeft B) (horizontalRight B) :=
  Icc_subset_Icc (csInf_le_csInf (isCompact_horizontalProjection hB).bddBelow
      (hU.nonempty.image _) (image_mono hsub))
    (csSup_le_csSup (isCompact_horizontalProjection hB).bddAbove
      (hU.nonempty.image _) (image_mono hsub))

theorem CapHausdorffTendsto.exterior_roof_integral_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => ∫ x in Icc (horizontalLeft (U n)) (horizontalRight (U n)) \
        middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)), capRoof (U n) x)
      atTop (𝓝 (∫ x in Icc (horizontalLeft K) (horizontalRight K) \
        middleHalfInterval (horizontalLeft K) (horizontalRight K), capRoof K x)) :=
  tendsto_setIntegral_moving_domain (fun n => (hU n).measurable_capRoof)
    (fun n => measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
    (measurableSet_Icc.diff (measurableSet_middleHalfInterval _ _))
    (h.capRoof_tendsto_ae hU hK)
    (by filter_upwards [h.projection_membership_ae hU hK, h.middle_membership_ae hU hK]
          with x hxI hxJ using (hxI.and hxJ).mono fun n hn => and_congr hn.1 (not_congr hn.2))
    zero_le_one
    (fun n => sdiff_subset.trans ((hU n).projection_subset_bounds_of_subset hB (hsub n)))
    fun n x _ => (Real.norm_of_nonneg (capRoof_nonneg (hU n).isCompact
      (fun p hp => ((hU n).inStrip hp).1) x)).trans_le
      (capRoof_le_one (hU n).isCompact (hU n).inStrip x)

theorem CapHausdorffTendsto.capScore_pi_div_two_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => capScore (U n) (Real.pi / 2)) atTop
      (𝓝 (capScore K (Real.pi / 2))) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨C, hC, hsupport⟩ := exists_support_upper_bound_quarterTurn hB
  have hwindow (n : ℕ) : middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆
      Icc (horizontalLeft B) (horizontalRight B) :=
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      (hU n).nonempty (hU n).isCompact)).trans
      ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  simp only [(hU _).capScore_pi_div_two, hK.capScore_pi_div_two]
  refine (h.exterior_roof_integral_tendsto hU hK hB hsub).sub (tendsto_setIntegral_moving_domain
    (fun n => measurable_sweptNiche (hU n).isCompact hpi le_rfl)
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    (Eventually.of_forall fun x => h.sweptNiche_tendsto hU hK tendsto_const_nhds)
    (h.middle_membership_ae hU hK) (C := 2 * (C + 1 + |horizontalLeft B| + |horizontalRight B|))
    (by positivity) hwindow fun n x hx => ?_)
  -- The support bounds of the containing compact set bound every niche on its window.
  have habs := abs_le_endpoint_sum_of_mem_Icc (hwindow n hx)
  rw [Real.norm_of_nonneg (sweptNiche_nonneg _ _ _)]
  refine sweptNiche_le_of_forall hpi (by positivity) fun t ht => ?_
  have hb := hsupport t ⟨ht.1.le, ht.2.le⟩
  linarith [cornerWall_le_of_support_bounds hC ht
    ((support_mono (hsub n) (hU n).nonempty hB _).trans hb.1)
    ((support_mono (hsub n) (hU n).nonempty hB _).trans hb.2) x]

end AmbidextrousSofa
