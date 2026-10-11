module

public import AmbidextrousSofa.Analysis.HorizontalWindowLimit

@[expose] public section

/-!
# The lower spatial limit of positive niche length

Intersecting each finite positive region with the target positive region
produces bounded indicators that converge everywhere except for the moving
window endpoints. The finite niche itself need not have convergent zero
sets. Its overlap integral converges to the actual target positive length
and is bounded above by the literal finite horizontal source moment.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

def positiveNicheOverlap (target U : Set Plane) (grid : Finset QuarterAngle) : ℝ → ℝ :=
  (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x} ∩
    {x : ℝ | 0 < finiteBarrier U (normal grid) (pairList grid) none x}).indicator
      (fun _ => 1)

theorem measurableSet_positiveNiche {target : Set Plane} (hTarget : IsDownwardCap target) :
    MeasurableSet (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
      {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x}) :=
  (measurableSet_middleHalfInterval _ _).inter (measurableSet_lt measurable_const
    (measurable_sweptNiche hTarget.isCompact (by linarith [Real.pi_pos]) le_rfl))

theorem integral_positiveNicheOverlap_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (grid : Finset QuarterAngle) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      positiveNicheOverlap target U grid x) ≤
    finitePositiveLength U (normal grid) (pairList grid) none
      (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) := by
  change (∫ x in Icc (horizontalLeft U + capWidth U / 4)
    (horizontalRight U - capWidth U / 4), positiveNicheOverlap target U grid x) ≤ _
  rw [integral_Icc_eq_integral_Ioc, positiveNicheOverlap, setIntegral_indicator
    ((measurableSet_positiveNiche hTarget).inter (measurableSet_lt measurable_const
      (continuous_finiteBarrier U _ _ _).measurable)), setIntegral_const, smul_eq_mul, mul_one]
  exact measureReal_mono (fun x hx => ⟨hx.1, hx.2.2⟩)
    ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top).ne

/-- Uniform finite-wall convergence is used only at target points where
the niche is strictly positive. Zero-height components may disappear. -/
theorem integral_positiveNicheOverlap_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsDownwardCap (U n)) (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => ∫ x in middleHalfInterval
      (horizontalLeft (U n)) (horizontalRight (U n)),
        positiveNicheOverlap target (U n) (dyadic (level n)) x) atTop
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
        {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x}))) := by
  let P : Set ℝ := middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x}
  have hP : MeasurableSet P := measurableSet_positiveNiche hTarget
  have hflim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => positiveNicheOverlap target (U n) (dyadic (level n)) x)
        atTop (𝓝 (P.indicator (fun _ => 1) x)) := by
    refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    by_cases hx : x ∈ P
    · have hxB : x ∈ Icc a b := (hTarget.projection_subset_Icc_of_box hTargetBox)
        (middleHalfInterval_subset
          (horizontalLeft_le_horizontalRight hTarget.nonempty hTarget.isCompact) hx.1)
      filter_upwards [(finiteBarrier_dyadic_tendsto hHausdorff hU hTarget hlevel hbox
        (fun _ => hxB) tendsto_const_nhds).eventually (Ioi_mem_nhds hx.2)] with n hn
      rw [indicator_of_mem hx, positiveNicheOverlap, indicator_of_mem]
      exact ⟨hx, hn⟩
    · filter_upwards with n
      rw [indicator_of_notMem hx, positiveNicheOverlap, indicator_of_notMem]
      exact fun hm => hx hm.1
  have h := tendsto_setIntegral_moving_domain (fun n => measurable_const.indicator
    (hP.inter (measurableSet_lt measurable_const (continuous_finiteBarrier _ _ _ _).measurable)))
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    hflim (hHausdorff.middle_membership_ae hU hTarget) zero_le_one
    (fun n => (middleHalfInterval_subset (horizontalLeft_le_horizontalRight (hU n).nonempty
      (hU n).isCompact)).trans ((hU n).projection_subset_Icc_of_box (hbox n)))
    (fun n x _ => (norm_indicator_le_norm_self _ _).trans_eq norm_one)
  rwa [setIntegral_indicator hP, setIntegral_const, smul_eq_mul, mul_one, inter_eq_right.2
    (show P ⊆ middleHalfInterval _ _ from inter_subset_left)] at h

end AngularGrid

end AmbidextrousSofa
