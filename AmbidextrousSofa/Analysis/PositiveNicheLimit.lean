module

public import AmbidextrousSofa.Analysis.HorizontalWindowLimit

@[expose] public section

/-!
# The lower spatial limit of positive niche length

Intersecting each finite positive region with the target positive region
produces bounded indicators that converge everywhere except for the moving
window endpoints. The finite profiles need not have convergent zero sets.
The overlap integral converges to the actual target positive length and is
bounded above by the literal finite positive length. Both statements hold
for any measurable target profile and continuous finite profiles converging
to it on the box. Here they are applied to the full-angle niche; the partial
barrier uses them as well.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The overlap of a target positive set with the positive set of a continuous `f` is no
longer, on the middle window of `U`, than the positive set of `f` there. -/
theorem integral_positiveOverlap_le (target U : Set Plane) {g f : ℝ → ℝ} (hg : Measurable g)
    (hf : Continuous f) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩ {x | 0 < g x} ∩
        {x | 0 < f x}).indicator (fun _ => (1 : ℝ)) x) ≤
    volume.real (Ioc (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) ∩
      {x | 0 < f x}) := by
  change (∫ x in Icc (horizontalLeft U + capWidth U / 4)
    (horizontalRight U - capWidth U / 4), _) ≤ _
  rw [integral_Icc_eq_integral_Ioc, setIntegral_indicator
    (((measurableSet_middleHalfInterval _ _).inter (measurableSet_lt measurable_const hg)).inter
      (measurableSet_lt measurable_const hf.measurable)), setIntegral_const, smul_eq_mul, mul_one]
  exact measureReal_mono (fun x hx => ⟨hx.1, hx.2.2⟩)
    ((measure_mono inter_subset_left).trans_lt measure_Ioc_lt_top).ne

/-- Convergence of the finite profiles is used only at target points where the target profile
is strictly positive. Zero-height components may disappear. -/
theorem integral_positiveOverlap_tendsto {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {g : ℝ → ℝ} {f : ℕ → ℝ → ℝ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsDownwardCap (U n)) (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hHausdorff : CapHausdorffTendsto U target) (hg : Measurable g) (hf : ∀ n, Continuous (f n))
    (hlim : ∀ x ∈ Icc a b, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x in middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)),
      (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩ {x | 0 < g x} ∩
        {x | 0 < f n x}).indicator (fun _ => (1 : ℝ)) x) atTop
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
        {x | 0 < g x}))) := by
  set P := middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩ {x | 0 < g x}
  have hP : MeasurableSet P :=
    (measurableSet_middleHalfInterval _ _).inter (measurableSet_lt measurable_const hg)
  have hflim : ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => (P ∩ {x | 0 < f n x}).indicator
      (fun _ => (1 : ℝ)) x) atTop (𝓝 (P.indicator (fun _ => 1) x)) := by
    refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    by_cases hx : x ∈ P
    · filter_upwards [(hlim x ((hTarget.projection_subset_Icc_of_box hTargetBox)
        (middleHalfInterval_subset (horizontalLeft_le_horizontalRight hTarget.nonempty
          hTarget.isCompact) hx.1))).eventually (Ioi_mem_nhds hx.2)] with n hn
      rw [indicator_of_mem hx, indicator_of_mem]
      exact ⟨hx, hn⟩
    · filter_upwards with n
      rw [indicator_of_notMem hx, indicator_of_notMem fun hm => hx hm.1]
  have h := tendsto_setIntegral_moving_domain (fun n => measurable_const.indicator
    (hP.inter (measurableSet_lt measurable_const (hf n).measurable)))
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    hflim (hHausdorff.middle_membership_ae hU hTarget) zero_le_one
    (fun n => (middleHalfInterval_subset (horizontalLeft_le_horizontalRight (hU n).nonempty
      (hU n).isCompact)).trans ((hU n).projection_subset_Icc_of_box (hbox n)))
    (fun n x _ => (norm_indicator_le_norm_self _ _).trans_eq norm_one)
  rwa [setIntegral_indicator hP, setIntegral_const, smul_eq_mul, mul_one,
    inter_eq_right.2 (show P ⊆ middleHalfInterval _ _ from inter_subset_left)] at h

namespace AngularGrid

open FinitePolygon

def positiveNicheOverlap (target U : Set Plane) (grid : Finset QuarterAngle) : ℝ → ℝ :=
  (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
    {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x} ∩
    {x : ℝ | 0 < finiteBarrier U (normal grid) (pairList grid) none x}).indicator
      (fun _ => 1)

theorem integral_positiveNicheOverlap_le {target U : Set Plane}
    (hTarget : IsDownwardCap target) (grid : Finset QuarterAngle) :
    (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
      positiveNicheOverlap target U grid x) ≤
    finitePositiveLength U (normal grid) (pairList grid) none
      (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) :=
  integral_positiveOverlap_le target U
    (measurable_sweptNiche hTarget.isCompact (by linarith [Real.pi_pos]) le_rfl)
    (continuous_finiteBarrier U _ _ _)

theorem integral_positiveNicheOverlap_tendsto
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ} {level : ℕ → ℕ}
    (hTarget : IsDownwardCap target) (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsDownwardCap (U n)) (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop) :
    Tendsto (fun n => ∫ x in middleHalfInterval
      (horizontalLeft (U n)) (horizontalRight (U n)),
        positiveNicheOverlap target (U n) (dyadic (level n)) x) atTop
      (𝓝 (volume.real (middleHalfInterval (horizontalLeft target) (horizontalRight target) ∩
        {x : ℝ | 0 < sweptNiche target (Real.pi / 2) x}))) :=
  integral_positiveOverlap_tendsto hTarget hTargetBox hU hbox hHausdorff
    (measurable_sweptNiche hTarget.isCompact (by linarith [Real.pi_pos]) le_rfl)
    (fun _ => continuous_finiteBarrier _ _ _ _) fun _ hx =>
      finiteBarrier_dyadic_tendsto hHausdorff hU hTarget hlevel hbox (fun _ => hx)
        tendsto_const_nhds

end AngularGrid

end AmbidextrousSofa
