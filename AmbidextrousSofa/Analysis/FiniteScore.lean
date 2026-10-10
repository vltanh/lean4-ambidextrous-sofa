import AmbidextrousSofa.Analysis.Circumscription
import AmbidextrousSofa.Analysis.GridNiche

/-!
# Continuous finite spatial objectives and actual selected polygons

The finite objective retains the cap's own moving middle window. Its roof
integral is continuous by actual Hausdorff convergence of caps; its finite
physical barrier is jointly continuous. Compactness supplies an actual
maximizing cap. Circumscription preserves the sampled supports and improves
the charged roof, so it supplies an actual maximizing polygon in the same
box. No polygon existence or maximization field is assumed.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

theorem intervalSpatialScore_eq_setIntegrals (roof niche : ℝ → ℝ) {l r : ℝ}
    (hlr : l ≤ r) (hroof : ∀ a b, IntervalIntegrable roof volume a b) :
    intervalSpatialScore roof niche l r =
      (∫ x in Icc l r \ middleHalfInterval l r, roof x) -
        ∫ x in middleHalfInterval l r, niche x := by
  have hm : l + (r - l) / 4 ≤ r - (r - l) / 4 := by linarith
  have hroofI : IntegrableOn roof (Icc l r) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mp (hroof l r)
  rw [setIntegral_sdiff (measurableSet_middleHalfInterval _ _) hroofI
    (middleHalfInterval_subset hlr)]
  simp only [middleHalfInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hlr, ← intervalIntegral.integral_of_le hm]
  have hfirst := intervalIntegral.integral_add_adjacent_intervals
    (hroof l (l + (r - l) / 4))
    (hroof (l + (r - l) / 4) (r - (r - l) / 4))
  have hsecond := intervalIntegral.integral_add_adjacent_intervals
    (hroof l (r - (r - l) / 4)) (hroof (r - (r - l) / 4) r)
  unfold intervalSpatialScore
  linarith

theorem finiteSpatialScore_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    finiteSpatialScore U normal corners terminal =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        finiteBarrier U normal corners terminal x := by
  apply intervalSpatialScore_eq_setIntegrals _ _
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
  intro a b
  apply intervalIntegrable_iff'.mpr
  simpa only [uIcc] using hU.integrableOn_capRoof_Icc (min a b) (max a b)

theorem continuous_finiteBarrier_caps (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (fun p : CompactCap × ℝ => finiteBarrier p.1.carrier normal corners terminal p.2) := by
  have heq : (fun p : CompactCap × ℝ => finiteBarrier p.1.carrier normal corners terminal p.2) =
      fun p => (barrierExpr corners terminal).eval (fun i =>
        wallSlope normal i * p.2 + barrierIntercept normal (fun j => support p.1.carrier (normal j)) i) := by
    funext p
    exact finiteBarrier_eq_eval normal _ (fun _ => rfl) corners terminal p.2
  rw [heq]
  apply WallExpr.continuous_eval
  intro i
  cases i with
  | none => simp only [wallSlope, barrierIntercept, zero_mul, zero_add]; exact continuous_const
  | some i =>
    have hs : Continuous (fun p : CompactCap × ℝ => support p.1.carrier (normal i)) :=
      continuous_capSupport.comp (continuous_fst.prodMk continuous_const)
    exact (continuous_const.mul continuous_snd).add
      ((hs.sub continuous_const).div_const (normal i).2)

theorem middle_finiteBarrier_integral_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    Tendsto (fun n => ∫ x in middleHalfInterval
        (horizontalLeft (U n)) (horizontalRight (U n)), finiteBarrier (U n) normal corners terminal x)
      atTop (𝓝 (∫ x in middleHalfInterval (horizontalLeft K) (horizontalRight K),
        finiteBarrier K normal corners terminal x)) := by
  have hc := continuous_finiteBarrier_caps normal corners terminal
  obtain ⟨C, hC⟩ := ((isCompact_boxedCaps hB).prod
    (isCompact_Icc : IsCompact (Icc (horizontalLeft B) (horizontalRight B)))).bddAbove_image
      hc.continuousOn
  have hwindow : ∀ n, middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆
      Icc (horizontalLeft B) (horizontalRight B) := fun n =>
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      (hU n).nonempty (hU n).isCompact)).trans
      ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  have hcaps := IsDownwardCap.tendsto_toCompactCap hU hK h
  apply tendsto_setIntegral_moving_domain
    (fun n => (continuous_finiteBarrier (U n) normal corners terminal).measurable)
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    (Eventually.of_forall (fun x => (hc.tendsto (hK.toCompactCap, x)).comp
      (hcaps.prodMk_nhds tendsto_const_nhds)))
    (h.middle_membership_ae hU hK) (C := max C 0) (le_max_right _ _) hwindow
  intro n x hx
  rw [Real.norm_of_nonneg (finiteBarrier_nonneg _ _ _ _ _)]
  have hp : ((hU n).toCompactCap, x) ∈
      boxedCaps B ×ˢ Icc (horizontalLeft B) (horizontalRight B) :=
    ⟨hsub n, hwindow n hx⟩
  exact (hC (mem_image_of_mem _ hp)).trans (le_max_left _ _)

theorem finiteSpatialScore_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    Tendsto (fun n => finiteSpatialScore (U n) normal corners terminal) atTop
      (𝓝 (finiteSpatialScore K normal corners terminal)) := by
  have hlim := (h.exterior_roof_integral_tendsto hU hK hB hsub).sub
    (middle_finiteBarrier_integral_tendsto h hU hK hB hsub normal corners terminal)
  have hScore (n : ℕ) := finiteSpatialScore_eq_integrals (hU n) normal corners terminal
  have hScoreK := finiteSpatialScore_eq_integrals hK normal corners terminal
  simpa only [← hScore, ← hScoreK] using hlim

theorem continuous_finiteSpatialScore_box {B : Set Plane} (hB : IsCompact B)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (fun U : boxedCaps B => finiteSpatialScore U.val.carrier normal corners terminal) := by
  apply continuous_iff_seqContinuous.mpr
  intro U K hlim
  have hc : Tendsto (fun n => (U n).val) atTop (𝓝 K.val) :=
    (continuous_subtype_val.tendsto K).comp hlim
  exact finiteSpatialScore_tendsto (CompactCap.tendsto_iff_hausdorff.mp hc)
    (fun n => (U n).val.isCap) K.val.isCap hB (fun n => (U n).property) normal corners terminal

theorem continuousOn_finiteSpatialScore_box {B : Set Plane} (hB : IsCompact B)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    ContinuousOn (fun U : CompactCap => finiteSpatialScore U.carrier normal corners terminal)
      (boxedCaps B) :=
  continuousOn_iff_continuous_restrict.mpr
    (continuous_finiteSpatialScore_box hB normal corners terminal)

theorem continuous_sampledPenalty_caps [Fintype ι] (normal : ι → Plane) (weight target : ι → ℝ) :
    Continuous (fun U : CompactCap => sampledPenalty U.carrier normal weight target) := by
  unfold sampledPenalty heightPenalty
  apply continuous_finsetSum
  intro i _
  have hs : Continuous (fun U : CompactCap => support U.carrier (normal i)) :=
    continuous_capSupport.comp (continuous_id.prodMk continuous_const)
  exact continuous_const.mul ((hs.sub continuous_const).pow 2)

theorem circumscription_idem {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane) :
    circumscription (circumscription U normal) normal = circumscription U normal := by
  have hprojection := horizontalProjection_circumscription hU normal
  have hleft : horizontalLeft (circumscription U normal) = horizontalLeft U :=
    congrArg sInf hprojection
  have hright : horizontalRight (circumscription U normal) = horizontalRight U :=
    congrArg sSup hprojection
  have hsupport : (fun i => support (circumscription U normal) (normal i)) =
      fun i => support U (normal i) := funext (support_circumscription hU normal)
  unfold circumscription
  rw [hleft, hright, hsupport]

/-- Every nonempty boxed cap domain has an actual polygon maximizing the
finite physical objective minus the displayed sampled support penalty. -/
theorem exists_boxed_selected_polygon [Fintype ι] (normal : ι → Plane)
    (hnormal : ∀ i, 0 ≤ (normal i).2) (weight target : ι → ℝ)
    (corners : List (ι × ι)) (terminal : Option ι) {a b : ℝ}
    {V : Set Plane} (hV : IsDownwardCap V) (hVB : V ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) :
    ∃ K : Set Plane, IsDownwardCap K ∧ K ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 ∧
      K = circumscription K normal ∧
      ∀ U : Set Plane, IsDownwardCap U → U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        finiteSpatialScore U normal corners terminal - sampledPenalty U normal weight target ≤
          finiteSpatialScore K normal corners terminal - sampledPenalty K normal weight target := by
  let B : Set Plane := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  let Φ : CompactCap → ℝ := fun U =>
    finiteSpatialScore U.carrier normal corners terminal - sampledPenalty U.carrier normal weight target
  have hΦ : ContinuousOn Φ (boxedCaps B) :=
    (continuousOn_finiteSpatialScore_box hB normal corners terminal).sub
      (continuous_sampledPenalty_caps normal weight target).continuousOn
  obtain ⟨C, hCB, hmax⟩ := exists_boxed_cap_max hB hV hVB hΦ
  let K : Set Plane := circumscription C.carrier normal
  have hK : IsDownwardCap K := isDownwardCap_circumscription C.isCap normal hnormal
  have hKB : K ⊆ B := circumscription_subset_box C.isCap normal hCB
  have hImprove : Φ C ≤ Φ hK.toCompactCap := by
    change finiteSpatialScore C.carrier normal corners terminal - sampledPenalty C.carrier normal weight target ≤
      finiteSpatialScore (circumscription C.carrier normal) normal corners terminal -
        sampledPenalty (circumscription C.carrier normal) normal weight target
    rw [sampledPenalty_circumscription C.isCap normal weight target]
    exact sub_le_sub_right (finiteSpatialScore_le_circumscription C.isCap normal hnormal corners terminal) _
  refine ⟨K, hK, hKB, (circumscription_idem C.isCap normal).symm, ?_⟩
  intro U hU hUB
  exact (hmax hU.toCompactCap hUB).trans hImprove

end FinitePolygon

/-- The actual cap score is the three-integral spatial objective on its own
projection. Only the roof's proved local integrability is needed for this
identity; no global continuity of its zero extension is asserted. -/
theorem IsDownwardCap.capScore_eq_intervalSpatialScore {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) :
    capScore U α = intervalSpatialScore (capRoof U) (partialBarrier U α)
      (horizontalLeft U) (horizontalRight U) := by
  rw [capScore_eq_integrals]
  symm
  apply FinitePolygon.intervalSpatialScore_eq_setIntegrals _ _
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
  intro a b
  apply intervalIntegrable_iff'.mpr
  simpa only [uIcc] using hU.integrableOn_capRoof_Icc (min a b) (max a b)

end AmbidextrousSofa
