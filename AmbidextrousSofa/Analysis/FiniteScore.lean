module

public import AmbidextrousSofa.Analysis.Circumscription
public import AmbidextrousSofa.Analysis.GridNiche

@[expose] public section

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
  rw [setIntegral_sdiff (measurableSet_middleHalfInterval _ _)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mp (hroof l r))
    (middleHalfInterval_subset hlr)]
  simp only [middleHalfInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hlr,
    ← intervalIntegral.integral_of_le (show l + (r - l) / 4 ≤ r - (r - l) / 4 by linarith)]
  unfold intervalSpatialScore
  linarith [intervalIntegral.integral_add_adjacent_intervals (hroof l (l + (r - l) / 4))
      (hroof _ (r - (r - l) / 4)),
    intervalIntegral.integral_add_adjacent_intervals (hroof l (r - (r - l) / 4)) (hroof _ r)]

theorem finiteSpatialScore_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    finiteSpatialScore U normal corners terminal =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        finiteBarrier U normal corners terminal x :=
  intervalSpatialScore_eq_setIntegrals _ _
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
    fun _ _ => (hU.integrableOn_capRoof_Icc _ _).intervalIntegrable

theorem continuous_finiteBarrier_caps (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (fun p : CompactCap × ℝ => finiteBarrier p.1.carrier normal corners terminal p.2) := by
  refine ((barrierExpr corners terminal).continuous_eval fun i => ?_).congr fun p =>
    (finiteBarrier_eq_eval normal _ (fun _ => rfl) corners terminal p.2).symm
  rcases i with _ | i
  · simpa [wallSlope, barrierIntercept] using continuous_const
  · exact (continuous_const.mul continuous_snd).add
      (((continuous_capSupport.comp (continuous_fst.prodMk continuous_const)).sub
        continuous_const).div_const _)

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
    (isCompact_Icc (a := horizontalLeft B) (b := horizontalRight B))).bddAbove_image
      hc.continuousOn
  have hwindow : ∀ n, middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ⊆
      Icc (horizontalLeft B) (horizontalRight B) := fun n =>
    (middleHalfInterval_subset (horizontalLeft_le_horizontalRight
      (hU n).nonempty (hU n).isCompact)).trans
      ((hU n).projection_subset_bounds_of_subset hB (hsub n))
  refine tendsto_setIntegral_moving_domain
    (fun n => (continuous_finiteBarrier (U n) normal corners terminal).measurable)
    (fun n => measurableSet_middleHalfInterval _ _) (measurableSet_middleHalfInterval _ _)
    (Eventually.of_forall (fun x => (hc.tendsto (hK.toCompactCap, x)).comp
      ((IsDownwardCap.tendsto_toCompactCap hU hK h).prodMk_nhds tendsto_const_nhds)))
    (h.middle_membership_ae hU hK) (C := max C 0) (le_max_right _ _) hwindow fun n x hx => ?_
  rw [Real.norm_of_nonneg (finiteBarrier_nonneg _ _ _ _ _)]
  exact (hC (mem_image_of_mem _ (show ((hU n).toCompactCap, x) ∈ boxedCaps B ×ˢ _ from
    ⟨hsub n, hwindow n hx⟩))).trans (le_max_left _ _)

theorem continuous_finiteSpatialScore_box {B : Set Plane} (hB : IsCompact B)
    (normal : ι → Plane) (corners : List (ι × ι)) (terminal : Option ι) :
    Continuous (fun U : boxedCaps B => finiteSpatialScore U.val.carrier normal corners terminal) := by
  refine continuous_iff_seqContinuous.mpr fun U K hlim => ?_
  have h : CapHausdorffTendsto (fun n => (U n).val.carrier) K.val.carrier :=
    CompactCap.tendsto_iff_hausdorff.mp ((continuous_subtype_val.tendsto K).comp hlim)
  have hU (n : ℕ) := (U n).val.isCap
  have hsub (n : ℕ) := (U n).property
  simpa only [Function.comp_def, ← finiteSpatialScore_eq_integrals (hU _) normal corners terminal,
    ← finiteSpatialScore_eq_integrals K.val.isCap normal corners terminal] using
    (h.exterior_roof_integral_tendsto hU K.val.isCap hB hsub).sub
      (middle_finiteBarrier_integral_tendsto h hU K.val.isCap hB hsub normal corners terminal)

theorem continuous_sampledPenalty_caps [Fintype ι] (normal : ι → Plane) (weight target : ι → ℝ) :
    Continuous (fun U : CompactCap => sampledPenalty U.carrier normal weight target) :=
  continuous_finsetSum _ fun _ _ => continuous_const.mul
    (((continuous_capSupport.comp (continuous_id.prodMk continuous_const)).sub
      continuous_const).pow 2)

theorem circumscription_idem {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane) :
    circumscription (circumscription U normal) normal = circumscription U normal := by
  rw [circumscription, horizontalLeft, horizontalRight,
    horizontalProjection_circumscription hU normal, funext (support_circumscription hU normal)]
  rfl

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
  have hB : IsCompact (Icc a b ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hCB, hmax⟩ := exists_boxed_cap_max hB hV hVB (Φ := fun U =>
      finiteSpatialScore U.carrier normal corners terminal -
        sampledPenalty U.carrier normal weight target)
    ((continuousOn_iff_continuous_domRestrict.mpr
      (continuous_finiteSpatialScore_box hB normal corners terminal)).sub
      (continuous_sampledPenalty_caps normal weight target).continuousOn)
  refine ⟨_, isDownwardCap_circumscription C.isCap normal hnormal,
    circumscription_subset_box C.isCap normal hCB, (circumscription_idem C.isCap normal).symm,
    fun U hU hUB => (hmax hU.toCompactCap hUB).trans ?_⟩
  rw [sampledPenalty_circumscription C.isCap normal weight target]
  exact sub_le_sub_right
    (finiteSpatialScore_le_circumscription C.isCap normal hnormal corners terminal) _

end FinitePolygon

/-- The actual cap score is the three-integral spatial objective on its own
projection. Only the roof's proved local integrability is needed for this
identity; no global continuity of its zero extension is asserted. -/
theorem IsDownwardCap.capScore_eq_intervalSpatialScore {U : Set Plane}
    (hU : IsDownwardCap U) (α : ℝ) :
    capScore U α = intervalSpatialScore (capRoof U) (partialBarrier U α)
      (horizontalLeft U) (horizontalRight U) :=
  (capScore_eq_integrals U α).trans (FinitePolygon.intervalSpatialScore_eq_setIntegrals _ _
    (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)
    fun _ _ => (hU.integrableOn_capRoof_Icc _ _).intervalIntegrable).symm

end AmbidextrousSofa
