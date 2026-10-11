module

public import AmbidextrousSofa.Analysis.DrySourceProjection

@[expose] public section

/-!
# Actual dry intervals are paid for by the horizontal top

The finite horizontal source identity retains the literal roof top leaf.
Its source mass bounds the inner floor mass, up to the actual summable
selection error. Hausdorff convergence localizes every height-one point
near the target top, while the dry-source cutoff removes finite positive
length from a fixed dry interval. The resulting inequality is proved for
an arbitrary full maximum using its own selected polygon sequence.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem CapHausdorffTendsto.eventually_top_points_near
    {U : ℕ → Set Plane} {K B : Set Plane} {s t ε : ℝ}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    (htop : ∀ p ∈ K, p.2 = 1 → p.1 ∈ Icc s t) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ p ∈ U n, p.2 = 1 → p.1 ∈ Icc (s - ε) (t + ε) := by
  by_contra hnot
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.mp hnot)
  push Not at hbad
  choose point hpoint hheight houtside using hbad
  obtain ⟨p, -, ms, hms, hp⟩ := hB.tendsto_subseq fun n => hbox _ (hpoint n)
  have hsub : CapHausdorffTendsto (fun n => U (φ (ms n))) K :=
    h.comp (hφ.comp hms).tendsto_atTop
  have hpt := htop p (hsub.mem_of_tendsto (fun _ => (hU _).isCompact) (fun _ => (hU _).nonempty)
    hK.isCompact hK.nonempty (fun n => hpoint (ms n)) hp)
    (isClosed_singleton.mem_of_tendsto hp.snd_nhds (.of_forall fun n => hheight (ms n)))
  -- the limit is a top point of `K`, but its abscissa is a limit of abscissae far from `[s, t]`
  exact isOpen_Ioo.isClosed_compl.mem_of_tendsto hp.fst_nhds
    (.of_forall fun n hn => houtside (ms n) (Ioo_subset_Icc_self hn))
    ⟨by linarith [hpt.1], by linarith [hpt.2]⟩

namespace FinitePolygon

variable {ι : Type*}

/-- The two charged top pieces are disjoint subsets of the actual top
projection. In particular their total mass is at most the whole top width. -/
theorem finiteWingMass_top_le [Fintype ι] {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) {s t : ℝ} (hst : s ≤ t)
    (htop : ∀ p ∈ U, p.2 = 1 → p.1 ∈ Icc s t) :
    finiteWingMass U normal none ≤ t - s := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hfin (l r : ℝ) (S : Set ℝ) : volume (Ioc l r ∩ S) ≠ ⊤ :=
    measure_inter_ne_top_of_left_ne_top measure_Ioc_lt_top.ne
  rw [finiteWingMass, WallExpr.sourceMass, WallExpr.sourceMass, ← measureReal_union
    (disjoint_left.2 fun x hA hB => ?_)
    (measurableSet_Ioc.inter (WallExpr.measurableSet_sourceSet _ _ _ _)) (hfin _ _ _) (hfin _ _ _),
    ← Real.volume_real_Icc_of_le hst]
  · refine measureReal_mono (fun x hx => htop (x, 1) ?_ rfl) measure_Icc_lt_top.ne
    have hx' : x ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rcases hx with hx | hx
      exacts [⟨hx.1.1.le, by linarith [hx.1.2]⟩, ⟨by linarith [hx.1.1], hx.1.2⟩]
    have h := capRoof_mem hU.isCompact (hU.horizontalProjection_eq_Icc ▸ hx')
    rw [← eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly hx', roofEnvelope,
      WallExpr.eval_eq_source, show roofExpr.source _ = none from hx.elim (·.2) (·.2)] at h
    simpa [wallSlope, roofIntercept] using h
  · linarith [hA.1.2, hB.1.1]

end FinitePolygon

namespace AngularGrid

open FinitePolygon

/-- The selected horizontal balance bounds inner floor mass by the
literal outer top source and its summable finite selection error. -/
theorem IsSelectedPolygon.interval_length_le_top_add_positive
    {target U : Set Plane} {L R coefficient a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target L R level coefficient U) (hc : 0 ≤ coefficient)
    (hab : a ≤ b) (ha : horizontalLeft U + capWidth U / 4 ≤ a)
    (hb : b ≤ horizontalRight U - capWidth U / 4) :
    b - a ≤ finiteWingMass U (normal (dyadic level)) none +
      finitePositiveLength U (normal (dyadic level)) (pairList (dyadic level)) none a b +
      ∑ j : SourceIndex (dyadic level), selectionDefect target U level coefficient j := by
  let e := barrierExpr (pairList (dyadic level)) none
  let slope := wallSlope (normal (dyadic level))
  let intercept := barrierIntercept (normal (dyadic level))
    fun i => support U (normal (dyadic level) i)
  have hlr := ha.trans (hab.trans hb)
  have hinj := wallSlopes_injective (dyadic level)
  have hab' := e.sum_sourceMass slope intercept hab
  have hlr' := e.sum_sourceMass slope intercept hlr
  rw [Fintype.sum_option, ← finitePositiveLength_eq_sum _ _ _ _ hinj hab] at hab'
  rw [Fintype.sum_option, ← finitePositiveLength_eq_sum _ _ _ _ hinj hlr] at hlr'
  have hfloor : e.sourceMass slope intercept a b none ≤ e.sourceMass slope intercept _ _ none :=
    measureReal_mono (fun x hx => ⟨⟨ha.trans_lt hx.1.1, hx.1.2.trans hb⟩, hx.2⟩)
      (measure_inter_ne_top_of_left_ne_top measure_Ioc_lt_top.ne)
  have hsum : ∑ j, -selectionDefect target U level coefficient j ≤
      ∑ j, (normal (dyadic level) j).2 * normalizedExposureDefect U (dyadic level) j := by
    refine Finset.sum_le_sum fun j _ => ?_
    have hs : (normal (dyadic level) j).2 ≤ 1 := by
      rw [normal_eq_unitNormal]; exact Real.sin_le_one _
    have h1 : _ ≤ (normal (dyadic level) j).2 * normalizedExposureDefect U _ j :=
      mul_le_mul_of_nonneg_left (hU.exposure_defect_div_ge hc j) (normal_snd_pos _ j).le
    linarith [mul_le_mul_of_nonneg_right hs (selectionDefect_nonneg target U level hc j)]
  rw [Finset.sum_neg_distrib, sum_sin_normalizedExposureDefect_eq_horizontal_balance hU.isCap]
    at hsum
  linarith [show capWidth U = horizontalRight U - horizontalLeft U from rfl]

theorem dry_interval_length_le_top_width_of_selected
    {target : Set Plane} {U : ℕ → Set Plane} {L R a b s t : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target L R (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hab : a ≤ b) (ha : horizontalLeft target + capWidth target / 4 < a)
    (hb : b < horizontalRight target - capWidth target / 4) (hst : s ≤ t)
    (htop : ∀ p ∈ target, p.2 = 1 → p.1 ∈ Icc s t)
    (hnegative : ∀ x ∈ Icc a b, ∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator target θ x < 0) : b - a ≤ t - s := by
  have hcap n := (hU n).isCap
  have hbox n := subset_symmetricBox_of_horizontalBox (hU n).inBox
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCompact hTarget.nonempty
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlim := ((tendsto_const_nhds (x := t - s + ε)).add
    (finitePositiveLength_tendsto_zero_on_dry_interval hHausdorff hcap hTarget hlevel
      (by positivity) hbox hab ha hb hnegative)).add
    (selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff)
  rw [add_zero, add_zero] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [(hl.add ((hr.sub hl).div_const 4)).eventually (gt_mem_nhds ha),
    (hr.sub ((hr.sub hl).div_const 4)).eventually (lt_mem_nhds hb),
    hHausdorff.eventually_top_points_near hcap hTarget (isCompact_Icc.prod isCompact_Icc) hbox
      htop (half_pos hε)] with n hnL hnR htopn
  have := (hU n).interval_length_le_top_add_positive (hc n) hab hnL.le hnR.le
  have := finiteWingMass_top_le (hcap n) _ (normal_snd_pos _) (hU n).polygon_eq
    (by linarith : s - ε / 2 ≤ t + ε / 2) htopn
  linarith

end AngularGrid

/-- The selected polygons and all their source errors are internal to
this theorem. The premise is literal strict wall geometry on a compact
interval of the actual maximum. -/
theorem IsFullCapMaximizer.dry_interval_length_le_top_width
    {U : Set Plane} (hU : IsFullCapMaximizer U) {a b s t : ℝ}
    (hab : a ≤ b) (ha : horizontalLeft U + capWidth U / 4 < a)
    (hb : b < horizontalRight U - capWidth U / 4) (hst : s ≤ t)
    (htop : ∀ p ∈ U, p.2 = 1 → p.1 ∈ Icc s t)
    (hnegative : ∀ x ∈ Icc a b, ∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2),
      secondWallNumerator U θ x < 0) : b - a ≤ t - s := by
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU
      (horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact)
      fun p hp => ⟨hU.isCap.fst_mem_Icc hp, hU.isCap.inStrip hp⟩
  exact AngularGrid.dry_interval_length_le_top_width_of_selected hU.isCap hV hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate hab ha hb hst htop hnegative

end AmbidextrousSofa
