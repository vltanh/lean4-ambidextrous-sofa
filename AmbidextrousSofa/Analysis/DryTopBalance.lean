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
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ p ∈ U n,
      p.2 = 1 ∧ p.1 ∉ Icc (s - ε) (t + ε) := by
    intro k
    by_contra hk
    apply hnot
    refine eventually_atTop.mpr ⟨k, ?_⟩
    intro n hn p hp hpy
    by_contra hpx
    exact hk ⟨n, hn, p, hp, hpy, hpx⟩
  choose ns hns point hpoint hheight houtside using hbad
  obtain ⟨p, _, ms, hms, hp⟩ := hB.tendsto_subseq (fun n => hbox (ns n) (hpoint n))
  let seq : ℕ → ℕ := fun n => ns (ms n)
  have hseq : Tendsto seq atTop atTop :=
    (tendsto_atTop_mono hns tendsto_id).comp hms.tendsto_atTop
  have hpK : p ∈ K := CapHausdorffTendsto.mem_of_tendsto (U := fun n => U (seq n)) (h.comp hseq)
    (fun n => (hU (seq n)).isCompact) (fun n => (hU (seq n)).nonempty)
    hK.isCompact hK.nonempty (fun n => hpoint (ms n)) hp
  have hpy : p.2 = 1 := tendsto_nhds_unique hp.snd_nhds
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
      (Eventually.of_forall (fun n => (hheight (ms n)).symm)))
  have hpt := htop p hpK hpy
  have hnear := hp.fst_nhds.eventually (Ioo_mem_nhds
    (show s - ε < p.1 by linarith only [hpt.1, hε])
    (show p.1 < t + ε by linarith only [hpt.2, hε]))
  obtain ⟨n, hn⟩ := hnear.exists
  exact houtside (ms n) ⟨hn.1.le, hn.2.le⟩

namespace FinitePolygon

variable {ι : Type*}

theorem topSource_mem_cap [Fintype ι] {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) {x : ℝ}
    (hx : x ∈ Icc (horizontalLeft U) (horizontalRight U))
    (hsource : x ∈ (roofExpr (ι := ι)).sourceSet (wallSlope normal)
      (roofIntercept normal (fun i => support U (normal i))) none) : (x, 1) ∈ U := by
  have hroof := capRoof_eq_roofEnvelope_of_circumscription hU normal hnormal hpoly hx
  have hvalue := (roofExpr (ι := ι)).eval_eq_source
    (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i)
  change (roofExpr (ι := ι)).source
    (fun i => wallSlope normal i * x + roofIntercept normal (fun j => support U (normal j)) i) =
      none at hsource
  rw [hsource] at hvalue
  have hheight : capRoof U x = 1 := by
    exact hroof.trans (by
      simpa only [roofEnvelope, wallSlope, roofIntercept, zero_mul, zero_add] using hvalue)
  rw [← hheight]
  apply capRoof_mem hU.isCompact
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  exact hx

/-- The two charged top pieces are disjoint subsets of the actual top
projection. In particular their total mass is at most the whole top width. -/
theorem finiteWingMass_top_le [Fintype ι] {U : Set Plane} (hU : IsDownwardCap U)
    (normal : ι → Plane) (hnormal : ∀ i, 0 < (normal i).2)
    (hpoly : U = circumscription U normal) {s t : ℝ} (hst : s ≤ t)
    (htop : ∀ p ∈ U, p.2 = 1 → p.1 ∈ Icc s t) :
    finiteWingMass U normal none ≤ t - s := by
  classical
  let F := (roofExpr (ι := ι)).sourceSet (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) none
  let A := Ioc (horizontalLeft U) (horizontalLeft U + capWidth U / 4) ∩ F
  let B := Ioc (horizontalRight U - capWidth U / 4) (horizontalRight U) ∩ F
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hgap : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth
    linarith only [hlr]
  have hJL : horizontalLeft U + capWidth U / 4 ≤ horizontalRight U := by
    unfold capWidth
    linarith only [hlr]
  have hJR : horizontalLeft U ≤ horizontalRight U - capWidth U / 4 := by
    unfold capWidth
    linarith only [hlr]
  have hdisjoint : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact not_lt_of_ge (hxA.1.2.trans hgap) hxB.1.1
  have hF : MeasurableSet F := (roofExpr (ι := ι)).measurableSet_sourceSet _ _ _
  have hAf : volume A ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono inter_subset_left) (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top)).ne
  have hBf : volume B ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono inter_subset_left) (by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top)).ne
  have hsub : A ∪ B ⊆ Icc s t := by
    intro x hx
    have hxproj : x ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rcases hx with hx | hx
      · exact ⟨hx.1.1.le, hx.1.2.trans hJL⟩
      · exact ⟨hJR.trans hx.1.1.le, hx.1.2⟩
    have hxsource : x ∈ F := hx.elim (fun h => h.2) (fun h => h.2)
    exact htop (x, 1) (topSource_mem_cap hU normal hnormal hpoly hxproj hxsource) rfl
  change volume.real A + volume.real B ≤ t - s
  rw [← measureReal_union hdisjoint (measurableSet_Ioc.inter hF) hAf hBf]
  exact (measureReal_mono hsub (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).trans_eq
    (Real.volume_real_Icc_of_le hst)

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
  classical
  let grid := dyadic level
  let e := barrierExpr (pairList grid) (none : Option (SourceIndex grid))
  let slope := wallSlope (normal grid)
  let intercept := barrierIntercept (normal grid) (fun i => support U (normal grid i))
  let l := horizontalLeft U + capWidth U / 4
  let r := horizontalRight U - capWidth U / 4
  have hlr : l ≤ r := ha.trans (hab.trans hb)
  have hpartition : e.sourceMass slope intercept a b none +
      finitePositiveLength U (normal grid) (pairList grid) none a b = b - a := by
    rw [finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective grid) hab]
    simpa only [Fintype.sum_option] using e.sum_sourceMass slope intercept hab
  have hwhole : e.sourceMass slope intercept l r none +
      finitePositiveLength U (normal grid) (pairList grid) none l r = capWidth U / 2 := by
    have h := e.sum_sourceMass slope intercept hlr
    rw [Fintype.sum_option, ← finitePositiveLength_eq_sum U (normal grid) (pairList grid)
      none (wallSlopes_injective grid) hlr] at h
    convert h using 1
    dsimp only [l, r, capWidth]
    ring
  have hfloor : e.sourceMass slope intercept a b none ≤ e.sourceMass slope intercept l r none := by
    apply measureReal_mono
    · intro x hx
      exact ⟨⟨ha.trans_lt hx.1.1, hx.1.2.trans hb⟩, hx.2⟩
    · apply (lt_of_le_of_lt (measure_mono inter_subset_left) ?_).ne
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
  have hdefect (j : SourceIndex grid) :
      -selectionDefect target U level coefficient j ≤
        (normal grid j).2 * normalizedExposureDefect U grid j := by
    have hE := selectionDefect_nonneg target U level hc j
    have hD := hU.exposure_defect_div_ge hc j
    have hmul := mul_le_mul_of_nonneg_left hD (normal_snd_pos grid j).le
    have hs : (normal grid j).2 ≤ 1 := by
      rw [normal_eq_unitNormal]
      exact Real.sin_le_one _
    have herror := mul_le_mul_of_nonneg_right hs hE
    change _ ≤ (normal grid j).2 * normalizedExposureDefect U grid j at hmul
    nlinarith only [hmul, herror]
  have hsum : -(∑ j : SourceIndex grid, selectionDefect target U level coefficient j) ≤
      ∑ j : SourceIndex grid, (normal grid j).2 * normalizedExposureDefect U grid j := by
    simpa only [Finset.sum_neg_distrib] using
      (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hdefect j))
  rw [sum_sin_normalizedExposureDefect_eq_horizontal_balance hU.isCap grid] at hsum
  change -(∑ j : SourceIndex grid, selectionDefect target U level coefficient j) ≤
    finitePositiveLength U (normal grid) (pairList grid) none l r -
      (capWidth U / 2 - finiteWingMass U (normal grid) none) at hsum
  linarith only [hpartition, hwhole, hfloor, hsum]

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
  let B : ℝ := |L| + |R| + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hbox : ∀ n, U n ⊆ Icc (-B) B ×ˢ Icc (0 : ℝ) 1 :=
    fun n => subset_symmetricBox_of_horizontalBox (hU n).inBox
  have hpositive := finitePositiveLength_tendsto_zero_on_dry_interval hHausdorff hcap hTarget
    hlevel hB hbox hab ha hb hnegative
  have herror := selectionDefect_sum_tendsto (level := level) hTarget hcap hc hrate hHausdorff
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCompact hTarget.nonempty
  have hjL := hl.add ((hr.sub hl).div_const 4)
  have hjR := hr.sub ((hr.sub hl).div_const 4)
  have hinside : ∀ᶠ n in atTop,
      horizontalLeft (U n) + capWidth (U n) / 4 ≤ a ∧
      b ≤ horizontalRight (U n) - capWidth (U n) / 4 := by
    filter_upwards [hjL.eventually (Iio_mem_nhds ha), hjR.eventually (Ioi_mem_nhds hb)]
      with n hnL hnR
    exact ⟨hnL.le, hnR.le⟩
  have hbound (ε : ℝ) (hε : 0 < ε) : b - a ≤ t - s + 2 * ε := by
    have htopN := hHausdorff.eventually_top_points_near hcap hTarget
      (isCompact_Icc.prod isCompact_Icc) hbox htop hε
    have hinequality : ∀ᶠ n in atTop, b - a ≤ t - s + 2 * ε +
        finitePositiveLength (U n) (normal (dyadic (level n)))
          (pairList (dyadic (level n))) none a b +
        ∑ j : SourceIndex (dyadic (level n)),
          selectionDefect target (U n) (level n) (coefficient n) j := by
      filter_upwards [hinside, htopN] with n hn htopn
      have hsource := (hU n).interval_length_le_top_add_positive (hc n) hab hn.1 hn.2
      have htopmass := finiteWingMass_top_le (hcap n) (normal (dyadic (level n)))
        (normal_snd_pos (dyadic (level n))) (hU n).polygon_eq
        (show s - ε ≤ t + ε by linarith only [hst, hε]) htopn
      linarith only [hsource, htopmass]
    have hconstant : Tendsto (fun _ : ℕ => t - s + 2 * ε) atTop (𝓝 (t - s + 2 * ε)) :=
      tendsto_const_nhds
    have hlim := (hconstant.add hpositive).add herror
    have hresult := ge_of_tendsto hlim hinequality
    simpa only [add_zero] using hresult
  by_contra hnot
  have hgap : 0 < (b - a) - (t - s) := sub_pos.mpr (lt_of_not_ge hnot)
  have h := hbound (((b - a) - (t - s)) / 4) (by positivity)
  linarith only [h, hgap]

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
  let L := horizontalLeft U - 1
  let R := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hLR : L ≤ R := by dsimp only [L, R]; linarith only [hlr]
  have hbox : U ⊆ Icc L R ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx := hU.isCap.fst_mem_Icc hp
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp only [L]; linarith only [hx.1]
    · dsimp only [R]; linarith only [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hLR hbox
  exact AngularGrid.dry_interval_length_le_top_width_of_selected hU.isCap hV hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate hab ha hb hst htop hnegative

end AmbidextrousSofa
