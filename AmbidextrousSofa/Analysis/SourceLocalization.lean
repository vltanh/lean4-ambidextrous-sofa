import AmbidextrousSofa.Analysis.FiniteGraphFlux

/-!
# Actual finite sources localize at positive limiting graph pieces

The positive part of the two-wall minimum is jointly continuous in the
actual cap, abscissa and closed quarter angle, including the two axis
angles. Every selected finite source realizes that clipped value. Hence
compactness localizes the finite source angles in any open set containing
all actual maximizing angles of a compact limiting graph piece. This
argument permits several maximizing angles, including tangency plateaus.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem CapHausdorffTendsto.fullWallClip_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {point angle : ℕ → ℝ} {x t : ℝ}
    (hx : Tendsto point atTop (𝓝 x)) (ht : Tendsto angle atTop (𝓝 t))
    (htmem : t ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Tendsto (fun n => fullWallClip (hU n).toCompactCap (point n) (angle n)) atTop
      (𝓝 (fullWallClip hK.toCompactCap x t)) := by
  have hcap := IsDownwardCap.tendsto_toCompactCap hU hK h
  exact (continuousAt_fullWallClip htmem).tendsto.comp
    ((hcap.prodMk_nhds hx).prodMk_nhds ht)

namespace AngularGrid

open FinitePolygon

theorem sourceQuarterAngle_mem (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    sourceQuarterAngle (fullAngle grid j) ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [sourceQuarterAngle_fullAngle]
  cases j with
  | inl t => exact interiorPoint_mem grid t
  | inr t => exact interiorPoint_mem grid t

theorem innerSource_cornerWall (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    cornerWall U (sourceQuarterAngle (fullAngle grid j)) x =
      finiteBarrier U (normal grid) (pairList grid) none x := by
  rw [sourceQuarterAngle_fullAngle]
  cases j with
  | inl t =>
    have hsource := innerSource_height U grid (Sum.inl t) hx
    have hcomp := first_source_le_companion U grid t hx
    simp only [normal, supportWall_unitNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    exact (min_eq_left hcomp).trans hsource.symm
  | inr t =>
    have hsource := innerSource_height U grid (Sum.inr t) hx
    have hcomp := second_source_le_first U grid t hx
    simp only [normal, supportWall_companionNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    exact (min_eq_right hcomp).trans hsource.symm

theorem innerSource_fullWallClip {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U grid j) :
    fullWallClip hU.toCompactCap x (sourceQuarterAngle (fullAngle grid j)) =
      finiteBarrier U (normal grid) (pairList grid) none x := by
  change max (cornerWall U (sourceQuarterAngle (fullAngle grid j)) x) 0 = _
  rw [innerSource_cornerWall U grid j hx]
  exact max_eq_left (finiteBarrier_nonneg U (normal grid) (pairList grid) none x)

/-- Positivity of a compact limiting graph piece persists for the
literal finite sampled niches. The abscissae may vary with the cap. -/
theorem eventually_finiteBarrier_pos_on_compact
    {U : ℕ → Set Plane} {K : Set Plane} {level : ℕ → ℕ} {a b : ℝ} {F : Set ℝ}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hlevel : Tendsto level atTop atTop)
    (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hF : IsCompact F) (hFbox : F ⊆ Icc a b)
    (hpositive : ∀ x ∈ F, 0 < sweptNiche K (Real.pi / 2) x) :
    ∀ᶠ n in atTop, ∀ x ∈ F,
      0 < finiteBarrier (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none x := by
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ x ∈ F,
      ¬ 0 < finiteBarrier (U n) (normal (dyadic (level n)))
        (pairList (dyadic (level n))) none x := by
    intro k
    by_contra hk
    apply hnot
    refine eventually_atTop.mpr ⟨k, ?_⟩
    intro n hn x hx
    by_contra hneg
    exact hk ⟨n, hn, x, hx, hneg⟩
  choose ns hns point hpoint hnonpos using hbad
  obtain ⟨x, hx, ms, hms, hpointlim⟩ := hF.tendsto_subseq hpoint
  let seq : ℕ → ℕ := fun n => ns (ms n)
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hseq : Tendsto seq atTop atTop := hnsTop.comp hms.tendsto_atTop
  have hfinite := finiteBarrier_dyadic_tendsto (hHausdorff.comp hseq)
    (fun n => hU (seq n)) hK (hlevel.comp hseq) (fun n => hbox (seq n))
    (fun n => hFbox (hpoint (ms n))) hpointlim
  have hle : sweptNiche K (Real.pi / 2) x ≤ 0 := le_of_tendsto hfinite
    (Eventually.of_forall (fun n => le_of_not_gt (hnonpos (ms n))))
  exact not_lt_of_ge hle (hpositive x hx)

/-- Only actual maximizing angles of the closed-angle clipped wall
family are used. The open set can contain a whole plateau of maximizing
parameters; uniqueness is not assumed as a hidden regularity premise. -/
theorem eventually_innerSources_in_open_of_maximizers
    {U : ℕ → Set Plane} {K : Set Plane} {level : ℕ → ℕ} {a b : ℝ} {F V : Set ℝ}
    (hHausdorff : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) (hlevel : Tendsto level atTop atTop)
    (hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hF : IsCompact F) (hFbox : F ⊆ Icc a b) (hV : IsOpen V)
    (hmaximizers : ∀ x ∈ F, ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hK.toCompactCap x t = sweptNiche K (Real.pi / 2) x → t ∈ V) :
    ∀ᶠ n in atTop, ∀ x ∈ F, ∀ j : SourceIndex (dyadic (level n)),
      x ∈ innerSourceSet (U n) (dyadic (level n)) j →
        sourceQuarterAngle (fullAngle (dyadic (level n)) j) ∈ V := by
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ x ∈ F,
      ∃ j : SourceIndex (dyadic (level n)), x ∈ innerSourceSet (U n) (dyadic (level n)) j ∧
        sourceQuarterAngle (fullAngle (dyadic (level n)) j) ∉ V := by
    intro k
    by_contra hk
    apply hnot
    refine eventually_atTop.mpr ⟨k, ?_⟩
    intro n hn x hx j hsource
    by_contra hj
    exact hk ⟨n, hn, x, hx, j, hsource, hj⟩
  choose ns hns point hpoint source hsource houtside using hbad
  let angle : ℕ → ℝ := fun n => sourceQuarterAngle (fullAngle (dyadic (level (ns n))) (source n))
  have hpair : ∀ n, (point n, angle n) ∈ F ×ˢ Icc (0 : ℝ) (Real.pi / 2) := by
    intro n
    exact ⟨hpoint n, Ioo_subset_Icc_self (sourceQuarterAngle_mem _ _)⟩
  obtain ⟨z, hz, ms, hms, hpairlim⟩ := (hF.prod isCompact_Icc).tendsto_subseq hpair
  let seq : ℕ → ℕ := fun n => ns (ms n)
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hseq : Tendsto seq atTop atTop := hnsTop.comp hms.tendsto_atTop
  have hfinite := finiteBarrier_dyadic_tendsto (hHausdorff.comp hseq)
    (fun n => hU (seq n)) hK (hlevel.comp hseq) (fun n => hbox (seq n))
    (fun n => hFbox (hpoint (ms n))) hpairlim.fst
  have hclip := (hHausdorff.comp hseq).fullWallClip_tendsto
    (fun n => hU (seq n)) hK hpairlim.fst hpairlim.snd hz.2
  have hfiniteClip : Tendsto
      (fun n => fullWallClip (hU (seq n)).toCompactCap (point (ms n)) (angle (ms n)))
      atTop (𝓝 (sweptNiche K (Real.pi / 2) z.1)) := by
    apply hfinite.congr'
    exact Eventually.of_forall (fun n =>
      (innerSource_fullWallClip (hU (seq n)) _ (source (ms n)) (hsource (ms n))).symm)
  have heq : fullWallClip hK.toCompactCap z.1 z.2 = sweptNiche K (Real.pi / 2) z.1 :=
    tendsto_nhds_unique hclip hfiniteClip
  have hmem := hmaximizers z.1 hz.1 z.2 hz.2 heq
  have hevent : ∀ᶠ n in atTop, angle (ms n) ∈ V := hpairlim.snd.eventually (hV.mem_nhds hmem)
  obtain ⟨n, hn⟩ := hevent.exists
  exact houtside (ms n) hn

end AngularGrid

end AmbidextrousSofa
