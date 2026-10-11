module

public import AmbidextrousSofa.Analysis.FiniteGraphFlux
public import AmbidextrousSofa.Analysis.NegativeCornerCurvature

@[expose] public section

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

namespace AngularGrid

open FinitePolygon

theorem sourceQuarterAngle_mem (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    sourceQuarterAngle (fullAngle grid j) ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [sourceQuarterAngle_fullAngle]
  rcases j with t | t <;> exact interiorPoint_mem grid t

theorem innerSource_cornerWall (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    cornerWall U (sourceQuarterAngle (fullAngle grid j)) x =
      finiteBarrier U (normal grid) (pairList grid) none x := by
  rw [sourceQuarterAngle_fullAngle, innerSource_height U grid j hx, cornerWall]
  rcases j with t | t
  · exact min_eq_left ((first_source_le_companion U grid t hx).trans_eq
      (supportWall_companionNormal U t x))
  · rw [← supportWall_companionNormal]
    exact min_eq_right (second_source_le_first U grid t hx)

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
  by_contra hnot
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.1 hnot)
  push Not at hbad
  choose point hpoint hnonpos using hbad
  obtain ⟨x, hx, ms, hms, hlim⟩ := hF.tendsto_subseq hpoint
  have hseq := hφ.tendsto_atTop.comp hms.tendsto_atTop
  have hfinite := finiteBarrier_dyadic_tendsto (hHausdorff.comp hseq) (fun n => hU _) hK
    (hlevel.comp hseq) (fun n => hbox _) (fun n => hFbox (hpoint _)) hlim
  exact (hpositive x hx).not_ge (le_of_tendsto' hfinite fun n => hnonpos _)

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
  by_contra hnot
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop (not_eventually.1 hnot)
  push Not at hbad
  choose point hpoint source hsource houtside using hbad
  obtain ⟨z, hz, ms, hms, hlim⟩ := (hF.prod isCompact_Icc).tendsto_subseq (x := fun n =>
      (point n, sourceQuarterAngle (fullAngle (dyadic (level (φ n))) (source n))))
    fun n => ⟨hpoint n, Ioo_subset_Icc_self (sourceQuarterAngle_mem _ _)⟩
  have hseq := hφ.tendsto_atTop.comp hms.tendsto_atTop
  have hfinite := finiteBarrier_dyadic_tendsto (hHausdorff.comp hseq) (fun n => hU _) hK
    (hlevel.comp hseq) (fun n => hbox _) (fun n => hFbox (hpoint _)) hlim.fst_nhds
  -- The clipped walls at the sources converge, and they equal the finite barriers.
  have hclip := (continuousAt_fullWallClip (z := ((hK.toCompactCap, z.1), z.2)) hz.2).tendsto.comp
    (((IsDownwardCap.tendsto_toCompactCap (fun n => hU _) hK (hHausdorff.comp hseq)).prodMk_nhds
      hlim.fst_nhds).prodMk_nhds hlim.snd_nhds)
  have heq := tendsto_nhds_unique hclip <| hfinite.congr fun n => by
    simp only [Function.comp_apply, fullWallClip, IsDownwardCap.toCompactCap_carrier,
      innerSource_cornerWall _ _ _ (hsource _)]
    exact (max_eq_left (finiteBarrier_nonneg _ _ _ _ _)).symm
  obtain ⟨n, hn⟩ := (hlim.snd_nhds.eventually
    (hV.mem_nhds (hmaximizers z.1 hz.1 z.2 hz.2 heq))).exists
  exact houtside _ hn

end AngularGrid

end AmbidextrousSofa
