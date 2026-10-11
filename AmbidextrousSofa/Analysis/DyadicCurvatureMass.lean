module

public import AmbidextrousSofa.Analysis.DiscreteCurvature
public import AmbidextrousSofa.Analysis.MiddleFacetBounds
public import AmbidextrousSofa.Analysis.GridCounting

@[expose] public section

/-!
# Actual polygon curvature mass near the axes

Finite half-plane concentration is reindexed by the distinct actual
source normals. Combining the source atom bound with exact dyadic counting
gives a uniform linear bound on both punctured axis neighborhoods. The
only remaining addition is the total selected support penalty defect.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

open Classical in
theorem fullPolygonAngles_filter_eq_source_image (grid : Finset QuarterAngle)
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) :
    (fullPolygonAngles (fullAngle grid)).filter (fun t => t ∈ s) =
      (Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ s)).image
        (fullAngle grid) := by
  have hbox (i : Fin 4) : fullPolygonAngle (fullAngle grid) (Sum.inl i) ∉ s := fun hi => by
    have hib := hs hi
    fin_cases i <;> simp [fullPolygonAngle] at hi hib
    · exact htop hi
    · linarith [Real.pi_pos]
  ext t
  simp only [fullPolygonAngles, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨?_, fun ⟨j, hj, h⟩ => ⟨⟨Sum.inr j, h⟩, h ▸ hj⟩⟩
  rintro ⟨⟨i | j, rfl⟩, hi⟩
  exacts [(hbox i hi).elim, ⟨j, hi, rfl⟩]

open Classical in
theorem upperCurvature_real_eq_sum_sources {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) :
    (upperCurvature U).real s = ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex grid => fullAngle grid j ∈ s),
        (upperCurvature U {fullAngle grid j}).toReal := by
  have h := upperCurvature_eq_sum_fullPolygonAngles hU (fullAngle grid)
    (fun j => ⟨(fullAngle_mem grid j).1.le, (fullAngle_mem grid j).2.le⟩)
    (funext (normal_eq_unitNormal grid) ▸ hpoly) hs
  rw [fullPolygonAngles_filter_eq_source_image grid hs htop,
    Finset.sum_image (fun i _ j _ hij => fullAngle_injective grid hij)] at h
  rw [measureReal_def, h]
  exact ENNReal.toReal_sum (fun _ _ => isCompact_singleton.measure_ne_top)

open Classical in
theorem upperCurvature_real_le_mesh_sum {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) {q : SourceIndex grid → Prop} [DecidablePred q]
    (hq : ∀ j, fullAngle grid j ∈ s → q j) (error : SourceIndex grid → ℝ)
    (herror : ∀ j, 0 ≤ error j) {C δ ε : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hatom : ∀ j, q j → (upperCurvature U {fullAngle grid j}).toReal ≤ C * δ + error j)
    (hcount : (∑ _j ∈ Finset.univ.filter q, δ) ≤ ε) :
    (upperCurvature U).real s ≤ C * ε + ∑ j, error j := by
  rw [upperCurvature_real_eq_sum_sources hU grid hpoly hs htop]
  refine (Finset.sum_le_sum fun j hj => hatom j (hq j (Finset.mem_filter.mp hj).2)).trans
    ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.monotone_filter_right _ fun j _ => hq j)
      fun j _ _ => add_nonneg (mul_nonneg hC hδ) (herror j)).trans ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add (mul_le_mul_of_nonneg_left hcount hC)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => herror j)

theorem IsSelectedPolygon.curvature_right_axis_bound {target U : Set Plane}
    {a b coefficient R w ε : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (hε : 0 ≤ ε) (hεcut : ε ≤ axisCutoff w) :
    (upperCurvature U).real (Ioc 0 ε) ≤
      (4 * R + 10) * ε + ∑ j, selectionDefect target U level coefficient j := by
  have hεquarter : ε ≤ Real.pi / 4 := hεcut.trans (min_le_left _ _)
  exact upperCurvature_real_le_mesh_sum hU.isCap (dyadic level) hU.polygon_eq
    (fun t ht => ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩) (fun h => by linarith [h.2, Real.pi_pos])
    (fun j hj => hj.2) _ (selectionDefect_nonneg target U level hcoefficient) (by linarith)
    (mesh_pos level).le (fun j hj => hU.curvature_atom_coarse_near_axes hcoefficient hR hbox hw hW
      j (Or.inl (hj.trans hεcut))) (sum_mesh_right_sources_le level hε)

theorem IsSelectedPolygon.curvature_left_axis_bound {target U : Set Plane}
    {a b coefficient R w ε : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (hε : 0 ≤ ε) (hεcut : ε ≤ axisCutoff w) :
    (upperCurvature U).real (Ico (Real.pi - ε) Real.pi) ≤
      (4 * R + 10) * ε + ∑ j, selectionDefect target U level coefficient j := by
  have hεquarter : ε ≤ Real.pi / 4 := hεcut.trans (min_le_left _ _)
  exact upperCurvature_real_le_mesh_sum hU.isCap (dyadic level) hU.polygon_eq
    (fun t ht => ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩) (fun h => by linarith [h.1, Real.pi_pos])
    (q := fun j => Real.pi - fullAngle (dyadic level) j ≤ ε) (fun j hj => by linarith [hj.1]) _
    (selectionDefect_nonneg target U level hcoefficient) (by linarith) (mesh_pos level).le
    (fun j hj => hU.curvature_atom_coarse_near_axes hcoefficient hR hbox hw hW j
      (Or.inr (hj.trans hεcut))) (sum_mesh_left_sources_le level hε)

end AngularGrid

end AmbidextrousSofa
