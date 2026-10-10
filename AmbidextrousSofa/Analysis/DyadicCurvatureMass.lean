import AmbidextrousSofa.Analysis.DiscreteCurvature
import AmbidextrousSofa.Analysis.MiddleFacetBounds
import AmbidextrousSofa.Analysis.GridCounting

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

theorem fullPolygonAngles_filter_eq_source_image (grid : Finset QuarterAngle)
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) :
    (fullPolygonAngles (fullAngle grid)).filter (fun t => t ∈ s) =
      (Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ s)).image
        (fullAngle grid) := by
  classical
  have hbox : ∀ i : Fin 4, fullPolygonAngle (fullAngle grid) (Sum.inl i) ∉ s := by
    intro i hi
    have hib := hs hi
    fin_cases i
    · have h : (0 : ℝ) < 0 := by simpa only [fullPolygonAngle, Matrix.cons_val_zero] using hib.1
      exact lt_irrefl _ h
    · apply htop
      simpa [fullPolygonAngle] using hi
    · have h : Real.pi < Real.pi := by simpa [fullPolygonAngle] using hib.2
      exact lt_irrefl _ h
    · have h : 3 * Real.pi / 2 < Real.pi := by simpa [fullPolygonAngle] using hib.2
      linarith [Real.pi_pos]
  ext t
  simp only [fullPolygonAngles, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, rfl⟩, hi⟩
    cases i with
    | inl i => exact False.elim (hbox i hi)
    | inr j => exact ⟨j, hi, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨Sum.inr j, rfl⟩, hj⟩

theorem upperCurvature_eq_sum_sources {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) :
    upperCurvature U s = ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex grid => fullAngle grid j ∈ s), upperCurvature U {fullAngle grid j} := by
  classical
  have hn : normal grid = fun j => unitNormal (fullAngle grid j) := funext (normal_eq_unitNormal grid)
  have h := upperCurvature_eq_sum_fullPolygonAngles hU (fullAngle grid)
    (fun j => ⟨(fullAngle_mem grid j).1.le, (fullAngle_mem grid j).2.le⟩)
    (by simpa only [← hn] using hpoly) hs
  rw [fullPolygonAngles_filter_eq_source_image grid hs htop,
    Finset.sum_image (fun i _ j _ hij => fullAngle_injective grid hij)] at h
  exact h

theorem upperCurvature_real_eq_sum_sources {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) :
    (upperCurvature U).real s = ∑ j ∈ Finset.univ.filter
      (fun j : SourceIndex grid => fullAngle grid j ∈ s),
        (upperCurvature U {fullAngle grid j}).toReal := by
  classical
  change (upperCurvature U s).toReal = _
  rw [upperCurvature_eq_sum_sources hU grid hpoly hs htop]
  exact ENNReal.toReal_sum (fun _ _ => isCompact_singleton.measure_ne_top)

theorem upperCurvature_real_le_mesh_sum {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (hpoly : U = circumscription U (normal grid))
    {s : Set ℝ} [DecidablePred (fun t => t ∈ s)] (hs : s ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ s) (error : SourceIndex grid → ℝ)
    (herror : ∀ j, 0 ≤ error j) {C δ ε : ℝ} (hC : 0 ≤ C)
    (hatom : ∀ j, fullAngle grid j ∈ s →
      (upperCurvature U {fullAngle grid j}).toReal ≤ C * δ + error j)
    (hcount : (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ s), δ) ≤ ε) :
    (upperCurvature U).real s ≤ C * ε + ∑ j, error j := by
  classical
  let F := Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ s)
  have herr : (∑ j ∈ F, error j) ≤ ∑ j, error j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro j _ _
    exact herror j
  calc
    (upperCurvature U).real s = ∑ j ∈ F, (upperCurvature U {fullAngle grid j}).toReal :=
      upperCurvature_real_eq_sum_sources hU grid hpoly hs htop
    _ ≤ ∑ j ∈ F, (C * δ + error j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hatom j (Finset.mem_filter.mp hj).2
    _ = C * (∑ j ∈ F, δ) + ∑ j ∈ F, error j := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ C * ε + ∑ j, error j :=
      add_le_add (mul_le_mul_of_nonneg_left hcount hC) herr

theorem IsSelectedPolygon.curvature_right_axis_bound {target U : Set Plane}
    {a b coefficient R w ε : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (hε : 0 ≤ ε) (hεcut : ε ≤ axisCutoff w) :
    (upperCurvature U).real (Ioc 0 ε) ≤
      (4 * R + 10) * ε + ∑ j, selectionDefect target U level coefficient j := by
  classical
  have hεquarter : ε ≤ Real.pi / 4 := hεcut.trans (min_le_left _ _)
  have hs : Ioc (0 : ℝ) ε ⊆ Ioo 0 Real.pi := by
    intro t ht
    exact ⟨ht.1, by linarith [ht.2, Real.pi_pos]⟩
  have htop : Real.pi / 2 ∉ Ioc (0 : ℝ) ε := by
    intro h
    linarith [h.2, Real.pi_pos]
  have hfilter : Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
      fullAngle (dyadic level) j ∈ Ioc (0 : ℝ) ε) =
        Finset.univ.filter (fun j : SourceIndex (dyadic level) => fullAngle (dyadic level) j ≤ ε) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Ioc,
      (fullAngle_mem (dyadic level) j).1, true_and]
  apply upperCurvature_real_le_mesh_sum hU.isCap (dyadic level) hU.polygon_eq hs htop
    (selectionDefect target U level coefficient)
    (selectionDefect_nonneg target U level hcoefficient) (by linarith)
  · intro j hj
    exact hU.curvature_atom_coarse_near_axes hcoefficient hR hbox hw hW j
      (Or.inl (hj.2.trans hεcut))
  · rw [hfilter]
    exact sum_mesh_right_sources_le level hε

theorem IsSelectedPolygon.curvature_left_axis_bound {target U : Set Plane}
    {a b coefficient R w ε : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hw : 0 < w) (hW : w ≤ capWidth U) (hε : 0 ≤ ε) (hεcut : ε ≤ axisCutoff w) :
    (upperCurvature U).real (Ico (Real.pi - ε) Real.pi) ≤
      (4 * R + 10) * ε + ∑ j, selectionDefect target U level coefficient j := by
  classical
  have hεquarter : ε ≤ Real.pi / 4 := hεcut.trans (min_le_left _ _)
  have hs : Ico (Real.pi - ε) Real.pi ⊆ Ioo 0 Real.pi := by
    intro t ht
    exact ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  have htop : Real.pi / 2 ∉ Ico (Real.pi - ε) Real.pi := by
    intro h
    linarith [h.1, Real.pi_pos]
  have hfilter : Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
      fullAngle (dyadic level) j ∈ Ico (Real.pi - ε) Real.pi) =
        Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
          Real.pi - fullAngle (dyadic level) j ≤ ε) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Ico,
      (fullAngle_mem (dyadic level) j).2, and_true]
    constructor <;> intro h <;> linarith
  apply upperCurvature_real_le_mesh_sum hU.isCap (dyadic level) hU.polygon_eq hs htop
    (selectionDefect target U level coefficient)
    (selectionDefect_nonneg target U level hcoefficient) (by linarith)
  · intro j hj
    exact hU.curvature_atom_coarse_near_axes hcoefficient hR hbox hw hW j
      (Or.inr (by linarith [hj.1]))
  · rw [hfilter]
    exact sum_mesh_left_sources_le level hε

end AngularGrid

end AmbidextrousSofa
