module

public import AmbidextrousSofa.Analysis.PartialSourceMass
public import AmbidextrousSofa.Analysis.DyadicCurvatureMass

@[expose] public section

/-!
# Proper source counting and literal curvature interval bounds

Only the two rescaled visited families contribute nonterminal inner mass.
Each is an equally spaced family and has one mesh cell of interval
rounding error. The outer-only samples have zero inner mass; their actual
curvature remains bounded by the retained middle mass and support defect.
The curvature on any set of angles is summed once over its source atoms,
for any bound on the atoms beyond their middle and selection errors.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon AngularGrid

open Classical in
theorem sum_mesh_scaled_interior_interval_le (α : TerminalAngle) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    (∑ _t ∈ Finset.univ.filter (fun t : InteriorPoint (dyadic n) =>
      (scaleAngle α t.val : ℝ) ∈ Icc a b), mesh α n) ≤ b - a + mesh α n := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_interval_le (fun t : InteriorPoint (dyadic n) => (scaleAngle α t.val : ℝ))
      (fun t => fullGridIndex n (Sum.inl t))
      (fun _ _ h => Sum.inl.inj (fullGridIndex_injective n h))
      (mesh_pos α n).le hab fun t => by
        have ht := fullAngle_eq_index_mul_mesh n (Sum.inl t)
        change (t.val : ℝ) = (fullGridIndex n (Sum.inl t) : ℝ) * AngularGrid.mesh n at ht
        rw [scaleAngle_coe, ht, mesh]
        ring

open Classical in
theorem sum_mesh_scaled_sources_interval_le (α : TerminalAngle) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    (∑ k : AngularGrid.SourceIndex (dyadic n),
      if fullAngle α (dyadic n) (scaledSource α (dyadic n) k) ∈ Icc a b
        then mesh α n else 0) ≤ 2 * (b - a + mesh α n) := by
  classical
  rw [Fintype.sum_sum_type]
  change (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) ∈ Icc a b then mesh α n else 0) +
    (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b then mesh α n else 0) ≤ _
  have h1 := sum_mesh_scaled_interior_interval_le α n hab
  have h2 := sum_mesh_scaled_interior_interval_le α n (sub_le_sub_right hab (Real.pi / 2))
  simp only [Finset.sum_filter, ← Set.add_mem_Icc_iff_left, sub_sub_sub_cancel_right] at h1 h2
  linarith

open Classical in
theorem innerSourceMass_sum_interval_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    {R a b : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (hab : a ≤ b) (hterminal : (α : ℝ) ∉ Icc a b) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic n) =>
      fullAngle α (dyadic n) j ∈ Icc a b), innerSourceMass U α hαL (dyadic n) j) ≤
        (8 * R + 24) * (b - a + mesh α n) := by
  classical
  set F := Finset.univ.filter (fun j : SourceIndex α (dyadic n) =>
    fullAngle α (dyadic n) j ∈ Icc a b)
  have hδ := (mesh_pos α n).le
  have hw (j : SourceIndex α (dyadic n)) (k : AngularGrid.SourceIndex (dyadic n)) :
      0 ≤ if scaledSource α (dyadic n) k = j then (4 * R + 12) * mesh α n else 0 := by positivity
  have hpoint (j : SourceIndex α (dyadic n)) (hj : j ∈ F) :
      innerSourceMass U α hαL (dyadic n) j ≤
        ∑ k, if scaledSource α (dyadic n) k = j then (4 * R + 12) * mesh α n else 0 := by
    by_cases hscaled : ∃ k : AngularGrid.SourceIndex (dyadic n), j = scaledSource α (dyadic n) k
    · obtain ⟨k, rfl⟩ := hscaled
      refine (innerSourceMass_scaled_le hU α hαL hR hbox n k).trans ?_
      simpa only [↓reduceIte] using
        Finset.single_le_sum (fun q _ => hw (scaledSource α (dyadic n) k) q) (Finset.mem_univ k)
    · rw [innerSourceMass_eq_zero_of_not_scaled U α hαL (dyadic n) j
        (fun h => hterminal (by subst h; exact (Finset.mem_filter.mp hj).2)) hscaled]
      exact Finset.sum_nonneg fun k _ => hw j k
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [Finset.sum_comm, show (8 * R + 24) * (b - a + mesh α n) =
    (4 * R + 12) * (2 * (b - a + mesh α n)) by ring]
  simpa only [Finset.sum_ite_eq, F, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mul_sum, mul_ite, mul_zero] using mul_le_mul_of_nonneg_left
      (sum_mesh_scaled_sources_interval_le α n hab) (by positivity : (0 : ℝ) ≤ 4 * R + 12)

open Classical in
/-- The curvature on a set `s` of angles in `[a, b]`, when each source atom in `s` exceeds its
middle mass and selection error by at most `f j`; the terms are summed over `[a, b]`. -/
theorem IsSelectedPolygon.curvature_set_le_of_atoms {target U : Set Plane}
    {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}
    {boxLeft boxRight coefficient a b : ℝ} {level : ℕ} {s : Set ℝ}
    (hU : IsSelectedPolygon target α hαL boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hs : s ⊆ Ioo 0 Real.pi) (htop : Real.pi / 2 ∉ s) (hsab : s ⊆ Icc a b)
    {f : SourceIndex α (dyadic level) → ℝ} (hf : ∀ j, 0 ≤ f j)
    (hatom : ∀ j, fullAngle α (dyadic level) j ∈ s →
      (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤ f j +
        middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j) :
    (upperCurvature U).real s ≤
      (∑ j ∈ Finset.univ.filter (fun j => fullAngle α (dyadic level) j ∈ Icc a b), f j) +
      (∑ j ∈ Finset.univ.filter (fun j => fullAngle α (dyadic level) j ∈ Icc a b),
        middleOuterMass U α (dyadic level) j) +
      ∑ j, selectionDefect target U α level coefficient j := by
  classical
  rw [AngularGrid.upperCurvature_real_eq_sum_sources hU.isCap (outerGrid α (dyadic level))
    hU.polygon_eq hs htop]
  refine (Finset.sum_le_sum fun j hj => hatom j (Finset.mem_filter.mp hj).2).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hsub := Finset.monotone_filter_right (Finset.univ : Finset (SourceIndex α (dyadic level)))
    (p := fun j => fullAngle α (dyadic level) j ∈ s) fun _ _ h => hsab h
  gcongr ?_ + ?_ + ?_
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hf j
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
      middleOuterMass_nonneg hU.isCap α _ j
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ =>
      selectionDefect_nonneg target U α level hc j

open Classical in
theorem IsSelectedPolygon.curvature_Ioc_le {target U : Set Plane}
    {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}
    {boxLeft boxRight coefficient R a b : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL boxLeft boxRight level coefficient U)
    (hc : 0 ≤ coefficient) (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hab : a ≤ b) (hupper : Icc a b ⊆ Ioo 0 Real.pi)
    (htop : Real.pi / 2 ∉ Icc a b) (hterminal : (α : ℝ) ∉ Icc a b) :
    (upperCurvature U).real (Ioc a b) ≤
      (8 * R + 24) * (b - a + mesh α level) +
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
        fullAngle α (dyadic level) j ∈ Icc a b), middleOuterMass U α (dyadic level) j) +
      ∑ j, selectionDefect target U α level coefficient j := by
  classical
  refine (hU.curvature_set_le_of_atoms hc (Ioc_subset_Icc_self.trans hupper)
    (fun ht => htop (Ioc_subset_Icc_self ht)) Ioc_subset_Icc_self
    (innerSourceMass_nonneg hU.isCap α hαL _) fun j _ => hU.curvature_atom_le_mass hc j).trans ?_
  gcongr ?_ + _ + _
  exact innerSourceMass_sum_interval_le hU.isCap α hαL hR hbox level hab hterminal

end PartialGrid

end AmbidextrousSofa
