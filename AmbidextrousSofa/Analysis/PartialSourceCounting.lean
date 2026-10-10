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
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon AngularGrid

theorem scaledAngle_eq_index_mul_mesh (α : TerminalAngle) (n : ℕ)
    (t : InteriorPoint (dyadic n)) :
    (scaleAngle α t.val : ℝ) = (fullGridIndex n (Sum.inl t) : ℝ) * mesh α n := by
  have ht := fullAngle_eq_index_mul_mesh n (Sum.inl t)
  change (t.val : ℝ) = (fullGridIndex n (Sum.inl t) : ℝ) * AngularGrid.mesh n at ht
  rw [scaleAngle_coe, ht, mesh]
  ring

open Classical in
theorem sum_mesh_scaled_interior_interval_le (α : TerminalAngle) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    (∑ t ∈ Finset.univ.filter (fun t : InteriorPoint (dyadic n) =>
      (scaleAngle α t.val : ℝ) ∈ Icc a b), mesh α n) ≤ b - a + mesh α n := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    count_integer_mesh_interval_le (fun t : InteriorPoint (dyadic n) => (scaleAngle α t.val : ℝ))
      (fun t => fullGridIndex n (Sum.inl t))
      (fun s t h => Sum.inl.inj (fullGridIndex_injective n h))
      (mesh_pos α n).le hab (scaledAngle_eq_index_mul_mesh α n)

open Classical in
theorem sum_mesh_scaled_sources_interval_le (α : TerminalAngle) (n : ℕ)
    {a b : ℝ} (hab : a ≤ b) :
    (∑ k : AngularGrid.SourceIndex (dyadic n),
      if fullAngle α (dyadic n) (scaledSource α (dyadic n) k) ∈ Icc a b
        then mesh α n else 0) ≤ 2 * (b - a + mesh α n) := by
  classical
  have hfirst : (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) ∈ Icc a b then mesh α n else 0) ≤
        b - a + mesh α n := by
    rw [← Finset.sum_filter]
    exact sum_mesh_scaled_interior_interval_le α n hab
  have hsecond : (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b then mesh α n else 0) ≤
        b - a + mesh α n := by
    have hmem (t : InteriorPoint (dyadic n)) :
        (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b ↔
          (scaleAngle α t.val : ℝ) ∈ Icc (a - Real.pi / 2) (b - Real.pi / 2) := by
      constructor <;> intro h <;> constructor <;> linarith only [h.1, h.2]
    simp_rw [hmem]
    rw [← Finset.sum_filter]
    have h := sum_mesh_scaled_interior_interval_le α n
      (show a - Real.pi / 2 ≤ b - Real.pi / 2 by linarith only [hab])
    convert h using 1 <;> ring
  rw [Fintype.sum_sum_type]
  change (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) ∈ Icc a b then mesh α n else 0) +
    (∑ t : InteriorPoint (dyadic n),
      if (scaleAngle α t.val : ℝ) + Real.pi / 2 ∈ Icc a b then mesh α n else 0) ≤ _
  linarith only [hfirst, hsecond]

open Classical in
theorem innerSourceMass_sum_interval_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    {R a b : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (hab : a ≤ b) (hterminal : (α : ℝ) ∉ Icc a b) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α (dyadic n) =>
      fullAngle α (dyadic n) j ∈ Icc a b), innerSourceMass U α hαL (dyadic n) j) ≤
        (8 * R + 24) * (b - a + mesh α n) := by
  classical
  let C := 4 * R + 12
  let δ := mesh α n
  let F := Finset.univ.filter (fun j : SourceIndex α (dyadic n) =>
    fullAngle α (dyadic n) j ∈ Icc a b)
  have hC : 0 ≤ C := by dsimp [C]; linarith only [hR]
  have hδ : 0 ≤ δ := (mesh_pos α n).le
  have hpoint (j : SourceIndex α (dyadic n)) (hj : j ∈ F) :
      innerSourceMass U α hαL (dyadic n) j ≤
        ∑ k : AngularGrid.SourceIndex (dyadic n),
          if scaledSource α (dyadic n) k = j then C * δ else 0 := by
    by_cases hscaled : ∃ k : AngularGrid.SourceIndex (dyadic n), j = scaledSource α (dyadic n) k
    · obtain ⟨k, rfl⟩ := hscaled
      apply (innerSourceMass_scaled_le hU α hαL hR hbox n k).trans
      have h := Finset.single_le_sum
        (fun s (_ : s ∈ (Finset.univ : Finset (AngularGrid.SourceIndex (dyadic n)))) =>
          show 0 ≤ (if scaledSource α (dyadic n) s = scaledSource α (dyadic n) k
            then C * δ else 0) from by split_ifs <;> positivity)
        (Finset.mem_univ k)
      simpa only [↓reduceIte, C, δ] using h
    · have hjterminal : j ≠ terminalIndex α hαL (dyadic n) := by
        intro heq
        apply hterminal
        have hmem := (Finset.mem_filter.mp hj).2
        simp only [heq, fullAngle, terminalIndex, AngularGrid.fullAngle] at hmem
        exact hmem
      rw [innerSourceMass_eq_zero_of_not_scaled U α hαL (dyadic n) j hjterminal hscaled]
      apply Finset.sum_nonneg
      intro k _
      split_ifs <;> positivity
  calc
    (∑ j ∈ F, innerSourceMass U α hαL (dyadic n) j) ≤
        ∑ j ∈ F, ∑ k : AngularGrid.SourceIndex (dyadic n),
          if scaledSource α (dyadic n) k = j then C * δ else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ k : AngularGrid.SourceIndex (dyadic n),
        if fullAngle α (dyadic n) (scaledSource α (dyadic n) k) ∈ Icc a b
          then C * δ else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_ite_eq]
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    _ = C * ∑ k : AngularGrid.SourceIndex (dyadic n),
        if fullAngle α (dyadic n) (scaledSource α (dyadic n) k) ∈ Icc a b
          then mesh α n else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp only [δ, mul_zero]
    _ ≤ C * (2 * (b - a + mesh α n)) :=
      mul_le_mul_of_nonneg_left (sum_mesh_scaled_sources_interval_le α n hab) hC
    _ = _ := by dsimp [C]; ring

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
  let F := Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
    fullAngle α (dyadic level) j ∈ Ioc a b)
  let G := Finset.univ.filter (fun j : SourceIndex α (dyadic level) =>
    fullAngle α (dyadic level) j ∈ Icc a b)
  have hFG : F ⊆ G := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ioc_subset_Icc_self (Finset.mem_filter.mp hj).2⟩
  have hinner : (∑ j ∈ F, innerSourceMass U α hαL (dyadic level) j) ≤
      (8 * R + 24) * (b - a + mesh α level) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hFG
      (fun j _ _ => innerSourceMass_nonneg hU.isCap α hαL (dyadic level) j)).trans
      (innerSourceMass_sum_interval_le hU.isCap α hαL hR hbox level hab hterminal)
  have hmid : (∑ j ∈ F, middleOuterMass U α (dyadic level) j) ≤
      ∑ j ∈ G, middleOuterMass U α (dyadic level) j :=
    Finset.sum_le_sum_of_subset_of_nonneg hFG
      (fun j _ _ => middleOuterMass_nonneg hU.isCap α (dyadic level) j)
  have herr : (∑ j ∈ F, selectionDefect target U α level coefficient j) ≤
      ∑ j, selectionDefect target U α level coefficient j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => selectionDefect_nonneg target U α level hc j)
  calc
    (upperCurvature U).real (Ioc a b) =
        ∑ j ∈ F, (upperCurvature U {fullAngle α (dyadic level) j}).toReal :=
      AngularGrid.upperCurvature_real_eq_sum_sources hU.isCap (outerGrid α (dyadic level))
        hU.polygon_eq (Ioc_subset_Icc_self.trans hupper)
        (fun ht => htop (Ioc_subset_Icc_self ht))
    _ ≤ ∑ j ∈ F, (innerSourceMass U α hαL (dyadic level) j +
        middleOuterMass U α (dyadic level) j + selectionDefect target U α level coefficient j) :=
      Finset.sum_le_sum (fun j _ => hU.curvature_atom_le_mass hc j)
    _ = (∑ j ∈ F, innerSourceMass U α hαL (dyadic level) j) +
        (∑ j ∈ F, middleOuterMass U α (dyadic level) j) +
        ∑ j ∈ F, selectionDefect target U α level coefficient j := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add (add_le_add hinner hmid) herr

end PartialGrid

end AmbidextrousSofa
