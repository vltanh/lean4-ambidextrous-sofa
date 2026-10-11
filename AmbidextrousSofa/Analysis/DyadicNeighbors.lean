module

public import AmbidextrousSofa.Analysis.NeighborCompanion

@[expose] public section

/-!
# Concrete dyadic curvature inequalities

Every open dyadic point has both closed-grid neighbors. The geometric
source estimates therefore apply to the actual selected polygons, with a
mesh tending to zero. Solving the scalar self-bound yields the finite
precursor of the refined wing-curvature density.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

def mesh (n : ℕ) : ℝ := (Real.pi / 2) / divisions n

theorem mesh_pos (n : ℕ) : 0 < mesh n :=
  div_pos Real.pi_div_two_pos (Nat.cast_pos.mpr (divisions_pos n))

theorem mesh_le_pi_div_four (n : ℕ) : mesh n ≤ Real.pi / 4 := by
  have hN : (2 : ℝ) ≤ divisions n := by exact_mod_cast divisions_ge_two n
  rw [mesh, div_le_iff₀ (by linarith)]
  nlinarith [Real.pi_pos]

theorem mesh_sin_pos (n : ℕ) : 0 < Real.sin (mesh n) :=
  Real.sin_pos_of_pos_of_lt_pi (mesh_pos n) (by linarith [mesh_le_pi_div_four n, Real.pi_pos])

theorem mesh_cos_pos (n : ℕ) : 0 < Real.cos (mesh n) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [mesh_pos n, Real.pi_pos],
    by linarith [mesh_le_pi_div_four n, Real.pi_pos]⟩

theorem mesh_half_cos_ne (n : ℕ) : Real.cos (mesh n / 2) ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo ⟨by linarith [mesh_pos n, Real.pi_pos],
    by linarith [mesh_le_pi_div_four n, Real.pi_pos]⟩).ne'

theorem mesh_tendsto : Tendsto mesh atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp
    ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp (tendsto_add_atTop_nat 1)))

theorem dyadic_neighbors (n : ℕ) (t : InteriorPoint (dyadic n)) :
    (∃ s ∈ dyadic n, (s : ℝ) = (t.val : ℝ) - mesh n) ∧
      (∃ s ∈ dyadic n, (s : ℝ) = (t.val : ℝ) + mesh n) := by
  obtain ⟨i, hi, hti⟩ := (mem_dyadic_iff n t.val).mp (interiorPoint_mem_grid _ t)
  obtain ⟨ht0, ht1⟩ := interiorPoint_mem (dyadic n) t
  rcases i with _ | k
  · simp at hti; linarith
  have hk : k + 1 < divisions n := lt_of_le_of_ne hi fun h => by
    rw [h, mul_div_cancel_left₀ _ (Nat.cast_pos.mpr (divisions_pos n)).ne'] at hti; linarith
  refine ⟨⟨dyadicPoint n ⟨k, by omega⟩, (mem_dyadic_iff n _).mpr ⟨k, by omega, rfl⟩, ?_⟩,
    ⟨dyadicPoint n ⟨k + 2, by omega⟩, (mem_dyadic_iff n _).mpr ⟨k + 2, by omega, rfl⟩, ?_⟩⟩ <;>
  · simp only [dyadicPoint, hti, mesh]; push_cast; ring

def cornerSecant (U : Set Plane) (n : ℕ) : SourceIndex (dyadic n) → ℝ
  | Sum.inl t => firstCornerSecant U t.val (mesh n)
  | Sum.inr t => secondCornerSecant U t.val (mesh n)

theorem integral_innerDensity_dyadic_le {U : Set Plane} (hU : IsDownwardCap U)
    (n : ℕ) (j : SourceIndex (dyadic n)) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, innerDensity U (dyadic n) j x) ≤
      Real.tan (mesh n) * (|cornerSecant U n j| + Real.tan (mesh n / 2)) +
        max (2 * Real.tan (mesh n / 2) -
          (upperCurvature U {fullAngle (dyadic n) j}).toReal) 0 := by
  rcases j with t | t <;> obtain ⟨hm, hp⟩ := dyadic_neighbors n t
  exacts [integral_first_source_le hU _ t (mesh_cos_pos n) (mesh_sin_pos n) (mesh_half_cos_ne n)
    hab hm hp, integral_second_source_le hU _ t (mesh_cos_pos n) (mesh_sin_pos n)
    (mesh_half_cos_ne n) hab hm hp]

def middleOuterMass (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ :=
  ∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4), outerDensity U grid j x

theorem middleOuterMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) : 0 ≤ middleOuterMass U grid j :=
  intervalIntegral.integral_nonneg_of_forall
    (by linarith [horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact])
    (outerDensity_nonneg U grid j)

theorem solve_curvature_self_bound {x A B e : ℝ} (he : 0 ≤ e)
    (h : x ≤ A + max (B - x) 0 + e) : x ≤ max A ((A + B) / 2) + e := by
  have := le_max_left A ((A + B) / 2); have := le_max_right A ((A + B) / 2)
  rcases max_cases (B - x) 0 with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] at h <;> linarith

def finiteCurvatureDensity (q δ : ℝ) : ℝ :=
  max (Real.tan δ * (|q| + Real.tan (δ / 2)))
    ((Real.tan δ * (|q| + Real.tan (δ / 2)) + 2 * Real.tan (δ / 2)) / 2)

/-- The actual finite refined bound, including the middle face and all
penalty errors. Both additions are retained until their limits are proved. -/
theorem IsSelectedPolygon.curvature_atom_refined {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      finiteCurvatureDensity (cornerSecant U level j) (mesh level) +
        middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j := by
  have hsource := integral_innerDensity_dyadic_le hU.isCap level j
    (by linarith [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact] :
      horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)
  have hatom := hU.curvature_atom_le hcoefficient j
  rw [add_assoc]
  exact solve_curvature_self_bound (add_nonneg (middleOuterMass_nonneg hU.isCap _ j)
    (selectionDefect_nonneg target U level hcoefficient j)) (by unfold middleOuterMass; linarith)

end AngularGrid

end AmbidextrousSofa
