import AmbidextrousSofa.Analysis.NeighborCompanion

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

theorem mesh_pos (n : ℕ) : 0 < mesh n := by
  unfold mesh
  exact div_pos (by linarith [Real.pi_pos]) (by exact_mod_cast divisions_pos n)

theorem mesh_le_pi_div_four (n : ℕ) : mesh n ≤ Real.pi / 4 := by
  have hN : (2 : ℝ) ≤ divisions n := by exact_mod_cast divisions_ge_two n
  have hN0 : (0 : ℝ) < divisions n := by exact_mod_cast divisions_pos n
  have hmul := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ Real.pi / 4)
  unfold mesh
  rw [div_le_iff₀ hN0]
  nlinarith [hmul]

theorem mesh_lt_pi_div_two (n : ℕ) : mesh n < Real.pi / 2 :=
  (mesh_le_pi_div_four n).trans_lt (by linarith [Real.pi_pos])

theorem mesh_sin_pos (n : ℕ) : 0 < Real.sin (mesh n) :=
  Real.sin_pos_of_pos_of_lt_pi (mesh_pos n)
    ((mesh_lt_pi_div_two n).trans (by linarith [Real.pi_pos]))

theorem mesh_cos_pos (n : ℕ) : 0 < Real.cos (mesh n) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [mesh_pos n, Real.pi_pos], mesh_lt_pi_div_two n⟩

theorem mesh_half_cos_ne (n : ℕ) : Real.cos (mesh n / 2) ≠ 0 := by
  apply ne_of_gt
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> linarith [mesh_pos n, mesh_lt_pi_div_two n, Real.pi_pos]

theorem mesh_le_selectionRate (n : ℕ) : mesh n ≤ (Real.pi / 2) * selectionRate n := by
  have hN : (0 : ℝ) < divisions n := by exact_mod_cast divisions_pos n
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnN : (n : ℝ) + 1 ≤ divisions n := by
    have h : n + 1 ≤ divisions n := Nat.le_of_lt (show n + 1 < 2 ^ (n + 1) from Nat.lt_two_pow_self)
    exact_mod_cast h
  unfold mesh selectionRate
  rw [mul_one_div, div_le_div_iff₀ hN hn]
  exact mul_le_mul_of_nonneg_left hnN (by linarith [Real.pi_pos])

theorem mesh_tendsto : Tendsto mesh atTop (𝓝 0) := by
  apply squeeze_zero (fun n => (mesh_pos n).le) mesh_le_selectionRate
  simpa only [mul_zero] using selectionRate_tendsto.const_mul (Real.pi / 2)

theorem dyadic_neighbors (n : ℕ) (t : InteriorPoint (dyadic n)) :
    (∃ s ∈ dyadic n, (s : ℝ) = (t.val : ℝ) - mesh n) ∧
      (∃ s ∈ dyadic n, (s : ℝ) = (t.val : ℝ) + mesh n) := by
  obtain ⟨i, hi, hti⟩ := (mem_dyadic_iff n t.val).mp (interiorPoint_mem_grid _ t)
  have ht := interiorPoint_mem (dyadic n) t
  have hi0 : 0 < i := by
    by_contra h
    have hi' : i = 0 := by omega
    rw [hi'] at hti
    simp only [Nat.cast_zero, zero_mul, zero_div] at hti
    linarith [ht.1]
  have hiN : i < divisions n := by
    by_contra h
    have hi' : i = divisions n := by omega
    rw [hi'] at hti
    have hN : (divisions n : ℝ) ≠ 0 := by exact_mod_cast (divisions_pos n).ne'
    have heq : (t.val : ℝ) = Real.pi / 2 := by
      rw [hti]
      field_simp [hN]
    linarith [ht.2]
  constructor
  · let s : QuarterAngle := dyadicPoint n ⟨i - 1, by omega⟩
    refine ⟨s, (mem_dyadic_iff n s).mpr ⟨i - 1, by omega, rfl⟩, ?_⟩
    change ((i - 1 : ℕ) : ℝ) * (Real.pi / 2) / divisions n = (t.val : ℝ) - mesh n
    rw [hti, mesh, Nat.cast_sub (by omega : 1 ≤ i), Nat.cast_one]
    ring
  · let s : QuarterAngle := dyadicPoint n ⟨i + 1, by omega⟩
    refine ⟨s, (mem_dyadic_iff n s).mpr ⟨i + 1, by omega, rfl⟩, ?_⟩
    change ((i + 1 : ℕ) : ℝ) * (Real.pi / 2) / divisions n = (t.val : ℝ) + mesh n
    rw [hti, mesh, Nat.cast_add, Nat.cast_one]
    ring

def cornerSecant (U : Set Plane) (n : ℕ) : SourceIndex (dyadic n) → ℝ
  | Sum.inl t => firstCornerSecant U t.val (mesh n)
  | Sum.inr t => secondCornerSecant U t.val (mesh n)

theorem integral_innerDensity_dyadic_le {U : Set Plane} (hU : IsDownwardCap U)
    (n : ℕ) (j : SourceIndex (dyadic n)) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, innerDensity U (dyadic n) j x) ≤
      Real.tan (mesh n) * (|cornerSecant U n j| + Real.tan (mesh n / 2)) +
        max (2 * Real.tan (mesh n / 2) -
          (upperCurvature U {fullAngle (dyadic n) j}).toReal) 0 := by
  cases j with
  | inl t =>
    obtain ⟨hm, hp⟩ := dyadic_neighbors n t
    exact integral_first_source_le hU (dyadic n) t (mesh_cos_pos n) (mesh_sin_pos n)
      (mesh_half_cos_ne n) hab hm hp
  | inr t =>
    obtain ⟨hm, hp⟩ := dyadic_neighbors n t
    exact integral_second_source_le hU (dyadic n) t (mesh_cos_pos n) (mesh_sin_pos n)
      (mesh_half_cos_ne n) hab hm hp

def middleOuterMass (U : Set Plane) (grid : Finset QuarterAngle) (j : SourceIndex grid) : ℝ :=
  ∫ x in (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)..
    (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4), outerDensity U grid j x

theorem middleOuterMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) : 0 ≤ middleOuterMass U grid j := by
  apply intervalIntegral.integral_nonneg_of_forall
  · linarith [horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact]
  · exact outerDensity_nonneg U grid j

theorem IsSelectedPolygon.curvature_atom_self_bound {target U : Set Plane}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target a b level coefficient U) (hcoefficient : 0 ≤ coefficient)
    (j : SourceIndex (dyadic level)) :
    (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      Real.tan (mesh level) * (|cornerSecant U level j| + Real.tan (mesh level / 2)) +
        max (2 * Real.tan (mesh level / 2) -
          (upperCurvature U {fullAngle (dyadic level) j}).toReal) 0 +
        middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j := by
  have hsource := integral_innerDensity_dyadic_le hU.isCap level j
    (by linarith [horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact] :
      horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 ≤
        horizontalRight U - (horizontalRight U - horizontalLeft U) / 4)
  have hatom := hU.curvature_atom_le hcoefficient j
  change (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
    _ + middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j at hatom
  linarith

theorem solve_curvature_self_bound {x A B e : ℝ} (he : 0 ≤ e)
    (h : x ≤ A + max (B - x) 0 + e) : x ≤ max A ((A + B) / 2) + e := by
  by_cases hx : B ≤ x
  · rw [max_eq_right (by linarith : B - x ≤ 0), add_zero] at h
    exact h.trans (add_le_add_right (le_max_left _ _) e)
  · have hx' : 0 ≤ B - x := by linarith [le_of_not_ge hx]
    rw [max_eq_left hx'] at h
    have hle : x ≤ (A + B) / 2 + e := by linarith
    exact hle.trans (add_le_add_right (le_max_right _ _) e)

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
  have h := hU.curvature_atom_self_bound hcoefficient j
  have he := add_nonneg (middleOuterMass_nonneg hU.isCap (dyadic level) j)
    (selectionDefect_nonneg target U level hcoefficient j)
  have hsolve : (upperCurvature U {fullAngle (dyadic level) j}).toReal ≤
      max (Real.tan (mesh level) * (|cornerSecant U level j| + Real.tan (mesh level / 2)))
        ((Real.tan (mesh level) * (|cornerSecant U level j| + Real.tan (mesh level / 2)) +
          2 * Real.tan (mesh level / 2)) / 2) +
        (middleOuterMass U (dyadic level) j + selectionDefect target U level coefficient j) :=
    solve_curvature_self_bound he (by simpa only [add_assoc] using h)
  simpa only [finiteCurvatureDensity, add_assoc] using hsolve

end AngularGrid

end AmbidextrousSofa
