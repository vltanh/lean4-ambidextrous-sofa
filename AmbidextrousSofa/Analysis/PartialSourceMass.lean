module

public import AmbidextrousSofa.Analysis.PartialNeighborLength
public import AmbidextrousSofa.Analysis.BoxedSecants
public import AmbidextrousSofa.Analysis.GridCounting

@[expose] public section

/-!
# Vanishing-mesh bounds for actual proper-history source mass

The middle window of a cap is ordered, and the rescaled dyadic mesh is
positive and tends to zero. Each sampled visited source has both
endpoint-inclusive neighbors. Every other nonterminal source has zero
inner mass. This gives a uniform coarse source bound while keeping the
genuine terminal source separate.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The middle window of a cap is ordered. -/
theorem IsDownwardCap.quarter_le {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalLeft U + capWidth U / 4 ≤ horizontalRight U - capWidth U / 4 := by
  linarith [hU.capWidth_nonneg, show capWidth U = horizontalRight U - horizontalLeft U from rfl]

namespace PartialGrid

open FinitePolygon AngularGrid

def mesh (α : TerminalAngle) (n : ℕ) : ℝ :=
  ((α : ℝ) / (Real.pi / 2)) * AngularGrid.mesh n

theorem scaleAngle_coe (α : TerminalAngle) (t : QuarterAngle) :
    (scaleAngle α t : ℝ) = ((α : ℝ) / (Real.pi / 2)) * (t : ℝ) :=
  (mul_comm_div _ _ _).symm

theorem mesh_pos (α : TerminalAngle) (n : ℕ) : 0 < mesh α n :=
  mul_pos (div_pos (TerminalAngle.pos α) (by linarith [Real.pi_pos])) (AngularGrid.mesh_pos n)

theorem mesh_le_pi_div_four (α : TerminalAngle) (n : ℕ) : mesh α n ≤ Real.pi / 4 :=
  (mul_le_of_le_one_left (AngularGrid.mesh_pos n).le
    ((div_le_one (by positivity)).mpr α.property.2)).trans (AngularGrid.mesh_le_pi_div_four n)

theorem mesh_sin_pos (α : TerminalAngle) (n : ℕ) : 0 < Real.sin (mesh α n) :=
  Real.sin_pos_of_pos_of_lt_pi (mesh_pos α n)
    (by linarith [mesh_le_pi_div_four α n, Real.pi_pos])

theorem mesh_cos_pos (α : TerminalAngle) (n : ℕ) : 0 < Real.cos (mesh α n) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [mesh_pos α n, Real.pi_pos],
    by linarith [mesh_le_pi_div_four α n, Real.pi_pos]⟩

theorem mesh_half_cos_ne (α : TerminalAngle) (n : ℕ) : Real.cos (mesh α n / 2) ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo ⟨by linarith [mesh_pos α n, Real.pi_pos],
    by linarith [mesh_le_pi_div_four α n, Real.pi_pos]⟩).ne'

theorem mesh_tendsto (α : TerminalAngle) : Tendsto (mesh α) atTop (𝓝 0) :=
  mul_zero ((α : ℝ) / (Real.pi / 2)) ▸ AngularGrid.mesh_tendsto.const_mul _

theorem dyadic_neighbors (α : TerminalAngle) (n : ℕ) (t : InteriorPoint (dyadic n)) :
    (∃ s ∈ dyadic n, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) - mesh α n) ∧
      (∃ s ∈ dyadic n, (scaleAngle α s : ℝ) = (scaleAngle α t.val : ℝ) + mesh α n) := by
  obtain ⟨⟨s, hs, hseq⟩, ⟨u, hu, hueq⟩⟩ := AngularGrid.dyadic_neighbors n t
  exact ⟨⟨s, hs, by rw [scaleAngle_coe, scaleAngle_coe, hseq, mesh]; ring⟩,
    ⟨u, hu, by rw [scaleAngle_coe, scaleAngle_coe, hueq, mesh]; ring⟩⟩

def cornerSecant (U : Set Plane) (α : TerminalAngle) (n : ℕ) :
    AngularGrid.SourceIndex (dyadic n) → ℝ
  | Sum.inl t => firstCornerSecant U (scaleAngle α t.val) (mesh α n)
  | Sum.inr t => secondCornerSecant U (scaleAngle α t.val) (mesh α n)

theorem integral_scaled_innerDensity_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (n : ℕ) (j : AngularGrid.SourceIndex (dyadic n)) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, innerDensity U α hαL (dyadic n) (scaledSource α (dyadic n) j) x) ≤
      Real.tan (mesh α n) * (|cornerSecant U α n j| + Real.tan (mesh α n / 2)) +
        max (2 * Real.tan (mesh α n / 2) -
          (upperCurvature U {fullAngle α (dyadic n) (scaledSource α (dyadic n) j)}).toReal) 0 := by
  rcases j with t | t <;> obtain ⟨hm, hp⟩ := dyadic_neighbors α n t
  · exact integral_first_source_le hU α hαL (dyadic n) t (mesh_cos_pos α n)
      (mesh_sin_pos α n) (mesh_half_cos_ne α n) hab hm hp
  · exact integral_second_source_le hU α hαL (dyadic n) t (mesh_cos_pos α n)
      (mesh_sin_pos α n) (mesh_half_cos_ne α n) hab hm hp

theorem abs_cornerSecant_le_box {U : Set Plane} (hU : IsDownwardCap U)
    {R : ℝ} (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (α : TerminalAngle) (n : ℕ) (j : AngularGrid.SourceIndex (dyadic n)) :
    |cornerSecant U α n j| ≤ 2 * R + 3 := by
  rcases j with t | t
  · exact AngularGrid.abs_firstCornerSecant_le_box hU hbox _ _ (mesh_cos_pos α n).le
      (mesh_sin_pos α n).ne'
  · exact AngularGrid.abs_secondCornerSecant_le_box hU hbox _ _ (mesh_cos_pos α n).le
      (mesh_sin_pos α n).ne'

theorem raw_inner_bound_le_coarse {q atom R δ : ℝ} (hR : 0 ≤ R)
    (hq : |q| ≤ 2 * R + 3) (hatom : 0 ≤ atom)
    (hδ : δ ∈ Icc (0 : ℝ) (Real.pi / 4)) :
    Real.tan δ * (|q| + Real.tan (δ / 2)) +
      max (2 * Real.tan (δ / 2) - atom) 0 ≤ (4 * R + 12) * δ := by
  have hmain := (le_max_left _ _).trans (finiteCurvatureDensity_le_coarse (by linarith) hq hδ)
  have htan := tan_le_two_mul (δ := δ / 2) ⟨by linarith [hδ.1], by linarith [hδ.2, Real.pi_pos]⟩
  linarith [max_le (by linarith : 2 * Real.tan (δ / 2) - atom ≤ 2 * δ)
    (by linarith [hδ.1] : (0 : ℝ) ≤ 2 * δ)]

def innerSourceMass (U : Set Plane) (α : TerminalAngle)
    (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) : ℝ :=
  ∫ x in (horizontalLeft U + capWidth U / 4)..(horizontalRight U - capWidth U / 4),
    innerDensity U α hαL grid j x

def middleOuterMass (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) : ℝ := AngularGrid.middleOuterMass U (outerGrid α grid) j

theorem innerSourceMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    0 ≤ innerSourceMass U α hαL grid j :=
  intervalIntegral.integral_nonneg_of_forall hU.quarter_le (innerDensity_nonneg U α hαL grid j)

theorem middleOuterMass_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    0 ≤ middleOuterMass U α grid j :=
  AngularGrid.middleOuterMass_nonneg hU (outerGrid α grid) j

theorem innerSourceMass_scaled_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    {R : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (n : ℕ) (j : AngularGrid.SourceIndex (dyadic n)) :
    innerSourceMass U α hαL (dyadic n) (scaledSource α (dyadic n) j) ≤
      (4 * R + 12) * mesh α n :=
  (integral_scaled_innerDensity_le hU α hαL n j hU.quarter_le).trans
    (raw_inner_bound_le_coarse hR (abs_cornerSecant_le_box hU hbox α n j)
      ENNReal.toReal_nonneg ⟨(mesh_pos α n).le, mesh_le_pi_div_four α n⟩)

theorem innerSourceMass_eq_zero_of_not_scaled (U : Set Plane)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) (hterminal : j ≠ terminalIndex α hαL grid)
    (hscaled : ¬ ∃ k : AngularGrid.SourceIndex grid, j = scaledSource α grid k) :
    innerSourceMass U α hαL grid j = 0 := by
  classical
  have hdensity : innerDensity U α hαL grid j = fun _ => 0 := funext fun x => by
    rw [innerDensity, outwardVelocity_eq_single, WallExpr.sourceDensity_single]
    exact indicator_of_notMem (fun hx => hscaled (innerSource_origin U α hαL grid hterminal hx)) _
  rw [innerSourceMass, hdensity, intervalIntegral.integral_zero]

theorem IsSelectedPolygon.curvature_atom_le_mass {target U : Set Plane}
    {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}
    {a b coefficient : ℝ} {level : ℕ}
    (hU : IsSelectedPolygon target α hαL a b level coefficient U) (hc : 0 ≤ coefficient)
    (j : SourceIndex α (dyadic level)) :
    (upperCurvature U {fullAngle α (dyadic level) j}).toReal ≤
      innerSourceMass U α hαL (dyadic level) j + middleOuterMass U α (dyadic level) j +
        selectionDefect target U α level coefficient j :=
  hU.curvature_atom_le hc j

end PartialGrid

end AmbidextrousSofa
