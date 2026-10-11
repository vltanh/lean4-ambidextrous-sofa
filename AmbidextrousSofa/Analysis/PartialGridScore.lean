module

public import AmbidextrousSofa.Analysis.PartialGridPolygon

@[expose] public section

/-!
# Uniform finite recovery of the proper-angle spatial score

The finite history keeps the whole terminal first wall. Its only error is
the integral of the omitted historical barrier over the actual moving
middle window. The rescaled angular approximation controls this error
uniformly on the complete boxed cap domain.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open FinitePolygon

def score (U : Set Plane) (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) : ℝ :=
  finiteSpatialScore U (normal α grid) (pairList α grid)
    (some (terminalIndex α hαL grid))

theorem score_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) :
    score U α hαL grid =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), barrier U α grid x := by
  simp only [score, finiteSpatialScore_eq_integrals hU, finiteBarrier_eq_barrier]

theorem integrableOn_barriers {U : Set Plane} (hU : IsDownwardCap U) (α : TerminalAngle)
    (grid : Finset AngularGrid.QuarterAngle) :
    IntegrableOn (partialBarrier U α) (middleHalfInterval (horizontalLeft U) (horizontalRight U)) ∧
      IntegrableOn (barrier U α grid) (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
  ⟨integrableOn_partialBarrier_Icc hU.isCompact (TerminalAngle.pos α) α.property.2 _ _,
    (show Continuous (barrier U α grid) from ((continuous_barrier grid).comp
      (continuous_const.prodMk continuous_id) (f := fun x => ((hU.toCompactCap, α), x)) :)
      ).integrableOn_Icc⟩

theorem score_sub_capScore_eq {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) :
    score U α hαL grid - capScore U α =
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        partialBarrier U α x - barrier U α grid x := by
  obtain ⟨hN, hG⟩ := integrableOn_barriers hU α grid
  rw [score_eq_integrals hU α hαL grid, capScore_eq_integrals, integral_sub hN hG]
  ring

theorem capScore_le_score {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) :
    capScore U α ≤ score U α hαL grid :=
  sub_nonneg.mp (score_sub_capScore_eq hU α hαL grid ▸ integral_nonneg fun x =>
    sub_nonneg.mpr (barrier_le_partialBarrier hU.toCompactCap α grid x))

theorem score_sub_capScore_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) {ε : ℝ}
    (herror : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      partialBarrier U α x - barrier U α grid x ≤ ε) :
    score U α hαL grid - capScore U α ≤ capWidth U / 2 * ε := by
  obtain ⟨hN, hG⟩ := integrableOn_barriers hU α grid
  rw [score_sub_capScore_eq hU α hαL grid]
  refine (setIntegral_mono_on (hN.sub hG) continuous_const.integrableOn_Icc
    (measurableSet_middleHalfInterval _ _) herror).trans_eq ?_
  rw [setIntegral_const, smul_eq_mul,
    volumeReal_middleHalfInterval (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]
  rfl

theorem eventually_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) :
    ∀ᶠ n in atTop, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U α hαL (AngularGrid.dyadic n) - capScore U α ∧
          score U α hαL (AngularGrid.dyadic n) - capScore U α ≤ ε := by
  have hden : 0 < b - a + 1 := by linarith
  have hδ : 0 < ε / (b - a + 1) := div_pos hε hden
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_dyadic_box
    (isCompact_Icc.prod isCompact_Icc) a b) _ hδ] with n hn U hU hUB
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hproj : Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b :=
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex ▸
      image_subset_iff.2 fun p hp => (hUB hp).1
  have hbound := score_sub_capScore_le hU α hαL (AngularGrid.dyadic n) fun x hx =>
    (le_abs_self _).trans (Real.dist_eq _ _ ▸ hn ((hU.toCompactCap, α), x)
      ⟨⟨hUB, mem_univ _⟩, hproj (middleHalfInterval_subset hlr hx)⟩).le
  refine ⟨sub_nonneg.mpr (capScore_le_score hU α hαL _), hbound.trans ?_⟩
  rw [capWidth, mul_div_assoc', div_le_iff₀ hden]
  nlinarith [(hproj ⟨le_rfl, hlr⟩).1, (hproj ⟨hlr, le_rfl⟩).2]

theorem exists_level_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (m : ℕ) :
    ∃ n ≥ m, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U α hαL (AngularGrid.dyadic n) - capScore U α ∧
          score U α hαL (AngularGrid.dyadic n) - capScore U α ≤ ε :=
  ((eventually_ge_atTop m).and (eventually_score_error_le hab hε α hαL)).exists

end PartialGrid

end AmbidextrousSofa
