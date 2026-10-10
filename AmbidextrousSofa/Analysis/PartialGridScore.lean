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
  rw [score, finiteSpatialScore_eq_integrals hU]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (finiteBarrier_eq_barrier U α hαL grid)

theorem score_sub_capScore_eq {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) :
    score U α hαL grid - capScore U α =
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        partialBarrier U α x - barrier U α grid x := by
  have hN : IntegrableOn (partialBarrier U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_partialBarrier_Icc hU.isCompact (TerminalAngle.pos α) α.property.2 _ _
  have hG : IntegrableOn (barrier U α grid)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    ((continuous_barrier grid).comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  rw [score_eq_integrals hU α hαL grid, capScore_eq_integrals, integral_sub hN hG]
  ring

theorem capScore_le_score {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) :
    capScore U α ≤ score U α hαL grid := by
  apply sub_nonneg.mp
  rw [score_sub_capScore_eq hU α hαL grid]
  exact integral_nonneg (fun x =>
    sub_nonneg.mpr (barrier_le_partialBarrier hU.toCompactCap α grid x))

theorem score_sub_capScore_le {U : Set Plane} (hU : IsDownwardCap U)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2)
    (grid : Finset AngularGrid.QuarterAngle) {ε : ℝ}
    (herror : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      partialBarrier U α x - barrier U α grid x ≤ ε) :
    score U α hαL grid - capScore U α ≤ capWidth U / 2 * ε := by
  have hN : IntegrableOn (partialBarrier U α)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_partialBarrier_Icc hU.isCompact (TerminalAngle.pos α) α.property.2 _ _
  have hG : IntegrableOn (barrier U α grid)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    ((continuous_barrier grid).comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  have hConst : IntegrableOn (fun _ : ℝ => ε)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    continuous_const.integrableOn_Icc
  have hbound := setIntegral_mono_on (hN.sub hG) hConst
    (measurableSet_middleHalfInterval _ _) herror
  rw [score_sub_capScore_eq hU α hαL grid]
  calc
    _ ≤ ∫ _x in middleHalfInterval (horizontalLeft U) (horizontalRight U), ε := hbound
    _ = capWidth U / 2 * ε := by
      rw [setIntegral_const, smul_eq_mul,
        volumeReal_middleHalfInterval (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]
      rfl

theorem eventually_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) :
    ∀ᶠ n in atTop, ∀ U : Set Plane, ∀ hU : IsDownwardCap U,
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U α hαL (AngularGrid.dyadic n) - capScore U α ∧
          score U α hαL (AngularGrid.dyadic n) - capScore U α ≤ ε := by
  let B : Set Plane := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  let δ : ℝ := ε / (b - a + 1)
  have hden : 0 < b - a + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * (b - a + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hDini := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_dyadic_box hB a b) δ hδ
  filter_upwards [hDini] with n hn
  intro U hU hUB
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hprojection : Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b := by
    rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    rintro x ⟨p, hp, rfl⟩
    exact (hUB hp).1
  have hwidth : capWidth U ≤ b - a := by
    have hl := (hprojection ⟨le_rfl, hlr⟩).1
    have hr := (hprojection ⟨hlr, le_rfl⟩).2
    unfold capWidth
    linarith
  have hpoint : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      partialBarrier U α x - barrier U α (AngularGrid.dyadic n) x ≤ δ := by
    intro x hx
    have h := hn ((hU.toCompactCap, α), x)
      ⟨⟨hUB, mem_univ _⟩, hprojection (middleHalfInterval_subset hlr hx)⟩
    rw [Real.dist_eq] at h
    exact (le_abs_self _).trans h.le
  have hbound := score_sub_capScore_le hU α hαL (AngularGrid.dyadic n) hpoint
  have hmul := mul_le_mul_of_nonneg_right hwidth hδ.le
  refine ⟨sub_nonneg.mpr (capScore_le_score hU α hαL (AngularGrid.dyadic n)), ?_⟩
  nlinarith

theorem exists_level_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε)
    (α : TerminalAngle) (hαL : (α : ℝ) < Real.pi / 2) (m : ℕ) :
    ∃ n ≥ m, ∀ U : Set Plane, ∀ hU : IsDownwardCap U,
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U α hαL (AngularGrid.dyadic n) - capScore U α ∧
          score U α hαL (AngularGrid.dyadic n) - capScore U α ≤ ε := by
  obtain ⟨n, hn, herror⟩ := ((eventually_ge_atTop m).and
    (eventually_score_error_le hab hε α hαL)).exists
  exact ⟨n, hn, herror⟩

end PartialGrid

end AmbidextrousSofa
