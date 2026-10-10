module

public import AmbidextrousSofa.Analysis.PartialSourceBalance
public import AmbidextrousSofa.Analysis.PartialSourceCounting
public import AmbidextrousSofa.Analysis.HorizontalCutoff

@[expose] public section

/-!
# Actual proper horizontal source moment away from the top

The full terminal wall contributes its ordinary literal source. A fixed
proper angle is separated from a sufficiently small neighborhood of the
top normal, where the sampled neighboring-wall estimate controls all
remaining inner mass. Outer source envelopes use the physical outer grid.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem fullAngle_mem (α : TerminalAngle) (grid : Finset QuarterAngle)
    (j : SourceIndex α grid) : fullAngle α grid j ∈ Ioo (0 : ℝ) Real.pi :=
  AngularGrid.fullAngle_mem (outerGrid α grid) j

open Classical in
theorem sum_abs_defect_on_set_le_cos_sum
    (U : Set Plane) (grid : Finset QuarterAngle) {E : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hE : ∀ t ∈ E, δ ≤ |Real.cos t|) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
      |normalizedExposureDefect U α hαL grid j|) ≤
      (∑ j : SourceIndex α grid, |(normal α grid j).1| * |normalizedExposureDefect U α hαL grid j|) / δ := by
  classical
  apply (le_div_iff₀ hδ).mpr
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
        |(normal α grid j).1| * |normalizedExposureDefect U α hαL grid j| := by
      apply Finset.sum_le_sum
      intro j hj
      have h := hE (fullAngle α grid j) (Finset.mem_filter.mp hj).2
      have hn : (normal α grid j).1 = Real.cos (fullAngle α grid j) := by
        rw [normal_eq_unitNormal]
        rfl
      rw [hn, mul_comm]
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem sum_sin_innerSourceMass_eq_positiveLength {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex α grid, (normal α grid j).2 * innerSourceMass U α hαL grid j) =
      finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  rw [finitePositiveLength_eq_sum _ _ _ _ (wallSlopes_injective α grid) (by
    unfold capWidth; linarith)]
  apply Finset.sum_congr rfl
  intro j _
  unfold innerSourceMass innerDensity
  rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
  unfold WallExpr.sourceMass
  field_simp [(normal_snd_pos α grid j).ne']

theorem sum_sin_normalizedExposureDefect_eq_horizontal_balance {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    (∑ j : SourceIndex α grid, (normal α grid j).2 * normalizedExposureDefect U α hαL grid j) =
      finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) -
      (capWidth U / 2 - finiteWingMass U (normal α grid) none) := by
  have hterm (j : SourceIndex α grid) :
      (normal α grid j).2 * normalizedExposureDefect U α hαL grid j =
        finiteExposureDefect U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) j := by
    unfold normalizedExposureDefect
    field_simp [(normal_snd_pos α grid j).ne']
  simp only [hterm]
  exact finite_horizontal_source_balance hU _ _ _ (wallSlopes_injective α grid)

theorem normal_snd_mul_innerSourceMass_eq {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex α grid) :
    (normal α grid j).2 * innerSourceMass U α hαL grid j =
      finiteWingMass U (normal α grid) (some j) +
        (normal α grid j).2 * normalizedExposureDefect U α hαL grid j := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hinner : (normal α grid j).2 * innerSourceMass U α hαL grid j =
      (barrierExpr (pairList α grid) (some (terminalIndex α hαL grid))).sourceMass (wallSlope (normal α grid))
        (barrierIntercept (normal α grid) (fun i => support U (normal α grid i)))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) (some j) := by
    unfold innerSourceMass innerDensity
    rw [integral_sourceDensity_outward _ _ _ _ (by linarith)]
    unfold WallExpr.sourceMass
    field_simp [(normal_snd_pos α grid j).ne']
  rw [hinner]
  unfold normalizedExposureDefect finiteExposureDefect finiteWingMass
  field_simp [(normal_snd_pos α grid j).ne'] <;> ring

open Classical in
theorem finitePositiveLength_le_horizontalOuterMass_add_cutoff {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) {E : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hE : ∀ t ∈ E, δ ≤ |Real.cos t|) :
    finitePositiveLength U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) ≤
      AngularGrid.horizontalOuterMass U (outerGrid α grid) E +
        (∑ j : SourceIndex α grid, |(normal α grid j).1| *
          |normalizedExposureDefect U α hαL grid j|) / δ +
        ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∉ E),
          innerSourceMass U α hαL grid j := by
  classical
  rw [← sum_sin_innerSourceMass_eq_positiveLength hU grid,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => fullAngle α grid j ∈ E)]
  have hmain :
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
        (normal α grid j).2 * innerSourceMass U α hαL grid j) ≤
      AngularGrid.horizontalOuterMass U (outerGrid α grid) E +
        ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∈ E),
          |normalizedExposureDefect U α hαL grid j| := by
    unfold AngularGrid.horizontalOuterMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [normal_snd_mul_innerSourceMass_eq hU]
    apply add_le_add_left
    calc
      (normal α grid j).2 * normalizedExposureDefect U α hαL grid j ≤
          (normal α grid j).2 * |normalizedExposureDefect U α hαL grid j| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (normal_snd_pos α grid j).le
      _ ≤ _ := by
        have hs : (normal α grid j).2 ≤ 1 := by
          rw [normal_eq_unitNormal]; exact Real.sin_le_one _
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have hrest :
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∉ E),
        (normal α grid j).2 * innerSourceMass U α hαL grid j) ≤
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex α grid => fullAngle α grid j ∉ E),
        innerSourceMass U α hαL grid j := by
    apply Finset.sum_le_sum
    intro j _
    have hs : (normal α grid j).2 ≤ 1 := by rw [normal_eq_unitNormal]; exact Real.sin_le_one _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (innerSourceMass_nonneg hU α hαL grid j)
  exact add_le_add
    (hmain.trans (add_le_add_left (sum_abs_defect_on_set_le_cos_sum (α := α) (hαL := hαL) U grid hδ hE) _)) hrest

theorem finitePositiveLength_le_horizontalOuterMass_away_top {U : Set Plane}
    (hU : IsDownwardCap U) {R η : ℝ} (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ)
    (hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2)) (hterminal : η < Real.pi / 2 - α) :
    finitePositiveLength U (normal α (dyadic level)) (pairList α (dyadic level)) (some (terminalIndex α hαL (dyadic level)))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) ≤
      AngularGrid.horizontalOuterMass U (outerGrid α (dyadic level))
        (Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) +
        (∑ j : SourceIndex α (dyadic level), |(normal α (dyadic level) j).1| *
          |normalizedExposureDefect U α hαL (dyadic level) j|) / Real.sin η +
        (8 * R + 24) * (2 * η + mesh α level) := by
  classical
  have hsin : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos])
  have h := finitePositiveLength_le_horizontalOuterMass_add_cutoff (α := α) (hαL := hαL) hU (dyadic level) hsin
    (fun t ht => abs_cos_ge_sin_of_outside_top_interval hη ht.1 ht.2)
  have hfilter :
      Finset.univ.filter (fun j : SourceIndex α (dyadic level) => fullAngle α (dyadic level) j ∉
        Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) =
      Finset.univ.filter (fun j : SourceIndex α (dyadic level) => fullAngle α (dyadic level) j ∈
        Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_diff,
      fullAngle_mem, true_and, not_not]
  rw [hfilter] at h
  have hsmall := innerSourceMass_sum_interval_le hU α hαL hR hbox level
    (show Real.pi / 2 - η ≤ Real.pi / 2 + η by linarith [hη.1])
    (fun ht => by linarith [ht.1])
  have hid : Real.pi / 2 + η - (Real.pi / 2 - η) + mesh α level = 2 * η + mesh α level := by ring
  rw [hid] at hsmall
  exact h.trans (add_le_add_left hsmall _)


end PartialGrid
end AmbidextrousSofa
