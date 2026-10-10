module

public import AmbidextrousSofa.Analysis.FiniteHorizontalMoment
public import AmbidextrousSofa.Analysis.SourceOccupation

@[expose] public section

/-!
# Horizontal source mass with the top normal removed

The cosine-weighted selected defect controls every angular set separated
from the top normal. Near the top, the actual neighboring-wall estimate
controls the entire inner mass by the angular interval length and one mesh
cell. This gives a finite horizontal comparison with an explicit error;
the outer term is a literal spatial source density bounded by one.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem abs_cos_ge_sin_of_outside_top_interval {η t : ℝ}
    (hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2)) (ht : t ∈ Ioo (0 : ℝ) Real.pi)
    (hout : t ∉ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) :
    Real.sin η ≤ |Real.cos t| := by
  by_cases hlo : t < Real.pi / 2 - η
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi ht.1.le
      (show Real.pi / 2 - η ≤ Real.pi by linarith [Real.pi_pos, hη.1]) hlo.le
    rw [Real.cos_pi_div_two_sub] at h
    exact h.trans (le_abs_self _)
  · have hhi : Real.pi / 2 + η < t := by
      by_contra h
      exact hout ⟨le_of_not_gt hlo, le_of_not_gt h⟩
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (show 0 ≤ Real.pi / 2 + η by linarith [Real.pi_pos, hη.1]) ht.2.le hhi.le
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two] at h
    have hneg : Real.sin η ≤ -Real.cos t := by linarith
    exact hneg.trans (neg_le_abs _)

namespace AngularGrid

open FinitePolygon

def horizontalOuterDensity (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ → ℝ := by
  classical
  exact (roofExpr (ι := SourceIndex grid)).horizontalSourceDensity (wallSlope (normal grid))
    (roofIntercept (normal grid) (fun i => support U (normal grid i)))
    (Finset.univ.filter (fun j => fullAngle grid j ∈ E))

def horizontalOuterMass (U : Set Plane) (grid : Finset QuarterAngle) (E : Set ℝ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
    finiteWingMass U (normal grid) (some j)

theorem horizontalOuterDensity_bounds (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (x : ℝ) :
    0 ≤ horizontalOuterDensity U grid E x ∧ horizontalOuterDensity U grid E x ≤ 1 := by
  classical
  exact WallExpr.horizontalSourceDensity_bounds _ _ _ _ _

theorem measurable_horizontalOuterDensity (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) : Measurable (horizontalOuterDensity U grid E) := by
  classical
  exact WallExpr.measurable_horizontalSourceDensity _ _ _ _

theorem intervalIntegrable_horizontalOuterDensity (U : Set Plane)
    (grid : Finset QuarterAngle) (E : Set ℝ) (l r : ℝ) :
    IntervalIntegrable (horizontalOuterDensity U grid E) volume l r := by
  classical
  exact WallExpr.intervalIntegrable_horizontalSourceDensity _ _ _ _ l r

theorem horizontalOuterMass_eq_integrals {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (E : Set ℝ) :
    horizontalOuterMass U grid E =
      (∫ x in (horizontalLeft U)..(horizontalLeft U + capWidth U / 4),
        horizontalOuterDensity U grid E x) +
      ∫ x in (horizontalRight U - capWidth U / 4)..(horizontalRight U),
        horizontalOuterDensity U grid E x := by
  classical
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  unfold horizontalOuterDensity
  rw [WallExpr.integral_horizontalSourceDensity _ _ _ _ (by unfold capWidth; linarith),
    WallExpr.integral_horizontalSourceDensity _ _ _ _ (by unfold capWidth; linarith)]
  simp only [horizontalOuterMass, finiteWingMass, capWidth, Finset.sum_add_distrib]

theorem horizontalOuterDensity_eq_zero_of_no_edge {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle)
    (hpoly : U = circumscription U (normal grid)) (E : Set ℝ)
    {x : ℝ} (hx : x ∈ horizontalProjection U)
    (hno : ∀ t ∈ E, (x, capRoof U x) ∉ MovingSofaOptimality.edge U t) :
    horizontalOuterDensity U grid E x = 0 := by
  classical
  unfold horizontalOuterDensity WallExpr.horizontalSourceDensity WallExpr.sourceDensity
  cases hsource : (roofExpr (ι := SourceIndex grid)).source (fun i => wallSlope (normal grid) i * x +
    roofIntercept (normal grid) (fun j => support U (normal grid j)) i) with
  | none => rfl
  | some j =>
    have hj : j ∉ Finset.univ.filter (fun i : SourceIndex grid => fullAngle grid i ∈ E) := by
      intro hj
      apply hno (fullAngle grid j) (Finset.mem_filter.mp hj).2
      exact outerSource_mem_edge hU (normal grid) (normal_snd_pos grid) hpoly j
        (normal_eq_unitNormal grid j) hx hsource
    simp only [hj, ite_false]

theorem normal_snd_mul_innerSourceMass_eq {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    (normal grid j).2 * innerSourceMass U grid j =
      finiteWingMass U (normal grid) (some j) +
        (normal grid j).2 * normalizedExposureDefect U grid j := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hinner : (normal grid j).2 * innerSourceMass U grid j =
      (barrierExpr (pairList grid) none).sourceMass (wallSlope (normal grid))
        (barrierIntercept (normal grid) (fun i => support U (normal grid i)))
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) (some j) := by
    unfold innerSourceMass innerDensity
    rw [integral_sourceDensity_outward _ _ _ _ (by linarith),
      mul_div_cancel₀ _ (normal_snd_pos grid j).ne']
    rfl
  rw [hinner]
  unfold normalizedExposureDefect finiteExposureDefect finiteWingMass capWidth
  rw [mul_div_cancel₀ _ (normal_snd_pos grid j).ne']
  ring

open Classical in
/-- The finite neighboring-wall estimate controls the complete inner
mass in a small angular interval, with one retained boundary mesh cell. -/
theorem innerSourceMass_sum_interval_le {U : Set Plane} (hU : IsDownwardCap U)
    {R s t : ℝ} (hR : 0 ≤ R) (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (level : ℕ) (hst : s ≤ t) :
    (∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
      fullAngle (dyadic level) j ∈ Icc s t), innerSourceMass U (dyadic level) j) ≤
        (4 * R + 12) * (t - s + mesh level) := by
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : SourceIndex (dyadic level) =>
        fullAngle (dyadic level) j ∈ Icc s t), (4 * R + 12) * mesh level :=
      Finset.sum_le_sum (fun j _ => innerSourceMass_dyadic_le hU hR hbox level j)
    _ = (4 * R + 12) * ∑ j ∈ Finset.univ.filter
        (fun j : SourceIndex (dyadic level) => fullAngle (dyadic level) j ∈ Icc s t),
          mesh level := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_mesh_interval_sources_le level hst) (by linarith)

open Classical in
theorem finitePositiveLength_le_horizontalOuterMass_add_cutoff {U : Set Plane}
    (hU : IsDownwardCap U) (grid : Finset QuarterAngle) {E : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hE : ∀ t ∈ E, δ ≤ |Real.cos t|) :
    finitePositiveLength U (normal grid) (pairList grid) none
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) ≤
      horizontalOuterMass U grid E +
        (∑ j : SourceIndex grid, |(normal grid j).1| *
          |normalizedExposureDefect U grid j|) / δ +
        ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∉ E),
          innerSourceMass U grid j := by
  classical
  rw [← sum_sin_innerSourceMass_eq_positiveLength hU grid,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => fullAngle grid j ∈ E)]
  have hmain :
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
        (normal grid j).2 * innerSourceMass U grid j) ≤
      horizontalOuterMass U grid E +
        ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∈ E),
          |normalizedExposureDefect U grid j| := by
    unfold horizontalOuterMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rw [normal_snd_mul_innerSourceMass_eq hU]
    apply add_le_add_right
    calc
      (normal grid j).2 * normalizedExposureDefect U grid j ≤
          (normal grid j).2 * |normalizedExposureDefect U grid j| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (normal_snd_pos grid j).le
      _ ≤ _ := by
        have hs : (normal grid j).2 ≤ 1 := by
          rw [normal_eq_unitNormal]; exact Real.sin_le_one _
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have hrest :
      (∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∉ E),
        (normal grid j).2 * innerSourceMass U grid j) ≤
      ∑ j ∈ Finset.univ.filter (fun j : SourceIndex grid => fullAngle grid j ∉ E),
        innerSourceMass U grid j := by
    apply Finset.sum_le_sum
    intro j _
    have hs : (normal grid j).2 ≤ 1 := by rw [normal_eq_unitNormal]; exact Real.sin_le_one _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (innerSourceMass_nonneg hU grid j)
  exact add_le_add
    (hmain.trans (add_le_add_right (sum_abs_defect_on_set_le_cos_sum U grid hδ hE) _)) hrest

theorem finitePositiveLength_le_horizontalOuterMass_away_top {U : Set Plane}
    (hU : IsDownwardCap U) {R η : ℝ} (hR : 0 ≤ R)
    (hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1) (level : ℕ)
    (hη : η ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    finitePositiveLength U (normal (dyadic level)) (pairList (dyadic level)) none
        (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4) ≤
      horizontalOuterMass U (dyadic level)
        (Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) +
        (∑ j : SourceIndex (dyadic level), |(normal (dyadic level) j).1| *
          |normalizedExposureDefect U (dyadic level) j|) / Real.sin η +
        (4 * R + 12) * (2 * η + mesh level) := by
  classical
  have hsin : 0 < Real.sin η := Real.sin_pos_of_pos_of_lt_pi hη.1 (by linarith [hη.2, Real.pi_pos])
  have h := finitePositiveLength_le_horizontalOuterMass_add_cutoff hU (dyadic level)
    (E := Ioo (0 : ℝ) Real.pi \ Icc (Real.pi / 2 - η) (Real.pi / 2 + η)) hsin
    (fun t ht => abs_cos_ge_sin_of_outside_top_interval hη ht.1 ht.2)
  have hsmall := innerSourceMass_sum_interval_le hU hR hbox level
    (show Real.pi / 2 - η ≤ Real.pi / 2 + η by linarith [hη.1])
  have hid : Real.pi / 2 + η - (Real.pi / 2 - η) + mesh level = 2 * η + mesh level := by ring
  rw [hid] at hsmall
  refine h.trans (add_le_add_right (le_trans (le_of_eq ?_) hsmall) _)
  -- the two filters agree: a source angle lies in `(0, π)`
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
    fullAngle_mem, true_and, not_not]

end AngularGrid

end AmbidextrousSofa
