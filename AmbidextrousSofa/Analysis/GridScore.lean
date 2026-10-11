module

public import AmbidextrousSofa.Analysis.GridPolygon

@[expose] public section

/-!
# Uniform recovery of the full spatial objective

The finite polygon source system is the actual finite angular niche. Its
score error is therefore exactly the middle-window integral of the omitted
niche height. Uniform angular approximation controls this moving-window
error on the whole boxed cap domain, including degenerate caps.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

def score (U : Set Plane) (grid : Finset QuarterAngle) : ℝ :=
  finiteSpatialScore U (normal grid) (pairList grid) none

theorem score_eq_integrals {U : Set Plane} (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    score U grid =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), niche hU.toCompactCap grid x := by
  simp only [score, finiteSpatialScore_eq_integrals hU, finiteBarrier_eq_niche hU grid]

theorem score_sub_capScore_eq {U : Set Plane} (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    score U grid - capScore U (Real.pi / 2) =
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        sweptNiche U (Real.pi / 2) x - niche hU.toCompactCap grid x := by
  have hN : IntegrableOn (sweptNiche U (Real.pi / 2))
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_sweptNiche_Icc hU.isCompact (by positivity) le_rfl _ _
  have hG : IntegrableOn (niche hU.toCompactCap grid)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    ((continuous_niche grid).comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  rw [score_eq_integrals hU grid, hU.capScore_pi_div_two, integral_sub hN hG]
  ring

theorem capScore_le_score {U : Set Plane} (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    capScore U (Real.pi / 2) ≤ score U grid := by
  rw [← sub_nonneg, score_sub_capScore_eq hU grid]
  exact integral_nonneg fun x => sub_nonneg.mpr (niche_le_sweptNiche hU.toCompactCap grid x)

theorem score_sub_capScore_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) {ε : ℝ}
    (herror : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      sweptNiche U (Real.pi / 2) x - niche hU.toCompactCap grid x ≤ ε) :
    score U grid - capScore U (Real.pi / 2) ≤ capWidth U / 2 * ε := by
  have hε : IntegrableOn (fun _ => ε) (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    continuous_const.integrableOn_Icc
  rw [score_sub_capScore_eq hU grid]
  refine (integral_mono_of_nonneg (.of_forall fun x => sub_nonneg.mpr
    (niche_le_sweptNiche hU.toCompactCap grid x)) hε ((ae_restrict_iff'
      (measurableSet_middleHalfInterval _ _)).mpr (.of_forall herror))).trans_eq ?_
  rw [setIntegral_const, smul_eq_mul,
    volumeReal_middleHalfInterval (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]
  rfl

/-- The finite objective uniformly approaches the full physical objective
over all actual caps in the fixed box. Its error is always nonnegative. -/
theorem eventually_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U (dyadic n) - capScore U (Real.pi / 2) ∧
          score U (dyadic n) - capScore U (Real.pi / 2) ≤ ε := by
  have hden : 0 < b - a + 1 := by linarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_dyadic_box
    (isCompact_Icc.prod isCompact_Icc) a b) (ε / (b - a + 1)) (by positivity)] with n hn U hU hUB
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hproj : Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b := by
    rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    rintro x ⟨p, hp, rfl⟩
    exact (hUB hp).1
  refine ⟨sub_nonneg.mpr (capScore_le_score hU _), (score_sub_capScore_le hU _ fun x hx =>
    ((le_abs_self _).trans_lt (hn (hU.toCompactCap, x)
      ⟨hUB, hproj (middleHalfInterval_subset hlr hx)⟩)).le).trans ?_⟩
  have := (hproj ⟨le_rfl, hlr⟩).1
  have := (hproj ⟨hlr, le_rfl⟩).2
  calc capWidth U / 2 * (ε / (b - a + 1)) ≤ (b - a + 1) * (ε / (b - a + 1)) := by
        unfold capWidth; gcongr; linarith
    _ = ε := mul_div_cancel₀ _ hden.ne'

/-- Arbitrarily fine objective approximation is available while forcing
the chosen dyadic level to exceed any prescribed stage. -/
theorem exists_level_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) (m : ℕ) :
    ∃ n ≥ m, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U (dyadic n) - capScore U (Real.pi / 2) ∧
          score U (dyadic n) - capScore U (Real.pi / 2) ≤ ε :=
  ((eventually_ge_atTop m).and (eventually_score_error_le hab hε)).exists

end AngularGrid

end AmbidextrousSofa
