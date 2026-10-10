import AmbidextrousSofa.Analysis.GridPolygon

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
  rw [score, finiteSpatialScore_eq_integrals hU]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (finiteBarrier_eq_niche hU grid)

theorem score_sub_capScore_eq {U : Set Plane} (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    score U grid - capScore U (Real.pi / 2) =
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U),
        sweptNiche U (Real.pi / 2) x - niche hU.toCompactCap grid x := by
  have hN : IntegrableOn (sweptNiche U (Real.pi / 2))
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_sweptNiche_Icc hU.isCompact (by linarith [Real.pi_pos]) le_rfl _ _
  have hG : IntegrableOn (niche hU.toCompactCap grid)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    ((continuous_niche grid).comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  rw [score_eq_integrals hU grid, hU.capScore_pi_div_two, integral_sub hN hG]
  ring

theorem capScore_le_score {U : Set Plane} (hU : IsDownwardCap U) (grid : Finset QuarterAngle) :
    capScore U (Real.pi / 2) ≤ score U grid := by
  apply sub_nonneg.mp
  rw [score_sub_capScore_eq hU grid]
  exact integral_nonneg (fun x => sub_nonneg.mpr (niche_le_sweptNiche hU.toCompactCap grid x))

theorem score_sub_capScore_le {U : Set Plane} (hU : IsDownwardCap U)
    (grid : Finset QuarterAngle) {ε : ℝ}
    (herror : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      sweptNiche U (Real.pi / 2) x - niche hU.toCompactCap grid x ≤ ε) :
    score U grid - capScore U (Real.pi / 2) ≤ capWidth U / 2 * ε := by
  have hN : IntegrableOn (sweptNiche U (Real.pi / 2))
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    integrableOn_sweptNiche_Icc hU.isCompact (by linarith [Real.pi_pos]) le_rfl _ _
  have hG : IntegrableOn (niche hU.toCompactCap grid)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    ((continuous_niche grid).comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
  have hConst : IntegrableOn (fun _ : ℝ => ε)
      (middleHalfInterval (horizontalLeft U) (horizontalRight U)) :=
    continuous_const.integrableOn_Icc
  have hbound := setIntegral_mono_on (hN.sub hG) hConst (measurableSet_middleHalfInterval _ _) herror
  rw [score_sub_capScore_eq hU grid]
  calc
    _ ≤ ∫ _x in middleHalfInterval (horizontalLeft U) (horizontalRight U), ε := hbound
    _ = capWidth U / 2 * ε := by
      rw [setIntegral_const, smul_eq_mul,
        volumeReal_middleHalfInterval (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact)]
      rfl

/-- The finite objective uniformly approaches the full physical objective
over all actual caps in the fixed box. Its error is always nonnegative. -/
theorem eventually_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ U : Set Plane, ∀ hU : IsDownwardCap U,
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U (dyadic n) - capScore U (Real.pi / 2) ∧
          score U (dyadic n) - capScore U (Real.pi / 2) ≤ ε := by
  let B : Set Plane := Icc a b ×ˢ Icc (0 : ℝ) 1
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  let δ : ℝ := ε / (b - a + 1)
  have hden : 0 < b - a + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ * (b - a + 1) = ε := div_mul_cancel₀ ε hden.ne'
  have hDini := Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_dyadic_box hB a b) δ hδ
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
      sweptNiche U (Real.pi / 2) x - niche hU.toCompactCap (dyadic n) x ≤ δ := by
    intro x hx
    have h := hn (hU.toCompactCap, x)
      ⟨hUB, hprojection (middleHalfInterval_subset hlr hx)⟩
    rw [Real.dist_eq] at h
    exact (le_abs_self _).trans h.le
  have hbound := score_sub_capScore_le hU (dyadic n) hpoint
  have hmul := mul_le_mul_of_nonneg_right hwidth hδ.le
  refine ⟨sub_nonneg.mpr (capScore_le_score hU (dyadic n)), ?_⟩
  nlinarith

/-- Arbitrarily fine objective approximation is available while forcing
the chosen dyadic level to exceed any prescribed stage. -/
theorem exists_level_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) (m : ℕ) :
    ∃ n ≥ m, ∀ U : Set Plane, ∀ hU : IsDownwardCap U,
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U (dyadic n) - capScore U (Real.pi / 2) ∧
          score U (dyadic n) - capScore U (Real.pi / 2) ≤ ε := by
  obtain ⟨n, hn, herror⟩ := ((eventually_ge_atTop m).and
    (eventually_score_error_le hab hε)).exists
  exact ⟨n, hn, herror⟩

end AngularGrid

end AmbidextrousSofa
