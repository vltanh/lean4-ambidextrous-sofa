module

public import AmbidextrousSofa.Analysis.GridPolygon

@[expose] public section

/-!
# Uniform recovery of the full spatial objective

The error of a finite score is the middle-window integral of the omitted
barrier height; this bound holds for any continuous finite barrier below
the actual one. The finite polygon source system is the actual finite
angular niche, and uniform angular approximation controls this
moving-window error on the whole boxed cap domain, including degenerate
caps.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

/-- A score whose continuous barrier `G` lies below the barrier `N` of the cap score, and within
`ε / (b - a + 1)` of it on `[a, b]`, is at least the cap score and exceeds it by at most `ε`,
for every cap in `[a, b] × [0, 1]`. -/
theorem IsDownwardCap.score_error_le {U : Set Plane} (hU : IsDownwardCap U) {a b α ε : ℝ}
    (hUB : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1) (hε : 0 < ε) {N G : ℝ → ℝ}
    (hN : IntegrableOn N (middleHalfInterval (horizontalLeft U) (horizontalRight U)))
    (hscore : capScore U α =
      (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      ∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), N x)
    (hG : Continuous G) (hGN : ∀ x, G x ≤ N x)
    (herror : ∀ x ∈ Icc a b, dist (N x) (G x) < ε / (b - a + 1)) :
    0 ≤ (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), G x) - capScore U α ∧
    (∫ x in Icc (horizontalLeft U) (horizontalRight U) \
        middleHalfInterval (horizontalLeft U) (horizontalRight U), capRoof U x) -
      (∫ x in middleHalfInterval (horizontalLeft U) (horizontalRight U), G x) - capScore U α ≤
        ε := by
  have hlr := horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact
  have hproj : Icc (horizontalLeft U) (horizontalRight U) ⊆ Icc a b :=
    hU.horizontalProjection_eq_Icc ▸
      image_subset_iff.2 fun p hp => (hUB hp).1
  have hab := hproj ⟨le_rfl, hlr⟩
  have hab' := hproj ⟨hlr, le_rfl⟩
  have hden : 0 < b - a + 1 := by linarith [hab.1, hab'.2]
  rw [hscore, sub_sub_sub_cancel_left, ← integral_sub hN hG.integrableOn_Icc]
  refine ⟨integral_nonneg fun x => sub_nonneg.mpr (hGN x), ?_⟩
  calc _ ≤ ∫ _ in middleHalfInterval (horizontalLeft U) (horizontalRight U), ε / (b - a + 1) :=
        setIntegral_mono_on (hN.sub hG.integrableOn_Icc) continuous_const.integrableOn_Icc
          (measurableSet_middleHalfInterval _ _) fun x hx => (le_abs_self _).trans
            (herror x (hproj (middleHalfInterval_subset hlr hx))).le
    _ = (horizontalRight U - horizontalLeft U) / 2 * (ε / (b - a + 1)) := by
        rw [setIntegral_const, smul_eq_mul, volumeReal_middleHalfInterval hlr]
    _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hden]
        nlinarith [hab.1, hab'.2]

namespace AngularGrid

open FinitePolygon

def score (U : Set Plane) (grid : Finset QuarterAngle) : ℝ :=
  finiteSpatialScore U (normal grid) (pairList grid) none

/-- The finite objective uniformly approaches the full physical objective
over all actual caps in the fixed box. Its error is always nonnegative. -/
theorem eventually_score_error_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ U : Set Plane, IsDownwardCap U →
      U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 →
        0 ≤ score U (dyadic n) - capScore U (Real.pi / 2) ∧
          score U (dyadic n) - capScore U (Real.pi / 2) ≤ ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (tendstoUniformlyOn_dyadic_box
    (isCompact_Icc.prod isCompact_Icc) a b) (ε / (b - a + 1)) (by positivity)] with n hn U hU hUB
  have hG := (continuous_niche (dyadic n)).comp (Continuous.prodMk_right hU.toCompactCap)
  rw [score, finiteSpatialScore_eq_integrals hU, funext (finiteBarrier_eq_niche hU _)]
  exact hU.score_error_le hUB hε (integrableOn_sweptNiche_Icc hU.isCompact (by positivity) le_rfl
    _ _) hU.capScore_pi_div_two hG (niche_le_sweptNiche hU.toCompactCap _)
    fun x hx => hn (hU.toCompactCap, x) ⟨hUB, hx⟩

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
