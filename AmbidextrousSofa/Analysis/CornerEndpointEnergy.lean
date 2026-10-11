module

public import AmbidextrousSofa.Analysis.CornerPropagation

@[expose] public section

/-!
# The actual endpoint energy bound

The clipped energy is bounded by the larger of its initial value and
`17/4`, also through an interval where both sources vanish and the first
momentum may exceed one. Equality at the threshold does not need an
interior starting point with strictly smaller energy.
-/

open Set MeasureTheory

namespace AmbidextrousSofa

/-- The clipped energy stays below the larger of `17/4` and its initial value while, almost
everywhere, either the first momentum is at most one or both sources vanish; with both sources
zero it decreases for every value of the first momentum. -/
theorem clippedCornerEnergy_le_max_of_zero_source_alternative
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hqbound : ∀ᵐ t ∂volume.restrict (Ioo a b), -1 ≤ q t)
    (hκ : ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2)
    (halternative : ∀ᵐ t ∂volume.restrict (Ioo a b), p t ≤ 1 ∨ u t = 0 ∧ v t = 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) := by
  apply absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab (le_max_right _ _) _ ht
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy hp hab hode,
    hqbound, hκ, hshadow, halternative] with s hd hqb hk hs ha hE
  rw [hd.deriv]
  rcases ha with hp1 | ⟨hu0, hv0⟩
  · exact clippedCornerEnergy_derivative_nonpos_above hp1 hqb hk hs ((le_max_left _ _).trans_lt hE)
  -- With both sources zero the energy decreases for every value of the first momentum.
  rw [hu0, hv0]
  split_ifs with hps
  · rw [max_eq_left hps.le]
    linarith
  · rw [max_eq_right (not_lt.1 hps)]
    nlinarith [mul_nonneg (by linarith : 0 ≤ q s + 1) (by linarith : 0 ≤ 1 - p s)]

end AmbidextrousSofa
