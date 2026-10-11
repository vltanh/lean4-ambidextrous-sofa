module

public import AmbidextrousSofa.Analysis.CornerPropagation

@[expose] public section

/-!
# The actual endpoint energy bound

The clipped energy is bounded by the larger of its true endpoint limit
and `17/4`. Passing to the endpoint uses the established one-sided
support limits. In particular, equality at the threshold does not need
an interior starting point with strictly smaller energy.
-/

open Set MeasureTheory

namespace AmbidextrousSofa

theorem clippedCornerEnergy_le_max_initial
    {p q u v : ℝ → ℝ} {a b : ℝ}
    (hp : AbsolutelyContinuousOnInterval p a b)
    (hq : AbsolutelyContinuousOnInterval q a b) (hab : a ≤ b)
    (hode : ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt p (u t - 1 - q t) t ∧ HasDerivAt q (v t - 1 + p t) t)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioo a b), p t ≤ 1 ∧ -1 ≤ q t)
    (hκ : ∀ᵐ t ∂volume.restrict (Ioo a b), v t ≤ sourceKappa (p t))
    (hshadow : ∀ᵐ t ∂volume.restrict (Ioo a b),
      0 < p t → 0 < q t → u t = 0 ∧ v t ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    clippedCornerEnergy p q t ≤ max (17 / 4) (clippedCornerEnergy p q a) := by
  refine absolutelyContinuousOnInterval_le_of_ae_deriv_nonpos_above
    (absolutelyContinuousOnInterval_clippedCornerEnergy hp hq) hab (le_max_right _ _) ?_ ht
  filter_upwards [ae_hasDerivAt_clippedCornerEnergy hp hab hode, hbound, hκ, hshadow]
    with x hd hb hk hs hE
  exact hd.deriv ▸ clippedCornerEnergy_derivative_nonpos_above hb.1 hb.2 hk hs
    ((le_max_left _ _).trans_lt hE)

end AmbidextrousSofa
