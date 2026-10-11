module

public import AmbidextrousSofa.Measure.SignedRoof

@[expose] public section

/-!
# Identities for the signed three-arc area formula

The second tangent arc, reversed corner arc, and first tangent arc of a
support pair have explicit coordinate determinants, and the tangent arcs
satisfy density identities whose corrections are momentum derivatives.
These identities and the one-dimensional integration lemmas below are used
by `SignedRoofIntegralAC`, which integrates the arcs as actual graphs.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

def innerCornerDX (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  supportP fD g t * Real.cos t - supportQ gD f t * Real.sin t

def innerCornerDY (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  supportP fD g t * Real.sin t + supportQ gD f t * Real.cos t

def cornerDensity (f g fD gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - 1) * supportQ gD f t - (g t - 1) * supportP fD g t

def firstMomentumPrimitive (f g fD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t - 1) * supportP fD g t

def secondMomentumPrimitive (f g gD : ℝ → ℝ) (t : ℝ) : ℝ :=
  (g t - 1) * supportQ gD f t

def firstMomentumDerivative (f g fD gD fDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  fD t * supportP fD g t + (f t - 1) * (fDD t - gD t)

def secondMomentumDerivative (f g fD gD gDD : ℝ → ℝ) (t : ℝ) : ℝ :=
  gD t * supportQ gD f t + (g t - 1) * (gDD t + fD t)

theorem coordDet_innerCorner (f g fD gD : ℝ → ℝ) (t : ℝ) :
    coordDet (innerCornerPoint f g t)
      (innerCornerDX f g fD gD t, innerCornerDY f g fD gD t) =
      cornerDensity f g fD gD t := by
  simp only [coordDet, innerCornerPoint, innerCornerDX, innerCornerDY, cornerDensity]
  linear_combination ((f t - 1) * supportQ gD f t - (g t - 1) * supportP fD g t) *
    Real.sin_sq_add_cos_sq t

theorem innerCorner_eq_firstTangent_of_momentum_zero
    {f g fD : ℝ → ℝ} {t : ℝ} (hp : supportP fD g t = 0) :
    innerCornerPoint f g t = firstTangentPoint f fD t := by
  rw [innerCornerPoint, firstTangentPoint, Reference.supportPoint,
    show fD t = g t - 1 by unfold supportP at hp; linarith]

theorem innerCorner_eq_secondTangent_of_momentum_zero
    {f g gD : ℝ → ℝ} {t : ℝ} (hq : supportQ gD f t = 0) :
    innerCornerPoint f g t = secondTangentPoint g gD t := by
  rw [secondTangentPoint, companionSupportPoint_coordinates, innerCornerPoint,
    show gD t = -(f t - 1) by unfold supportQ at hq; linarith]
  ext <;> dsimp <;> ring

theorem firstTangent_density_identity (f g fD gD fDD : ℝ → ℝ) (t : ℝ) :
    (f t - 1) * (f t - 1 + fDD t) = cornerDensity f g fD gD t -
      supportP fD g t ^ 2 + firstMomentumDerivative f g fD gD fDD t := by
  unfold cornerDensity firstMomentumDerivative supportP supportQ
  ring

theorem secondTangent_density_identity (f g fD gD gDD : ℝ → ℝ) (t : ℝ) :
    (g t - 1) * (g t - 1 + gDD t) = cornerDensity f g fD gD t -
      supportQ gD f t ^ 2 + secondMomentumDerivative f g fD gD gDD t := by
  unfold cornerDensity secondMomentumDerivative supportP supportQ
  ring

/-- Integration of a density identity `L = c - P ^ 2 + M` whose correction `M` integrates
to `m`. -/
theorem integral_density_of_identity {a b m : ℝ} {L c P M : ℝ → ℝ}
    (hid : ∀ t, L t = c t - P t ^ 2 + M t) (hc : Continuous c) (hP : Continuous P)
    (hMi : IntervalIntegrable M volume a b) (hftc : ∫ t in a..b, M t = m) :
    (∫ t in a..b, L t) = (∫ t in a..b, c t) - (∫ t in a..b, P t ^ 2) + m := by
  have hc' := hc.intervalIntegrable (μ := volume) a b
  have hP' : IntervalIntegrable (fun t => P t ^ 2) volume a b := (hP.pow 2).intervalIntegrable a b
  rw [intervalIntegral.integral_congr fun t _ => hid t,
    intervalIntegral.integral_add (hc'.sub hP') hMi, intervalIntegral.integral_sub hc' hP', hftc]

theorem integral_split_of_eqOn {a b c : ℝ} {F G H : ℝ → ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hF : Continuous F) (hG : EqOn F G (Icc a b)) (hH : EqOn F H (Icc b c)) :
    (∫ t in a..c, F t) = (∫ t in a..b, G t) + ∫ t in b..c, H t := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable a b)
    (hF.intervalIntegrable b c)]
  exact congrArg₂ (· + ·) (intervalIntegral.integral_congr (uIcc_of_le hab ▸ hG))
    (intervalIntegral.integral_congr (uIcc_of_le hbc ▸ hH))

/-- A single sign switch changes a clipped square integral into its actual
active-interval integral. Endpoint values do not affect either integral. -/
theorem integral_min_sq_of_sign_switch {a b c : ℝ} {p : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hp : Continuous p)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ p t) (hright : ∀ t ∈ Icc b c, p t ≤ 0) :
    (∫ t in a..c, min (p t) 0 ^ 2) = ∫ t in b..c, p t ^ 2 := by
  rw [integral_split_of_eqOn (F := fun t => min (p t) 0 ^ 2) (G := 0) (H := fun t => p t ^ 2)
    hab hbc ((hp.min continuous_const).pow 2) (fun t ht => by simp [min_eq_right (hleft t ht)])
    fun t ht => by simp [min_eq_left (hright t ht)]]
  simp

theorem integral_max_sq_of_sign_switch {a b c : ℝ} {q : ℝ → ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hq : Continuous q)
    (hleft : ∀ t ∈ Icc a b, 0 ≤ q t) (hright : ∀ t ∈ Icc b c, q t ≤ 0) :
    (∫ t in a..c, max (q t) 0 ^ 2) = ∫ t in a..b, q t ^ 2 := by
  rw [integral_split_of_eqOn (F := fun t => max (q t) 0 ^ 2) (G := fun t => q t ^ 2) (H := 0)
    hab hbc ((hq.max continuous_const).pow 2) (fun t ht => by simp [max_eq_left (hleft t ht)])
    fun t ht => by simp [max_eq_right (hright t ht)]]
  simp

end AmbidextrousSofa
