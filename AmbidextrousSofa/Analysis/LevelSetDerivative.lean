module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

/-!
# Derivatives vanish almost everywhere on a fixed level set

Apart from a countable set of points isolated on the right within the
level set, every level-set point is approached by other points on the
same level. The ordinary derivative is therefore zero there. No
regularity or measurability assumption is needed for this statement:
Lean's total derivative is zero at nondifferentiable points as well.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem ae_deriv_eq_zero_on_level (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x : ℝ ∂volume, f x = c → deriv f x = 0 := by
  filter_upwards [(countable_setOfPred_isolated_right_within (s := {x | f x = c})).ae_notMem _]
    with x hx hfx
  have : NeBot (𝓝[{x | f x = c} ∩ Ioi x] x) := ⟨fun h => hx ⟨hfx, h⟩⟩
  exact deriv_zero_of_frequently_const <| .filter_mono
    (eventually_mem_nhdsWithin.mono fun _ hy => hy.1).frequently
    (nhdsWithin_mono x fun _ (hy : _ ∈ {x | f x = c} ∩ Ioi x) => hy.2.ne')

/-- Two successive level-set applications give the precise flatness
input used at a floor contact. The actual derivative formulas are
supplied separately, so no differentiability is silently assumed. -/
theorem ae_two_derivatives_eq_zero_on_level (f g : ℝ → ℝ) :
    ∀ᵐ x : ℝ ∂volume,
      (f x = 0 → deriv f x = 0) ∧ (g x = 0 → deriv g x = 0) :=
  (ae_deriv_eq_zero_on_level f 0).and (ae_deriv_eq_zero_on_level g 0)

end AmbidextrousSofa
