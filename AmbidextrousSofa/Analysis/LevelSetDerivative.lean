import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.LeftRightNhds

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
  let S := {x : ℝ | f x = c}
  have hcount : {x ∈ S | 𝓝[S ∩ Ioi x] x = ⊥}.Countable :=
    countable_setOfPred_isolated_right_within
  filter_upwards [hcount.ae_notMem volume] with x hx
  intro hfx
  have hne : 𝓝[S ∩ Ioi x] x ≠ ⊥ := fun hbot => hx ⟨hfx, hbot⟩
  letI : NeBot (𝓝[S ∩ Ioi x] x) := ⟨hne⟩
  have hlevel : ∀ᶠ y in 𝓝[S ∩ Ioi x] x, f y = c :=
    self_mem_nhdsWithin.mono (fun y hy => hy.1)
  have hle : 𝓝[S ∩ Ioi x] x ≤ 𝓝[≠] x :=
    nhdsWithin_mono x (fun y hy => by
      change y ≠ x
      exact hy.2.ne')
  exact deriv_zero_of_frequently_const (hlevel.frequently.filter_mono hle)

/-- Two successive level-set applications give the precise flatness
input used at a floor contact. The actual derivative formulas are
supplied separately, so no differentiability is silently assumed. -/
theorem ae_two_derivatives_eq_zero_on_level (f g : ℝ → ℝ) :
    ∀ᵐ x : ℝ ∂volume,
      (f x = 0 → deriv f x = 0) ∧ (g x = 0 → deriv g x = 0) :=
  (ae_deriv_eq_zero_on_level f 0).and (ae_deriv_eq_zero_on_level g 0)

end AmbidextrousSofa
