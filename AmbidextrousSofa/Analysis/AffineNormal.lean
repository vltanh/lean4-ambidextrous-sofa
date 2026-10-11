module

public import AmbidextrousSofa.Geometry.Support
public import MovingSofaOptimality.Basic.Plane
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

@[expose] public section

/-!
# The upward normal of an affine roof

These elementary identities relate an affine ceiling to its literal unit
normal and halfplane. They have no maximality or terminal-angle dependency.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

/-- The actual upward unit normal of the affine ceiling `y = m*x+c`. -/
def affineNormalAngle (m : ℝ) : ℝ := Real.arctan m + Real.pi / 2

theorem affineNormalAngle_mem (m : ℝ) : affineNormalAngle m ∈ Ioo (0 : ℝ) Real.pi := by
  rw [affineNormalAngle, mem_Ioo]
  constructor <;> linarith [Real.neg_pi_div_two_lt_arctan m, Real.arctan_lt_pi_div_two m]

theorem coordDot_affineNormalAngle (p : Plane) (m : ℝ) :
    coordDot p (unitNormal (affineNormalAngle m)) =
      Real.cos (Real.arctan m) * (p.2 - m * p.1) := by
  simp only [affineNormalAngle, unitNormal, coordDot, Real.cos_add_pi_div_two,
    Real.sin_add_pi_div_two, Real.sin_arctan, Real.cos_arctan]
  ring

theorem mem_affine_halfMinus_iff (p : Plane) (m c : ℝ) :
    p ∈ MovingSofaOptimality.halfMinus (affineNormalAngle m) (c * Real.cos (Real.arctan m)) ↔
      p.2 ≤ m * p.1 + c := by
  change coordDot p (unitNormal (affineNormalAngle m)) ≤ c * Real.cos (Real.arctan m) ↔ _
  rw [coordDot_affineNormalAngle, mul_comm c, mul_le_mul_iff_right₀ (Real.cos_arctan_pos m),
    sub_le_iff_le_add']

end AmbidextrousSofa
