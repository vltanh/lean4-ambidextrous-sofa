module

public import AmbidextrousSofa.Main

/-!
# The solution: the eight theorems of `Challenge.lean`

This module is the solution that Comparator checks against `Challenge.lean` (`comparator.json`).
It restates each theorem of the Challenge under its name, and proves it by the theorem of the same
name in `AmbidextrousSofa.Main`, which derives it from the library. The definitions that the
statements use are those of `AmbidextrousSofa.ChallengeDefs`, which the Challenge copies.
-/

@[expose] public section

open Set MeasureTheory

namespace Ambidextrous

/-- The equation `4Y³ + 3Y = 1` has exactly one positive solution, `Y = 0.2980…`. -/
theorem existsUnique_root : ∃! Y : ℝ, 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1 :=
  AmbidextrousSofa.Main.existsUnique_root

/-- **Romik's value.** The area `1 + 4Y² + arctan Y` of Romik's ambidextrous sofa is
`∛(3 + 2√2) + ∛(3 - 2√2) - 1 + arctan (½ (∛(√2 + 1) - ∛(√2 - 1))) = 1.64495…`. -/
theorem value_eq_romik (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    1 + 4 * Y ^ 2 + Real.arctan Y =
      (3 + 2 * √2) ^ (1 / 3 : ℝ) + (3 - 2 * √2) ^ (1 / 3 : ℝ) - 1 +
        Real.arctan (((√2 + 1) ^ (1 / 3 : ℝ) - (√2 - 1) ^ (1 / 3 : ℝ)) / 2) :=
  AmbidextrousSofa.Main.value_eq_romik hY

/-- **Optimality.** Every ambidextrous sofa has area at most `1 + 4Y² + arctan Y`. -/
theorem volume_le (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) (S : Set (ℝ × ℝ))
    (hS : IsAmbidextrous S) : volume.real S ≤ 1 + 4 * Y ^ 2 + Real.arctan Y :=
  AmbidextrousSofa.Main.volume_le hY S hS

/-- Romik's ambidextrous sofa is an ambidextrous sofa. -/
theorem isAmbidextrous_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    IsAmbidextrous (referenceSofa Y) :=
  AmbidextrousSofa.Main.isAmbidextrous_referenceSofa hY

/-- Romik's ambidextrous sofa has area `1 + 4Y² + arctan Y`. -/
theorem volume_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    volume.real (referenceSofa Y) = 1 + 4 * Y ^ 2 + Real.arctan Y :=
  AmbidextrousSofa.Main.volume_referenceSofa hY

/-- Every image of Romik's ambidextrous sofa by a rotation about the origin followed by a translation
is an ambidextrous sofa. -/
theorem isAmbidextrous_image_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) (θ : ℝ)
    (v : ℝ × ℝ) : IsAmbidextrous ((fun p => rotate θ p + v) '' referenceSofa Y) :=
  AmbidextrousSofa.Main.isAmbidextrous_image_referenceSofa hY θ v

/-- **MS.14.** The convex hull of Romik's ambidextrous sofa is `referenceHull Y`. -/
theorem convexHull_referenceSofa (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) :
    convexHull ℝ (referenceSofa Y) = referenceHull Y :=
  AmbidextrousSofa.Main.convexHull_referenceSofa hY

/-- **Uniqueness.** An ambidextrous sofa has area `1 + 4Y² + arctan Y` if and only if a rotation
about the origin followed by a translation maps Romik's ambidextrous sofa onto it. -/
theorem volume_eq_iff (Y : ℝ) (hY : 0 < Y ∧ 4 * Y ^ 3 + 3 * Y = 1) (S : Set (ℝ × ℝ))
    (hS : IsAmbidextrous S) :
    volume.real S = 1 + 4 * Y ^ 2 + Real.arctan Y ↔
      ∃ (θ : ℝ) (v : ℝ × ℝ), S = (fun p => rotate θ p + v) '' referenceSofa Y :=
  AmbidextrousSofa.Main.volume_eq_iff hY S hS

end Ambidextrous
