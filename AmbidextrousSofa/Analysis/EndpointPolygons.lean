module

public import AmbidextrousSofa.Analysis.EndpointTrimming
public import AmbidextrousSofa.Analysis.PolygonEnvelope

@[expose] public section

/-!
# Inward endpoint operations preserve the finite polygon class

A cut only changes the two displayed endpoint walls. Horizontal erosion
tightens each displayed upper wall by the positive horizontal component
of its normal. These are exact identities of actual sets. The new displayed
heights need not be attained supports; replacing every height by its actual
support gives the same polygon, including redundant inequalities.
-/

noncomputable section

open Set

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

/-- Displayed erosion heights describe the exact intersection, even when
they are no longer attained as support values. -/
theorem rightErosion_upperPolygon {l r ε : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hε : 0 ≤ ε) :
    rightErosion (upperPolygon l r normal height) ε =
      upperPolygon l (r - ε) normal (fun i => height i - ε * max (normal i).1 0) := by
  ext p
  simp only [rightErosion, mem_ofPred_eq, mem_upperPolygon_iff, mem_Icc, coordDot]
  constructor
  · rintro ⟨⟨⟨hl, -⟩, hy, h⟩, ⟨-, hr⟩, -, h'⟩
    refine ⟨⟨hl, by linarith⟩, hy, fun i => ?_⟩
    rcases max_cases (normal i).1 0 with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith [h i, h' i]
  · rintro ⟨⟨hl, hr⟩, hy, h⟩
    refine ⟨⟨⟨hl, by linarith⟩, hy, fun i => ?_⟩, ⟨by linarith, by linarith⟩, hy, fun i => ?_⟩
    · linarith [h i, mul_nonneg hε (le_max_right (normal i).1 0)]
    · linarith [h i, mul_le_mul_of_nonneg_left (le_max_left (normal i).1 0) hε]

theorem leftErosion_upperPolygon {l r ε : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hε : 0 ≤ ε) :
    leftErosion (upperPolygon l r normal height) ε =
      upperPolygon (l + ε) r normal (fun i => height i - ε * max (-(normal i).1) 0) := by
  ext p
  simp only [leftErosion, mem_ofPred_eq, mem_upperPolygon_iff, mem_Icc, coordDot]
  constructor
  · rintro ⟨⟨⟨-, hr⟩, hy, h⟩, ⟨hl, -⟩, -, h'⟩
    refine ⟨⟨by linarith, hr⟩, hy, fun i => ?_⟩
    rcases max_cases (-(normal i).1) 0 with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm] <;> linarith [h i, h' i]
  · rintro ⟨⟨hl, hr⟩, hy, h⟩
    refine ⟨⟨⟨by linarith, hr⟩, hy, fun i => ?_⟩, ⟨by linarith, by linarith⟩, hy, fun i => ?_⟩
    · linarith [h i, mul_nonneg hε (le_max_right (-(normal i).1) 0)]
    · linarith [h i, mul_le_mul_of_nonneg_left (le_max_left (-(normal i).1) 0) hε]

end FinitePolygon

end AmbidextrousSofa
