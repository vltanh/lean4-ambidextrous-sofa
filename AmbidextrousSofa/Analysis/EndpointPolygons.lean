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

theorem coordDot_horizontal_add (p v : Plane) (ε : ℝ) :
    coordDot (p.1 + ε, p.2) v = coordDot p v + ε * v.1 := by
  unfold coordDot
  ring

theorem coordDot_horizontal_sub (p v : Plane) (ε : ℝ) :
    coordDot (p.1 - ε, p.2) v = coordDot p v + ε * (-v.1) := by
  unfold coordDot
  ring

/-- Displayed erosion heights describe the exact intersection, even when
they are no longer attained as support values. -/
theorem rightErosion_upperPolygon {l r ε : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hε : 0 ≤ ε) :
    rightErosion (upperPolygon l r normal height) ε =
      upperPolygon l (r - ε) normal (fun i => height i - ε * max (normal i).1 0) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp.1
    obtain ⟨hxshift, _, hshift⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp.2
    apply (mem_upperPolygon_iff _ _ _ _ _).mpr
    refine ⟨⟨hx.1, by have h := hxshift.2; change p.1 + ε ≤ r at h; linarith⟩, hy, ?_⟩
    intro i
    by_cases hi : 0 ≤ (normal i).1
    · rw [max_eq_left hi]
      have h := hshift i
      rw [coordDot_horizontal_add] at h
      linarith
    · rw [max_eq_right (le_of_not_ge hi), mul_zero, sub_zero]
      exact hhalf i
  · intro hp
    obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
    have hbase : ∀ i, coordDot p (normal i) ≤ height i := by
      intro i
      have h := hhalf i
      have hnonneg := mul_nonneg hε (le_max_right (normal i).1 0)
      linarith
    refine ⟨(mem_upperPolygon_iff _ _ _ _ _).mpr
      ⟨⟨hx.1, by linarith [hx.2]⟩, hy, hbase⟩,
      (mem_upperPolygon_iff _ _ _ _ _).mpr ?_⟩
    refine ⟨⟨by change l ≤ p.1 + ε; linarith [hx.1],
      by change p.1 + ε ≤ r; linarith [hx.2]⟩, hy, ?_⟩
    intro i
    rw [coordDot_horizontal_add]
    have h := hhalf i
    have hle := mul_le_mul_of_nonneg_left (le_max_left (normal i).1 0) hε
    linarith

theorem leftErosion_upperPolygon {l r ε : ℝ} (normal : ι → Plane) (height : ι → ℝ)
    (hε : 0 ≤ ε) :
    leftErosion (upperPolygon l r normal height) ε =
      upperPolygon (l + ε) r normal (fun i => height i - ε * max (-(normal i).1) 0) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp.1
    obtain ⟨hxshift, _, hshift⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp.2
    apply (mem_upperPolygon_iff _ _ _ _ _).mpr
    refine ⟨⟨by have h := hxshift.1; change l ≤ p.1 - ε at h; linarith, hx.2⟩, hy, ?_⟩
    intro i
    by_cases hi : 0 ≤ -(normal i).1
    · rw [max_eq_left hi]
      have h := hshift i
      rw [coordDot_horizontal_sub] at h
      linarith
    · rw [max_eq_right (le_of_not_ge hi), mul_zero, sub_zero]
      exact hhalf i
  · intro hp
    obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
    have hbase : ∀ i, coordDot p (normal i) ≤ height i := by
      intro i
      have h := hhalf i
      have hnonneg := mul_nonneg hε (le_max_right (-(normal i).1) 0)
      linarith
    refine ⟨(mem_upperPolygon_iff _ _ _ _ _).mpr
      ⟨⟨by linarith [hx.1], hx.2⟩, hy, hbase⟩,
      (mem_upperPolygon_iff _ _ _ _ _).mpr ?_⟩
    refine ⟨⟨by change l ≤ p.1 - ε; linarith [hx.1],
      by change p.1 - ε ≤ r; linarith [hx.2]⟩, hy, ?_⟩
    intro i
    rw [coordDot_horizontal_sub]
    have h := hhalf i
    have hle := mul_le_mul_of_nonneg_left (le_max_left (-(normal i).1) 0) hε
    linarith

end FinitePolygon

end AmbidextrousSofa
