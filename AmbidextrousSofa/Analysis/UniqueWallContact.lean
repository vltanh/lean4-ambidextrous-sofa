module

public import AmbidextrousSofa.Analysis.CapNicheContinuity
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Measurability of unique actual wall contact

The closed quarter of wall angles is compact. For any positive
separation from a proposed angle, the existence of another maximizing
wall is a closed condition after projecting out that compact angle.
Unique contact is the countable intersection of the complements of
these separated-contact sets.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

theorem measurableSet_unique_fullWallClip_contact (U : CompactCap) {X : ℝ → ℝ}
    (hX : Continuous X) :
    MeasurableSet {t | ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip U (X t) s = sweptNiche U.carrier (Real.pi / 2) (X t) → s = t} := by
  -- The times with a maximizing wall at angular distance at least `ε` form a closed set.
  have hclosed (ε : ℝ) : IsClosed (Prod.fst '' {z : ℝ × Icc (0 : ℝ) (Real.pi / 2) |
      ε ≤ |(z.2 : ℝ) - z.1| ∧
        fullWallClip U (X z.1) z.2 = sweptNiche U.carrier (Real.pi / 2) (X z.1)}) :=
    isClosedMap_fst_of_compactSpace _
      ((isClosed_le (α := ℝ) continuous_const (by fun_prop)).inter
        (isClosed_eq (continuous_fullWallClip_on_angles.comp
            (f := fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) => ((U, X z.1), z.2)) (by fun_prop))
          (continuous_capSweptNiche.comp
            (f := fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) => (U, X z.1)) (by fun_prop))))
  convert MeasurableSet.iInter fun n : ℕ => (hclosed (1 / ((n : ℝ) + 1))).measurableSet.compl
  ext t
  simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff, mem_image, not_exists, not_and]
  refine ⟨fun h n z hz hzt => ?_, fun h s hs hc => by_contra fun hne => ?_⟩
  · subst hzt
    exact (Nat.cast_add_one_pos n).not_ge (by simpa [h _ z.2.2 hz.2] using hz.1)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.2 (sub_ne_zero.2 hne))
    exact h n (t, ⟨s, hs⟩) ⟨hn.le, hc⟩ rfl

theorem IsDownwardCap.measurableSet_unique_fullWallClip_contact
    {U : Set Plane} (hU : IsDownwardCap U) {X : ℝ → ℝ} (hX : Continuous X) :
    MeasurableSet {t | ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.toCompactCap (X t) s = sweptNiche U (Real.pi / 2) (X t) → s = t} :=
  AmbidextrousSofa.measurableSet_unique_fullWallClip_contact hU.toCompactCap hX

end AmbidextrousSofa
