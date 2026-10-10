module

public import Mathlib

@[expose] public section

/-!
# Recovery of a regular-closed set from equal measure

A closed set contains the closure of the interior of any set that it contains
up to a null difference, provided the measure is positive on nonempty open
sets. For a regular-closed larger set, finite equal measure therefore upgrades
containment to literal set equality.

The regular-closed property is stated explicitly as
`closure (interior F) = F`. No regularity of the smaller set beyond closedness
is needed.
-/

open Set MeasureTheory

namespace AmbidextrousSofa

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
variable (μ : Measure X) [μ.IsOpenPosMeasure]

/-- If `F \ S` is null and `S` is closed, then `S` contains the closure of
the interior of `F`. No measurability or finiteness assumption on `F` is needed. -/
theorem closure_interior_subset_of_measure_sdiff_eq_zero
    {S F : Set X} (hS : IsClosed S) (hzero : μ (F \ S) = 0) :
    closure (interior F) ⊆ S := by
  have hzero' : μ (interior F \ S) = 0 :=
    measure_mono_null (fun _ hx => ⟨interior_subset hx.1, hx.2⟩) hzero
  have hempty : interior F \ S = ∅ :=
    (isOpen_interior.sdiff hS).eq_empty_of_measure_zero hzero'
  exact closure_minimal (Set.sdiff_eq_empty.mp hempty) hS

/-- A closed subset of a regular-closed set of finite measure equals that set
if their measures agree. Finiteness is essential: equality of two infinite
measures alone gives no null-difference conclusion. -/
theorem eq_of_subset_of_measure_eq_of_regularClosed
    [OpensMeasurableSpace X] {S F : Set X}
    (hS : IsClosed S) (hregular : closure (interior F) = F)
    (hSF : S ⊆ F) (hfinite : μ F ≠ ⊤) (hmeasure : μ S = μ F) :
    S = F := by
  have hSfinite : μ S ≠ ⊤ := by
    rw [hmeasure]
    exact hfinite
  have hzero : μ (F \ S) = 0 := by
    rw [measure_sdiff hSF hS.nullMeasurableSet hSfinite, hmeasure, tsub_self]
  refine Set.Subset.antisymm hSF ?_
  have hclosure := closure_interior_subset_of_measure_sdiff_eq_zero μ hS hzero
  rwa [hregular] at hclosure

/-- Compact regular-closed recovery for a measure positive on nonempty open
sets and finite on compact sets. In particular, this specializes to Lebesgue
measure on the plane. The smaller set is only required to be closed. -/
theorem eq_of_subset_of_measure_eq_of_isCompact_regularClosed
    [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    {S F : Set X} (hS : IsClosed S) (hF : IsCompact F)
    (hregular : closure (interior F) = F)
    (hSF : S ⊆ F) (hmeasure : μ S = μ F) : S = F := by
  exact eq_of_subset_of_measure_eq_of_regularClosed μ hS hregular hSF
    (hF.measure_ne_top (μ := μ)) hmeasure

end AmbidextrousSofa
