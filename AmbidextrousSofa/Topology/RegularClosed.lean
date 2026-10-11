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

/-- Compact regular-closed recovery for a measure positive on nonempty open
sets and finite on compact sets. In particular, this specializes to Lebesgue
measure on the plane. The smaller set is only required to be closed. -/
theorem eq_of_subset_of_measure_eq_of_isCompact_regularClosed
    [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts μ]
    {S F : Set X} (hS : IsClosed S) (hF : IsCompact F)
    (hregular : closure (interior F) = F)
    (hSF : S ⊆ F) (hmeasure : μ S = μ F) : S = F := by
  have hzero : μ (F \ S) = 0 := by
    rw [measure_sdiff hSF hS.nullMeasurableSet (hmeasure ▸ hF.measure_ne_top), hmeasure, tsub_self]
  have hint : interior F \ S = ∅ := (isOpen_interior.sdiff hS).eq_empty_of_measure_zero
    (measure_mono_null (sdiff_subset_sdiff_left interior_subset) hzero)
  exact hSF.antisymm (hregular ▸ closure_minimal (sdiff_eq_empty.mp hint) hS)

end AmbidextrousSofa
