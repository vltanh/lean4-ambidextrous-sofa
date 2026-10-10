import AmbidextrousSofa.Analysis.CapScoreContinuity

/-!
# Existence of actual spatial cap maxima in a compact box

The domain consists of every nonempty compact convex downward cap contained
in the indicated compact set. Both degenerate and nonsmooth caps are kept.
Its compactness follows from the geometric Hausdorff limit theorem; the
full spatial score is continuous on this domain by its actual moving-window
integrals. The extreme-value theorem therefore supplies a genuine cap.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

def boxedCaps (B : Set Plane) : Set CompactCap := {U | U.carrier ⊆ B}

theorem isCompact_boxedCaps {B : Set Plane} (hB : IsCompact B) :
    IsCompact (boxedCaps B) := by
  apply IsSeqCompact.isCompact
  intro U hU
  obtain ⟨K, hK, hKB, φ, hφ, hlim⟩ := exists_cap_hausdorff_subsequence
    (fun n => (U n).isCap) hB hU
  refine ⟨hK.toCompactCap, hKB, φ, hφ, ?_⟩
  exact CompactCap.tendsto_iff_hausdorff.mpr hlim

theorem continuous_capScore_on_box {B : Set Plane} (hB : IsCompact B) :
    Continuous (fun U : boxedCaps B => capScore U.val.carrier (Real.pi / 2)) := by
  apply continuous_iff_seqContinuous.mpr
  intro U K hlim
  have hc : Tendsto (fun n => (U n).val) atTop (𝓝 K.val) :=
    (continuous_subtype_val.tendsto K).comp hlim
  have hh := CompactCap.tendsto_iff_hausdorff.mp hc
  exact hh.capScore_pi_div_two_tendsto (fun n => (U n).val.isCap) K.val.isCap hB
    (fun n => (U n).property)

theorem continuousOn_capScore_box {B : Set Plane} (hB : IsCompact B) :
    ContinuousOn (fun U : CompactCap => capScore U.carrier (Real.pi / 2)) (boxedCaps B) :=
  continuousOn_iff_continuous_restrict.mpr (continuous_capScore_on_box hB)

/-- A continuous objective has a maximum in the actual boxed cap domain.
This general extreme-value form also applies to finite support penalties. -/
theorem exists_boxed_cap_max {B : Set Plane} (hB : IsCompact B)
    {V : Set Plane} (hV : IsDownwardCap V) (hVB : V ⊆ B)
    {Φ : CompactCap → ℝ} (hΦ : ContinuousOn Φ (boxedCaps B)) :
    ∃ K : CompactCap, K.carrier ⊆ B ∧ ∀ U : CompactCap, U.carrier ⊆ B → Φ U ≤ Φ K := by
  obtain ⟨K, hKB, hmax⟩ := (isCompact_boxedCaps hB).exists_isMaxOn
    ⟨hV.toCompactCap, hVB⟩ hΦ
  exact ⟨K, hKB, fun U hUB => hmax hUB⟩

/-- The whole-angle spatial score reaches its maximum over every nonempty
compact boxed cap domain. No maximizer or regularity field is assumed. -/
theorem exists_capScore_max_of_compact_containment {B : Set Plane} (hB : IsCompact B)
    {V : Set Plane} (hV : IsDownwardCap V) (hVB : V ⊆ B) :
    ∃ K : Set Plane, IsDownwardCap K ∧ K ⊆ B ∧
      ∀ U : Set Plane, IsDownwardCap U → U ⊆ B →
        capScore U (Real.pi / 2) ≤ capScore K (Real.pi / 2) := by
  obtain ⟨K, hKB, hmax⟩ := exists_boxed_cap_max hB hV hVB (continuousOn_capScore_box hB)
  exact ⟨K.carrier, K.isCap, hKB, fun U hU hUB => hmax hU.toCompactCap hUB⟩

end AmbidextrousSofa
