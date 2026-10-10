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

def separatedWallContactSet (U : CompactCap) (X : ℝ → ℝ) (ε : ℝ) : Set ℝ :=
  {t | ∃ s ∈ Icc (0 : ℝ) (Real.pi / 2), ε ≤ |s - t| ∧
    fullWallClip U (X t) s = sweptNiche U.carrier (Real.pi / 2) (X t)}

def uniqueWallContactSet (U : CompactCap) (X : ℝ → ℝ) : Set ℝ :=
  {t | ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip U (X t) s = sweptNiche U.carrier (Real.pi / 2) (X t) → s = t}

theorem isClosed_separatedWallContactSet (U : CompactCap) {X : ℝ → ℝ}
    (hX : Continuous X) (ε : ℝ) : IsClosed (separatedWallContactSet U X ε) := by
  let B : Set (ℝ × Icc (0 : ℝ) (Real.pi / 2)) :=
    {z | ε ≤ |(z.2 : ℝ) - z.1| ∧
      fullWallClip U (X z.1) z.2 = sweptNiche U.carrier (Real.pi / 2) (X z.1)}
  have hclip : Continuous (fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) =>
      fullWallClip U (X z.1) z.2) :=
    continuous_fullWallClip_on_angles.comp
      (f := fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) => ((U, X z.1), z.2))
      ((continuous_const.prodMk (hX.comp continuous_fst)).prodMk continuous_snd)
  have hniche : Continuous (fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) =>
      sweptNiche U.carrier (Real.pi / 2) (X z.1)) :=
    continuous_capSweptNiche.comp (f := fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) => (U, X z.1))
      (continuous_const.prodMk (hX.comp continuous_fst))
  have hgap : Continuous (fun z : ℝ × Icc (0 : ℝ) (Real.pi / 2) =>
      |(z.2 : ℝ) - z.1|) :=
    ((continuous_subtype_val.comp continuous_snd).sub continuous_fst).abs
  have hB : IsClosed B :=
    (isClosed_le continuous_const hgap).inter (isClosed_eq hclip hniche)
  have himage : Prod.fst '' B = separatedWallContactSet U X ε := by
    ext t
    constructor
    · rintro ⟨⟨r, s⟩, hz, rfl⟩
      exact ⟨s, s.property, hz⟩
    · rintro ⟨s, hs, hdist, hcontact⟩
      exact ⟨(t, ⟨s, hs⟩), ⟨hdist, hcontact⟩, rfl⟩
  rw [← himage]
  exact isClosedMap_fst_of_compactSpace B hB

theorem uniqueWallContactSet_eq_iInter_compl (U : CompactCap) (X : ℝ → ℝ) :
    uniqueWallContactSet U X =
      ⋂ n : ℕ, (separatedWallContactSet U X (1 / ((n : ℝ) + 1)))ᶜ := by
  ext t
  constructor
  · intro ht
    apply mem_iInter.mpr
    intro n hn
    obtain ⟨s, hs, hdist, hcontact⟩ := hn
    have heq := ht s hs hcontact
    rw [heq, sub_self, abs_zero] at hdist
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    exact not_le_of_gt hpos hdist
  · intro ht s hs hcontact
    by_contra hne
    have hdist : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdist
    exact (mem_iInter.mp ht n) ⟨s, hs, hn.le, hcontact⟩

theorem measurableSet_uniqueWallContactSet (U : CompactCap) {X : ℝ → ℝ}
    (hX : Continuous X) : MeasurableSet (uniqueWallContactSet U X) := by
  rw [uniqueWallContactSet_eq_iInter_compl]
  exact MeasurableSet.iInter (fun n =>
    (isClosed_separatedWallContactSet U hX (1 / ((n : ℝ) + 1))).measurableSet.compl)

theorem measurableSet_unique_fullWallClip_contact (U : CompactCap) {X : ℝ → ℝ}
    (hX : Continuous X) :
    MeasurableSet {t | ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip U (X t) s = sweptNiche U.carrier (Real.pi / 2) (X t) → s = t} :=
  measurableSet_uniqueWallContactSet U hX

theorem IsDownwardCap.measurableSet_unique_fullWallClip_contact
    {U : Set Plane} (hU : IsDownwardCap U) {X : ℝ → ℝ} (hX : Continuous X) :
    MeasurableSet {t | ∀ s ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.toCompactCap (X t) s = sweptNiche U (Real.pi / 2) (X t) → s = t} :=
  AmbidextrousSofa.measurableSet_unique_fullWallClip_contact hU.toCompactCap hX

end AmbidextrousSofa
