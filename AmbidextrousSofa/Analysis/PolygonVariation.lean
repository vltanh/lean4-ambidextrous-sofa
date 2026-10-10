module

public import AmbidextrousSofa.Analysis.FiniteVariation

@[expose] public section

/-!
# Actual finite polygon support variations

`upperPolygon` is a bounded intersection of the unit strip, two actual
horizontal endpoint walls, and finitely many upper supporting halfplanes.
The outward variation changes one halfplane parameter. Every unchanged
support remains exact, while a strict point in the moved face gives an
attaining point for the increased support. Such a strict point is derived
from any two distinct points of the face when the other normals are
nonparallel; it is not a separate variational assumption.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace FinitePolygon

variable {ι : Type*}

/-- The actual set cut out by a finite upper support system and the fixed box. -/
def upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) : Set Plane :=
  (Icc l r ×ˢ Icc (0 : ℝ) 1) ∩ ⋂ i, {p | coordDot p (normal i) ≤ height i}

theorem mem_upperPolygon_iff (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) (p : Plane) :
    p ∈ upperPolygon l r normal height ↔
      p.1 ∈ Icc l r ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ ∀ i, coordDot p (normal i) ≤ height i := by
  simp only [upperPolygon, mem_inter_iff, mem_prod, mem_iInter, mem_setOf_eq]
  tauto

theorem isCompact_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) :
    IsCompact (upperPolygon l r normal height) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_iInter (fun i => isClosed_le (continuous_coordDot_right (normal i)) continuous_const))

theorem convex_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) :
    Convex ℝ (upperPolygon l r normal height) :=
  ((convex_Icc l r).prod (convex_Icc (0 : ℝ) 1)).inter
    (convex_iInter (fun i => convex_coordDot_halfspace (normal i) (height i)))

theorem isDownwardCap_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hlr : l ≤ r) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    IsDownwardCap (upperPolygon l r normal height) := by
  refine ⟨?_, isCompact_upperPolygon _ _ _ _, convex_upperPolygon _ _ _ _, ?_, ?_⟩
  · refine ⟨(l, 0), (mem_upperPolygon_iff _ _ _ _ _).mpr ?_⟩
    exact ⟨⟨le_rfl, hlr⟩, ⟨le_rfl, by norm_num⟩, hbaseline l ⟨le_rfl, hlr⟩⟩
  · intro p hp
    exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.1
  · intro p hp y hy0 hyp
    obtain ⟨hpx, hpy, hphalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
    apply (mem_upperPolygon_iff _ _ _ _ _).mpr
    refine ⟨hpx, ⟨hy0, hyp.trans hpy.2⟩, ?_⟩
    intro i
    calc
      coordDot (p.1, y) (normal i) ≤ coordDot p (normal i) := by
        unfold coordDot
        exact add_le_add_right (mul_le_mul_of_nonneg_right hyp (hnormal i)) _
      _ ≤ height i := hphalf i

theorem horizontalProjection_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalProjection (upperPolygon l r normal height) = Icc l r := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact ((mem_upperPolygon_iff _ _ _ _ _).mp hp).1
  · intro x hx
    refine ⟨(x, 0), (mem_upperPolygon_iff _ _ _ _ _).mpr ?_, rfl⟩
    exact ⟨hx, ⟨le_rfl, by norm_num⟩, hbaseline x hx⟩

theorem upperPolygon_mono {l r : ℝ} {normal : ι → Plane} {height height' : ι → ℝ}
    (hheight : ∀ i, height i ≤ height' i) :
    upperPolygon l r normal height ⊆ upperPolygon l r normal height' := by
  intro p hp
  obtain ⟨hx, hy, hhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
  exact (mem_upperPolygon_iff _ _ _ _ _).mpr ⟨hx, hy, fun i => (hhalf i).trans (hheight i)⟩

theorem upperPolygon_subset_outward [DecidableEq ι] (l r : ℝ)
    (normal : ι → Plane) (height : ι → ℝ) (j : ι) {ε : ℝ} (hε : 0 ≤ ε) :
    upperPolygon l r normal height ⊆
      upperPolygon l r normal (Function.update height j (height j + ε)) := by
  apply upperPolygon_mono
  intro i
  by_cases hij : i = j
  · subst i
    simp only [Function.update_self]
    linarith
  · simp only [Function.update_of_ne hij, le_refl]

/-- Retaining an old attaining point and its original halfplane pins every
unchanged actual support, whether or not another constraint is redundant. -/
theorem support_outward_unchanged [DecidableEq ι] {l r : ℝ}
    {normal : ι → Plane} {height : ι → ℝ} (j : ι) {ε : ℝ} (hε : 0 ≤ ε)
    (hne : (upperPolygon l r normal height).Nonempty)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    {i : ι} (hij : i ≠ j) :
    support (upperPolygon l r normal (Function.update height j (height j + ε))) (normal i) =
      height i := by
  have hsub := upperPolygon_subset_outward l r normal height j hε
  apply le_antisymm
  · apply support_le_of_forall (hne.mono hsub)
    intro p hp
    have hhalf := ((mem_upperPolygon_iff _ _ _ _ _).mp hp).2.2 i
    simpa only [Function.update_of_ne hij] using hhalf
  · rw [← hexact i]
    exact support_mono hsub hne (isCompact_upperPolygon _ _ _ _) _

/-- A strict point of the moved face remains feasible after a sufficiently
small displacement in its unit normal. It realizes the increased support. -/
theorem exists_outward_attaining_point [Fintype ι] [DecidableEq ι]
    {l r : ℝ} {normal : ι → Plane} {height : ι → ℝ} (j : ι) {p : Plane}
    (hpx : p.1 ∈ Ioo l r) (hpy : p.2 ∈ Ioo (0 : ℝ) 1)
    (hface : coordDot p (normal j) = height j)
    (hstrict : ∀ i, i ≠ j → coordDot p (normal i) < height i)
    (hunit : coordDot (normal j) (normal j) = 1) :
    ∃ δ > 0, ∀ ε ∈ Ico (0 : ℝ) δ,
      p + ε • normal j ∈ upperPolygon l r normal (Function.update height j (height j + ε)) ∧
        coordDot (p + ε • normal j) (normal j) = height j + ε := by
  have hcont : Continuous (fun ε : ℝ => p + ε • normal j) := by fun_prop
  have hx : ∀ᶠ ε : ℝ in 𝓝 0, (p + ε • normal j).1 ∈ Ioo l r :=
    (continuous_fst.comp hcont).continuousAt (isOpen_Ioo.mem_nhds (by simpa using hpx))
  have hy : ∀ᶠ ε : ℝ in 𝓝 0, (p + ε • normal j).2 ∈ Ioo (0 : ℝ) 1 :=
    (continuous_snd.comp hcont).continuousAt (isOpen_Ioo.mem_nhds (by simpa using hpy))
  have hother : ∀ i, ∀ᶠ ε : ℝ in 𝓝 0,
      i ≠ j → coordDot (p + ε • normal j) (normal i) < height i := by
    intro i
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    · have hvalue : coordDot (p + (0 : ℝ) • normal j) (normal i) < height i := by
        simpa only [zero_smul, add_zero] using hstrict i hij
      have h : ∀ᶠ ε : ℝ in 𝓝 0, coordDot (p + ε • normal j) (normal i) < height i :=
        ((continuous_coordDot_right (normal i)).comp hcont).continuousAt
          (Iio_mem_nhds hvalue)
      exact h.mono (fun _ h _ => h)
  have hnear := hx.and (hy.and (eventually_all.mpr hother))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hε.1] using hε.2
  obtain ⟨hxε, hyε, hotherε⟩ := hball hεball
  have hfaceε : coordDot (p + ε • normal j) (normal j) = height j + ε := by
    rw [coordDot_add_left, coordDot_smul_left, hface, hunit]
    ring
  refine ⟨(mem_upperPolygon_iff _ _ _ _ _).mpr
    ⟨⟨hxε.1.le, hxε.2.le⟩, ⟨hyε.1.le, hyε.2.le⟩, ?_⟩, hfaceε⟩
  intro i
  by_cases hij : i = j
  · subst i
    rw [Function.update_self, hfaceε]
  · rw [Function.update_of_ne hij]
    exact (hotherε i hij).le

/-- A nonparallel normal takes distinct values on two distinct points of
one positive-slope support line. -/
theorem coordDot_ne_on_face {p q u v : Plane} (hpq : p ≠ q) (huy : u.2 ≠ 0)
    (hface : coordDot p u = coordDot q u)
    (hdet : u.1 * v.2 - u.2 * v.1 ≠ 0) : coordDot p v ≠ coordDot q v := by
  intro hother
  have hdx : (p.1 - q.1) * (u.1 * v.2 - u.2 * v.1) = 0 := by
    unfold coordDot at hface hother
    linear_combination v.2 * hface - u.2 * hother
  have hx : p.1 = q.1 := sub_eq_zero.mp ((mul_eq_zero.mp hdx).resolve_right hdet)
  have hdy : (p.2 - q.2) * u.2 = 0 := by
    unfold coordDot at hface
    rw [hx] at hface
    nlinarith
  have hy : p.2 = q.2 := sub_eq_zero.mp ((mul_eq_zero.mp hdy).resolve_right huy)
  exact hpq (Prod.ext hx hy)

/-- Two distinct points of a non-axis, non-top facet supply a point strictly
inside the fixed box and strictly below every other nonparallel wall. -/
theorem midpoint_strict_face {l r : ℝ} {normal : ι → Plane} {height : ι → ℝ}
    (j : ι) {p q : Plane}
    (hp : p ∈ upperPolygon l r normal height) (hq : q ∈ upperPolygon l r normal height)
    (hpq : p ≠ q) (hpface : coordDot p (normal j) = height j)
    (hqface : coordDot q (normal j) = height j)
    (hnx : (normal j).1 ≠ 0) (hny : (normal j).2 ≠ 0)
    (hdet : ∀ i, i ≠ j →
      (normal j).1 * (normal i).2 - (normal j).2 * (normal i).1 ≠ 0) :
    ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q).1 ∈ Ioo l r ∧
      ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q).2 ∈ Ioo (0 : ℝ) 1 ∧
      coordDot ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) (normal j) = height j ∧
      ∀ i, i ≠ j →
        coordDot ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) (normal i) < height i := by
  obtain ⟨hpx, hpy, hphalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hp
  obtain ⟨hqx, hqy, hqhalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).mp hq
  have hface : coordDot p (normal j) = coordDot q (normal j) := hpface.trans hqface.symm
  have hxne : p.1 ≠ q.1 := by
    intro hx
    have hmul : (p.2 - q.2) * (normal j).2 = 0 := by
      unfold coordDot at hface
      rw [hx] at hface
      nlinarith
    exact hpq (Prod.ext hx (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hny)))
  have hyne : p.2 ≠ q.2 := by
    intro hy
    have hmul : (p.1 - q.1) * (normal j).1 = 0 := by
      unfold coordDot at hface
      rw [hy] at hface
      nlinarith
    exact hpq (Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hnx)) hy)
  have hxmid : ((p.1 + q.1) / 2) ∈ Ioo l r := by
    rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
    · constructor <;> linarith [hpx.1, hpx.2, hqx.1, hqx.2]
    · exact (hxne heq).elim
    · constructor <;> linarith [hpx.1, hpx.2, hqx.1, hqx.2]
  have hymid : ((p.2 + q.2) / 2) ∈ Ioo (0 : ℝ) 1 := by
    rcases lt_trichotomy p.2 q.2 with hlt | heq | hgt
    · constructor <;> linarith [hpy.1, hpy.2, hqy.1, hqy.2]
    · exact (hyne heq).elim
    · constructor <;> linarith [hpy.1, hpy.2, hqy.1, hqy.2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hxmid using 1 <;> simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul] <;> ring
  · convert hymid using 1 <;> simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] <;> ring
  · rw [coordDot_add_left, coordDot_smul_left, coordDot_smul_left, hpface, hqface]
    ring
  · intro i hij
    have hne := coordDot_ne_on_face hpq hny hface (hdet i hij)
    rw [coordDot_add_left, coordDot_smul_left, coordDot_smul_left]
    rcases lt_trichotomy (coordDot p (normal i)) (coordDot q (normal i)) with hlt | heq | hgt
    · linarith [hphalf i, hqhalf i]
    · exact (hne heq).elim
    · linarith [hphalf i, hqhalf i]

/-- Actual outward support realization for a nontrivial floating facet.
The strict interior face point is constructed from the two displayed
attaining points. All untouched supports and the projection remain fixed. -/
theorem exists_outward_support_variation [Fintype ι] [DecidableEq ι]
    {l r : ℝ} {normal : ι → Plane} {height : ι → ℝ} (j : ι)
    (hlr : l ≤ r) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i)
    (hexact : ∀ i, support (upperPolygon l r normal height) (normal i) = height i)
    {p q : Plane} (hp : p ∈ upperPolygon l r normal height)
    (hq : q ∈ upperPolygon l r normal height) (hpq : p ≠ q)
    (hpface : coordDot p (normal j) = height j) (hqface : coordDot q (normal j) = height j)
    (hnx : (normal j).1 ≠ 0) (hny : (normal j).2 ≠ 0)
    (hdet : ∀ i, i ≠ j →
      (normal j).1 * (normal i).2 - (normal j).2 * (normal i).1 ≠ 0)
    (hunit : coordDot (normal j) (normal j) = 1) :
    ∃ δ > 0, ∀ ε ∈ Ico (0 : ℝ) δ,
      IsDownwardCap (upperPolygon l r normal (Function.update height j (height j + ε))) ∧
      horizontalProjection (upperPolygon l r normal (Function.update height j (height j + ε))) =
        Icc l r ∧
      ∀ i, support (upperPolygon l r normal (Function.update height j (height j + ε))) (normal i) =
        Function.update height j (height j + ε) i := by
  obtain ⟨hmx, hmy, hmface, hmstrict⟩ := midpoint_strict_face j hp hq hpq hpface hqface hnx hny hdet
  obtain ⟨δ, hδ, hattain⟩ := exists_outward_attaining_point j hmx hmy hmface hmstrict hunit
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hbaseline' : ∀ x ∈ Icc l r, ∀ i,
      coordDot (x, 0) (normal i) ≤ Function.update height j (height j + ε) i := by
    intro x hx i
    by_cases hij : i = j
    · subst i
      simp only [Function.update_self]
      exact (hbaseline x hx j).trans (by linarith [hε.1])
    · simpa only [Function.update_of_ne hij] using hbaseline x hx i
  refine ⟨isDownwardCap_upperPolygon _ _ _ _ hlr hnormal hbaseline',
    horizontalProjection_upperPolygon _ _ _ _ hbaseline', ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    rw [Function.update_self]
    obtain ⟨hmε, hmdot⟩ := hattain ε hε
    apply support_eq_of_mem (isCompact_upperPolygon _ _ _ _) ?_ hmε hmdot
    intro z hz
    simpa only [Function.update_self] using ((mem_upperPolygon_iff _ _ _ _ _).mp hz).2.2 j
  · rw [Function.update_of_ne hij]
    exact support_outward_unchanged j hε.1 ⟨p, hp⟩ hexact hij

end FinitePolygon

end AmbidextrousSofa
