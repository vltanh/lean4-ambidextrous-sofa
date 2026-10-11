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
  simp only [upperPolygon, mem_inter_iff, mem_prod, mem_iInter, mem_ofPred_eq, and_assoc]

theorem isCompact_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) :
    IsCompact (upperPolygon l r normal height) :=
  (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_iInter (fun i => isClosed_le (continuous_coordDot_right (normal i)) continuous_const))

theorem isDownwardCap_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hlr : l ≤ r) (hnormal : ∀ i, 0 ≤ (normal i).2)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    IsDownwardCap (upperPolygon l r normal height) := by
  refine ⟨⟨(l, 0), (mem_upperPolygon_iff _ _ _ _ _).2
      ⟨⟨le_rfl, hlr⟩, ⟨le_rfl, zero_le_one⟩, hbaseline l ⟨le_rfl, hlr⟩⟩⟩,
    isCompact_upperPolygon _ _ _ _, ((convex_Icc l r).prod (convex_Icc 0 1)).inter
      (convex_iInter fun i => convex_coordDot_halfspace (normal i) (height i)),
    fun p hp => ((mem_upperPolygon_iff _ _ _ _ _).1 hp).2.1, fun p hp y hy0 hyp => ?_⟩
  obtain ⟨hpx, hpy, hphalf⟩ := (mem_upperPolygon_iff _ _ _ _ _).1 hp
  exact (mem_upperPolygon_iff _ _ _ _ _).2 ⟨hpx, ⟨hy0, hyp.trans hpy.2⟩, fun i =>
    (add_le_add_right (mul_le_mul_of_nonneg_right hyp (hnormal i)) _).trans (hphalf i)⟩

theorem horizontalProjection_upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ)
    (hbaseline : ∀ x ∈ Icc l r, ∀ i, coordDot (x, 0) (normal i) ≤ height i) :
    horizontalProjection (upperPolygon l r normal height) = Icc l r := by
  refine Subset.antisymm ?_ fun x hx => ⟨(x, 0), (mem_upperPolygon_iff _ _ _ _ _).2
    ⟨hx, ⟨le_rfl, zero_le_one⟩, hbaseline x hx⟩, rfl⟩
  rintro x ⟨p, hp, rfl⟩
  exact ((mem_upperPolygon_iff _ _ _ _ _).1 hp).1

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
  have hev : ∀ᶠ ε : ℝ in 𝓝 0, (p + ε • normal j).1 ∈ Ioo l r ∧
      (p + ε • normal j).2 ∈ Ioo (0 : ℝ) 1 ∧
      ∀ i, i ≠ j → coordDot (p + ε • normal j) (normal i) < height i :=
    (hcont.fst.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by simpa))).and
      ((hcont.snd.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (by simpa))).and
        (eventually_all.2 fun i => eventually_imp_distrib_left.2 fun hij =>
          ((continuous_coordDot_right _).comp hcont).continuousAt.eventually_lt
            continuousAt_const (by simpa using hstrict i hij)))
  obtain ⟨δ, hδ, hball⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 (nhdsWithin_le_nhds hev)
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  obtain ⟨hxε, hyε, hotherε⟩ := hball hε
  have hfaceε : coordDot (p + ε • normal j) (normal j) = height j + ε := by
    rw [coordDot_add_left, coordDot_smul_left, hface, hunit, mul_one]
  refine ⟨(mem_upperPolygon_iff _ _ _ _ _).2
    ⟨Ioo_subset_Icc_self hxε, Ioo_subset_Icc_self hyε, fun i => ?_⟩, hfaceε⟩
  rcases eq_or_ne i j with rfl | hij
  · rw [Function.update_self, hfaceε]
  · rw [Function.update_of_ne hij]
    exact (hotherε i hij).le

/-- A nonparallel normal takes distinct values on two distinct points of
one positive-slope support line. -/
theorem coordDot_ne_on_face {p q u v : Plane} (hpq : p ≠ q) (huy : u.2 ≠ 0)
    (hface : coordDot p u = coordDot q u)
    (hdet : u.1 * v.2 - u.2 * v.1 ≠ 0) : coordDot p v ≠ coordDot q v := by
  intro hother
  unfold coordDot at hface hother
  have hx : p.1 = q.1 := mul_right_cancel₀ hdet (by linear_combination v.2 * hface - u.2 * hother)
  exact hpq (Prod.ext hx (mul_right_cancel₀ huy (by linear_combination hface - u.1 * hx)))

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
  obtain ⟨⟨hpl, hpr⟩, ⟨hp0, hp1⟩, hph⟩ := (mem_upperPolygon_iff _ _ _ _ _).1 hp
  obtain ⟨⟨hql, hqr⟩, ⟨hq0, hq1⟩, hqh⟩ := (mem_upperPolygon_iff _ _ _ _ _).1 hq
  -- the two face points differ in every direction not parallel to the face
  have hne (v : Plane) (hv : (normal j).1 * v.2 - (normal j).2 * v.1 ≠ 0) :=
    (coordDot_ne_on_face hpq hny (hpface.trans hqface.symm) hv).lt_or_gt
  simp only [coordDot_add_left, coordDot_smul_left, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, mem_Ioo]
  refine ⟨?_, ?_, by rw [hpface, hqface]; ring, fun i hij => ?_⟩
  · rcases hne (1, 0) (by simpa using hny) with h | h <;> simp only [coordDot] at h <;>
      constructor <;> linarith
  · rcases hne (0, 1) (by simpa using hnx) with h | h <;> simp only [coordDot] at h <;>
      constructor <;> linarith
  · rcases hne _ (hdet i hij) with h | h <;> linarith [hph i, hqh i]

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
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  obtain ⟨hmε, hmdot⟩ := hattain ε hε
  have hle : height ≤ Function.update height j (height j + ε) :=
    le_update_self_iff.2 (le_add_of_nonneg_right hε.1)
  have hbaseline' := fun x hx i => (hbaseline x hx i).trans (hle i)
  have hK := isCompact_upperPolygon l r normal (Function.update height j (height j + ε))
  have hmem (z) (hz : z ∈ upperPolygon l r normal (Function.update height j (height j + ε))) :=
    ((mem_upperPolygon_iff _ _ _ _ _).1 hz).2.2
  refine ⟨isDownwardCap_upperPolygon _ _ _ _ hlr hnormal hbaseline',
    horizontalProjection_upperPolygon _ _ _ _ hbaseline', fun i => ?_⟩
  rcases eq_or_ne i j with rfl | hij
  · exact support_eq_of_mem hK (fun z hz => hmem z hz i) hmε (by rw [hmdot, Function.update_self])
  rw [Function.update_of_ne hij]
  refine le_antisymm (support_le_of_forall ⟨_, hmε⟩ fun z hz => ?_) ?_
  · simpa [hij] using hmem z hz i
  rw [← hexact i]
  refine support_mono (fun z hz => ?_) ⟨p, hp⟩ hK _
  obtain ⟨hzx, hzy, hzh⟩ := (mem_upperPolygon_iff _ _ _ _ _).1 hz
  exact (mem_upperPolygon_iff _ _ _ _ _).2 ⟨hzx, hzy, fun k => (hzh k).trans (hle k)⟩

end FinitePolygon

end AmbidextrousSofa
