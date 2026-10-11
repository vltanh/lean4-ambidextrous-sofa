module

public import AmbidextrousSofa.Analysis.RoofContinuity
public import AmbidextrousSofa.Geometry.Support

@[expose] public section

/-!
# Hausdorff compactness of the actual cap domain

Nonempty compact subsets of a fixed compact box have Hausdorff-convergent
subsequences. Convexity and downward closure both pass to that limit. Zero
width and zero height are retained, so the compactness statement does not
discard degenerate limits. Support values and projection endpoints converge
as consequences of an explicit distance estimate.

The hyperspace argument follows Mathlib's `NonemptyCompacts` compactness
machinery, also used by `mpc_blaschke` in the moving-sofa source project.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

def CapHausdorffTendsto (U : ℕ → Set Plane) (K : Set Plane) : Prop :=
  Tendsto (fun n => Metric.hausdorffDist (U n) K) atTop (𝓝 0)

theorem hausdorffEDist_ne_top_of_compact {K L : Set Plane}
    (hK : IsCompact K) (hKne : K.Nonempty) (hL : IsCompact L) (hLne : L.Nonempty) :
    Metric.hausdorffEDist K L ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hKne hLne hK.isBounded hL.isBounded

/-- Compactness realizes a nearest point, so no unspecified error term is
needed when comparing support values or taking limits of cap points. -/
theorem exists_mem_dist_le_hausdorff {K L : Set Plane}
    (hK : IsCompact K) (hKne : K.Nonempty) (hL : IsCompact L) (hLne : L.Nonempty)
    {p : Plane} (hp : p ∈ K) :
    ∃ q ∈ L, dist p q ≤ Metric.hausdorffDist K L := by
  obtain ⟨q, hq, hdist⟩ := hL.exists_infDist_eq_dist hLne p
  exact ⟨q, hq, hdist ▸ Metric.infDist_le_hausdorffDist_of_mem hp
    (hausdorffEDist_ne_top_of_compact hK hKne hL hLne)⟩

theorem CapHausdorffTendsto.exists_points_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsCompact (U n)) (hUne : ∀ n, (U n).Nonempty)
    (hK : IsCompact K) (hKne : K.Nonempty) {p : Plane} (hp : p ∈ K) :
    ∃ q : ℕ → Plane, (∀ n, q n ∈ U n) ∧ Tendsto q atTop (𝓝 p) := by
  choose q hq hdist using fun n => exists_mem_dist_le_hausdorff hK hKne (hU n) (hUne n) hp
  exact ⟨q, hq, tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero (fun _ => dist_nonneg)
    (fun n => by simpa only [dist_comm, Metric.hausdorffDist_comm] using hdist n) h)⟩

theorem CapHausdorffTendsto.mem_of_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsCompact (U n)) (hUne : ∀ n, (U n).Nonempty)
    (hK : IsCompact K) (hKne : K.Nonempty)
    {q : ℕ → Plane} {p : Plane} (hq : ∀ n, q n ∈ U n) (hp : Tendsto q atTop (𝓝 p)) :
    p ∈ K := by
  choose k hk hdist using fun n => exists_mem_dist_le_hausdorff (hU n) (hUne n) hK hKne (hq n)
  exact hK.isClosed.mem_of_tendsto (hp.congr_dist (squeeze_zero (fun _ => dist_nonneg) hdist h))
    (Eventually.of_forall hk)

/-- Blaschke selection specialized to the full downward-cap domain. The
limiting cap remains in the same compact box, including all degeneracies. -/
theorem exists_cap_hausdorff_subsequence {U : ℕ → Set Plane}
    (hU : ∀ n, IsDownwardCap (U n)) {B : Set Plane}
    (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    ∃ K : Set Plane, IsDownwardCap K ∧ K ⊆ B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CapHausdorffTendsto (U ∘ φ) K := by
  let C : ℕ → NonemptyCompacts Plane := fun n => ⟨⟨U n, (hU n).isCompact⟩, (hU n).nonempty⟩
  have hcompact : IsCompact (closure {D : NonemptyCompacts Plane | (D : Set Plane) ⊆ B}) :=
    (NonemptyCompacts.totallyBounded_subsets_of_totallyBounded
      hB.totallyBounded).closure.isCompact_of_isComplete isClosed_closure.isComplete
  obtain ⟨K, -, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq fun n => subset_closure (show C n ∈ _ from hsub n)
  have hd : CapHausdorffTendsto (U ∘ φ) K := by
    have h := tendsto_iff_dist_tendsto_zero.mp hlim
    simp only [NonemptyCompacts.dist_eq, C] at h
    exact h
  have hc n := (hU (φ n)).isCompact
  have hn n := (hU (φ n)).nonempty
  have hpoints {p} (hp : p ∈ (K : Set Plane)) :=
    hd.exists_points_tendsto hc hn K.isCompact K.nonempty hp
  have hclosed {B'} (hB' : IsClosed B') (h : ∀ n, U n ⊆ B') : (K : Set Plane) ⊆ B' :=
    fun p hp => by
      obtain ⟨q, hq, hlim⟩ := hpoints hp
      exact hB'.mem_of_tendsto hlim (Eventually.of_forall fun n => h _ (hq n))
  refine ⟨K, ⟨K.nonempty, K.isCompact, fun p hp q hq a b ha hb hab => ?_,
    hclosed (isClosed_Icc.preimage continuous_snd) fun n => (hU n).inStrip,
    fun p hp y hy0 hyp => ?_⟩, hclosed hB.isClosed hsub, φ, hφ, hd⟩
  · obtain ⟨ps, hps, hpl⟩ := hpoints hp
    obtain ⟨qs, hqs, hql⟩ := hpoints hq
    exact hd.mem_of_tendsto hc hn K.isCompact K.nonempty
      (fun n => (hU (φ n)).convex (hps n) (hqs n) ha hb hab)
      ((hpl.const_smul a).add (hql.const_smul b))
  · obtain ⟨q, hq, hlim⟩ := hpoints hp
    have h := ((by fun_prop : Continuous fun z : Plane => (z.1, min y z.2)).tendsto p).comp hlim
    rw [min_eq_left hyp] at h
    exact hd.mem_of_tendsto hc hn K.isCompact K.nonempty (fun n => (hU (φ n)).downward _ (hq n) _
      (le_min hy0 ((hU (φ n)).inStrip (hq n)).1) (min_le_right _ _)) h

theorem abs_coordDot_sub_le_dist (p q v : Plane) :
    |coordDot p v - coordDot q v| ≤ dist p q * (|v.1| + |v.2|) := by
  have h1 : |p.1 - q.1| ≤ dist p q := by
    simpa only [Prod.dist_eq, Real.dist_eq] using le_max_left (dist p.1 q.1) (dist p.2 q.2)
  have h2 : |p.2 - q.2| ≤ dist p q := by
    simpa only [Prod.dist_eq, Real.dist_eq] using le_max_right (dist p.1 q.1) (dist p.2 q.2)
  calc |coordDot p v - coordDot q v| = |(p.1 - q.1) * v.1 + (p.2 - q.2) * v.2| := by
        unfold coordDot; congr 1; ring
    _ ≤ |p.1 - q.1| * |v.1| + |p.2 - q.2| * |v.2| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ dist p q * (|v.1| + |v.2|) := by
        rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

theorem support_le_add_hausdorff {K L : Set Plane}
    (hK : IsCompact K) (hKne : K.Nonempty) (hL : IsCompact L) (hLne : L.Nonempty)
    (v : Plane) :
    support K v ≤ support L v + Metric.hausdorffDist K L * (|v.1| + |v.2|) := by
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hK hKne v
  obtain ⟨q, hq, hpq⟩ := exists_mem_dist_le_hausdorff hK hKne hL hLne hp
  linarith [(abs_le.mp (abs_coordDot_sub_le_dist p q v)).2, coordDot_le_support hL hq v,
    mul_le_mul_of_nonneg_right hpq (add_nonneg (abs_nonneg v.1) (abs_nonneg v.2))]

theorem abs_support_sub_le_hausdorff {K L : Set Plane}
    (hK : IsCompact K) (hKne : K.Nonempty) (hL : IsCompact L) (hLne : L.Nonempty)
    (v : Plane) :
    |support K v - support L v| ≤ Metric.hausdorffDist K L * (|v.1| + |v.2|) := by
  have hLK := support_le_add_hausdorff hL hLne hK hKne v
  rw [Metric.hausdorffDist_comm] at hLK
  exact abs_le.mpr ⟨by linarith, by linarith [support_le_add_hausdorff hK hKne hL hLne v]⟩

theorem CapHausdorffTendsto.support_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsCompact (U n))
    (hUne : ∀ n, (U n).Nonempty) (hK : IsCompact K) (hKne : K.Nonempty) (v : Plane) :
    Tendsto (fun n => support (U n) v) atTop (𝓝 (support K v)) :=
  tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero (fun _ => dist_nonneg)
    (fun n => abs_support_sub_le_hausdorff (hU n) (hUne n) hK hKne v)
    (by simpa only [zero_mul] using h.mul_const (|v.1| + |v.2|))

theorem CapHausdorffTendsto.horizontalRight_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsCompact (U n))
    (hUne : ∀ n, (U n).Nonempty) (hK : IsCompact K) (hKne : K.Nonempty) :
    Tendsto (fun n => horizontalRight (U n)) atTop (𝓝 (horizontalRight K)) := by
  simpa only [support_horizontal_right] using h.support_tendsto hU hUne hK hKne (1, 0)

theorem CapHausdorffTendsto.horizontalLeft_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsCompact (U n))
    (hUne : ∀ n, (U n).Nonempty) (hK : IsCompact K) (hKne : K.Nonempty) :
    Tendsto (fun n => horizontalLeft (U n)) atTop (𝓝 (horizontalLeft K)) := by
  have hLeft (n : ℕ) := support_horizontal_left (hU n) (hUne n)
  simpa only [support_horizontal_left hK hKne, hLeft, neg_neg] using
    (h.support_tendsto hU hUne hK hKne (-1, 0)).neg

end AmbidextrousSofa
