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
  refine ⟨q, hq, ?_⟩
  rw [← hdist]
  exact Metric.infDist_le_hausdorffDist_of_mem hp
    (hausdorffEDist_ne_top_of_compact hK hKne hL hLne)

theorem CapHausdorffTendsto.exists_points_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsCompact (U n)) (hUne : ∀ n, (U n).Nonempty)
    (hK : IsCompact K) (hKne : K.Nonempty) {p : Plane} (hp : p ∈ K) :
    ∃ q : ℕ → Plane, (∀ n, q n ∈ U n) ∧ Tendsto q atTop (𝓝 p) := by
  have hnear : ∀ n, ∃ q ∈ U n, dist q p ≤ Metric.hausdorffDist (U n) K := by
    intro n
    obtain ⟨q, hq, hpq⟩ := exists_mem_dist_le_hausdorff hK hKne (hU n) (hUne n) hp
    exact ⟨q, hq, by simpa only [dist_comm, Metric.hausdorffDist_comm] using hpq⟩
  choose q hq hdist using hnear
  refine ⟨q, hq, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  exact squeeze_zero (fun n => dist_nonneg) hdist h

theorem CapHausdorffTendsto.mem_of_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsCompact (U n)) (hUne : ∀ n, (U n).Nonempty)
    (hK : IsCompact K) (hKne : K.Nonempty)
    {q : ℕ → Plane} {p : Plane} (hq : ∀ n, q n ∈ U n) (hp : Tendsto q atTop (𝓝 p)) :
    p ∈ K := by
  have hbound : ∀ n, Metric.infDist p K ≤
      Metric.hausdorffDist (U n) K + dist p (q n) := by
    intro n
    have hfirst := Metric.infDist_le_infDist_add_dist (x := p) (y := q n) (s := K)
    have hsecond := Metric.infDist_le_hausdorffDist_of_mem (hq n)
      (hausdorffEDist_ne_top_of_compact (hU n) (hUne n) hK hKne)
    linarith
  have hlim : Tendsto (fun _ : ℕ => Metric.infDist p K) atTop (𝓝 0) :=
    squeeze_zero (fun _ => Metric.infDist_nonneg) hbound
      (by simpa only [dist_self, add_zero] using
        h.add ((tendsto_const_nhds (x := p) : Tendsto (fun _ : ℕ => p) atTop (𝓝 p)).dist hp))
  have hzero : Metric.infDist p K = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  rw [← hK.isClosed.closure_eq, Metric.mem_closure_iff_infDist_zero hKne]
  exact hzero

theorem CapHausdorffTendsto.convex_limit
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsCompact (U n)) (hUne : ∀ n, (U n).Nonempty)
    (hconvex : ∀ n, Convex ℝ (U n)) (hK : IsCompact K) (hKne : K.Nonempty) :
    Convex ℝ K := by
  intro p hp q hq a b ha hb hab
  obtain ⟨pseq, hpseq, hpseq_lim⟩ := h.exists_points_tendsto hU hUne hK hKne hp
  obtain ⟨qseq, hqseq, hqseq_lim⟩ := h.exists_points_tendsto hU hUne hK hKne hq
  apply h.mem_of_tendsto hU hUne hK hKne
    (fun n => hconvex n (hpseq n) (hqseq n) ha hb hab)
  exact (hpseq_lim.const_smul a).add (hqseq_lim.const_smul b)

theorem CapHausdorffTendsto.subset_closed_limit
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsCompact (U n)) (hUne : ∀ n, (U n).Nonempty)
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hB : IsClosed B) (hsub : ∀ n, U n ⊆ B) : K ⊆ B := by
  intro p hp
  obtain ⟨q, hq, hlim⟩ := h.exists_points_tendsto hU hUne hK hKne hp
  exact hB.mem_of_tendsto hlim (Eventually.of_forall (fun n => hsub n (hq n)))

theorem CapHausdorffTendsto.isDownwardCap_limit
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsCompact K) (hKne : K.Nonempty) :
    IsDownwardCap K := by
  have hc : ∀ n, IsCompact (U n) := fun n => (hU n).isCompact
  have hn : ∀ n, (U n).Nonempty := fun n => (hU n).nonempty
  refine ⟨hKne, hK, h.convex_limit hc hn (fun n => (hU n).convex) hK hKne,
    h.subset_closed_limit hc hn hK hKne ?_ (fun n => (hU n).inStrip), ?_⟩
  · exact isClosed_Icc.preimage continuous_snd
  · intro p hp y hy0 hyp
    obtain ⟨q, hq, hlim⟩ := h.exists_points_tendsto hc hn hK hKne hp
    let clipped : ℕ → Plane := fun n => ((q n).1, min y (q n).2)
    have hclip : ∀ n, clipped n ∈ U n := by
      intro n
      exact (hU n).downward (q n) (hq n) _
        (le_min hy0 ((hU n).inStrip (hq n)).1) (min_le_right _ _)
    apply h.mem_of_tendsto hc hn hK hKne hclip
    have hmap : Continuous (fun z : Plane => (z.1, min y z.2)) := by fun_prop
    have h2 := (hmap.tendsto p).comp hlim
    rw [min_eq_left hyp] at h2
    exact h2

/-- Blaschke selection specialized to the full downward-cap domain. The
limiting cap remains in the same compact box, including all degeneracies. -/
theorem exists_cap_hausdorff_subsequence {U : ℕ → Set Plane}
    (hU : ∀ n, IsDownwardCap (U n)) {B : Set Plane}
    (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    ∃ K : Set Plane, IsDownwardCap K ∧ K ⊆ B ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ CapHausdorffTendsto (U ∘ φ) K := by
  let C : ℕ → NonemptyCompacts Plane :=
    fun n => ⟨⟨U n, (hU n).isCompact⟩, (hU n).nonempty⟩
  let domain : Set (NonemptyCompacts Plane) := {D | (D : Set Plane) ⊆ B}
  have htotal : TotallyBounded domain :=
    NonemptyCompacts.totallyBounded_subsets_of_totallyBounded hB.totallyBounded
  have hcompact : IsCompact (closure domain) :=
    (TotallyBounded.closure htotal).isCompact_of_isComplete isClosed_closure.isComplete
  obtain ⟨Kc, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (show C n ∈ domain from hsub n))
  let K : Set Plane := Kc
  have hK : IsCompact K := Kc.isCompact
  have hKne : K.Nonempty := Kc.nonempty
  have hd : CapHausdorffTendsto (U ∘ φ) K := by
    have h := tendsto_iff_dist_tendsto_zero.mp hlim
    simp only [NonemptyCompacts.dist_eq, C] at h
    exact h
  refine ⟨K, hd.isDownwardCap_limit (fun n => hU (φ n)) hK hKne, ?_, φ, hφ, hd⟩
  exact hd.subset_closed_limit (fun n => (hU (φ n)).isCompact)
    (fun n => (hU (φ n)).nonempty) hK hKne hB.isClosed (fun n => hsub (φ n))

theorem abs_coordDot_sub_le_dist (p q v : Plane) :
    |coordDot p v - coordDot q v| ≤ dist p q * (|v.1| + |v.2|) := by
  have hfst : |p.1 - q.1| ≤ dist p q := by
    simpa only [Prod.dist_eq, Real.dist_eq] using (le_max_left (dist p.1 q.1) (dist p.2 q.2))
  have hsnd : |p.2 - q.2| ≤ dist p q := by
    simpa only [Prod.dist_eq, Real.dist_eq] using (le_max_right (dist p.1 q.1) (dist p.2 q.2))
  calc
    |coordDot p v - coordDot q v| = |(p.1 - q.1) * v.1 + (p.2 - q.2) * v.2| := by
      unfold coordDot
      congr 1
      ring
    _ ≤ |(p.1 - q.1) * v.1| + |(p.2 - q.2) * v.2| := abs_add_le _ _
    _ = |p.1 - q.1| * |v.1| + |p.2 - q.2| * |v.2| := by rw [abs_mul, abs_mul]
    _ ≤ dist p q * |v.1| + dist p q * |v.2| :=
      add_le_add (mul_le_mul_of_nonneg_right hfst (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hsnd (abs_nonneg _))
    _ = dist p q * (|v.1| + |v.2|) := by ring

theorem support_le_add_hausdorff {K L : Set Plane}
    (hK : IsCompact K) (hKne : K.Nonempty) (hL : IsCompact L) (hLne : L.Nonempty)
    (v : Plane) :
    support K v ≤ support L v + Metric.hausdorffDist K L * (|v.1| + |v.2|) := by
  obtain ⟨p, hp, hsupport⟩ := exists_coordDot_eq_support hK hKne v
  obtain ⟨q, hq, hpq⟩ := exists_mem_dist_le_hausdorff hK hKne hL hLne hp
  have hdot := (abs_le.mp (abs_coordDot_sub_le_dist p q v)).2
  have hdist := mul_le_mul_of_nonneg_right hpq (add_nonneg (abs_nonneg v.1) (abs_nonneg v.2))
  have hqbound := coordDot_le_support hL hq v
  linarith

theorem abs_support_sub_le_hausdorff {K L : Set Plane}
    (hK : IsCompact K) (hKne : K.Nonempty) (hL : IsCompact L) (hLne : L.Nonempty)
    (v : Plane) :
    |support K v - support L v| ≤ Metric.hausdorffDist K L * (|v.1| + |v.2|) := by
  have hKL := support_le_add_hausdorff hK hKne hL hLne v
  have hLK := support_le_add_hausdorff hL hLne hK hKne v
  rw [Metric.hausdorffDist_comm] at hLK
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem CapHausdorffTendsto.support_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsCompact (U n))
    (hUne : ∀ n, (U n).Nonempty) (hK : IsCompact K) (hKne : K.Nonempty) (v : Plane) :
    Tendsto (fun n => support (U n) v) atTop (𝓝 (support K v)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _)
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
  have h := (h.support_tendsto hU hUne hK hKne (-1, 0)).neg
  have hLeft (n : ℕ) := support_horizontal_left (hU n) (hUne n)
  simpa only [support_horizontal_left hK hKne, hLeft, neg_neg] using h

end AmbidextrousSofa
