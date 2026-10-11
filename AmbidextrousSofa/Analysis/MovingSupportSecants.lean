module

public import AmbidextrousSofa.Analysis.WingCurvatureDensity

@[expose] public section

/-!
# Moving support points and shrinking angular secants

At a non-atomic target normal, its supporting face is a singleton.
Compactness and the actual support equalities then force every sequence
of nearby supporting points to converge to that singleton, even when the
supporting directions move. The forward angular secant is sandwiched
between the tangent coordinates of two such points. This proves its
limit without dividing a Hausdorff error by the shrinking mesh.
-/

noncomputable section

open Set Filter MovingSofaOptimality
open scoped Topology

namespace AmbidextrousSofa

theorem CapHausdorffTendsto.support_tendsto_moving
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {v : ℕ → Plane} {w : Plane} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => support (U n) (v n)) atTop (𝓝 (support K w)) :=
  -- Elaborating the composition before unifying with the goal keeps this fast.
  ((continuous_capSupport.tendsto (hK.toCompactCap, w)).comp
    ((IsDownwardCap.tendsto_toCompactCap hU hK h).prodMk_nhds hv) :)

/-- Supporting points converge at every non-atomic target normal. Both
the cap and its normal may vary. -/
theorem CapHausdorffTendsto.supporting_points_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {p : ℕ → Plane} {angle : ℕ → ℝ} {t : ℝ}
    (hp : ∀ n, p n ∈ edge (U n) (angle n))
    (hangle : Tendsto angle atTop (𝓝 t)) (ht : sigmaAt K t = 0) :
    Tendsto p atTop (𝓝 (vplus K t)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨q, -, ms, hms, hq⟩ := hB.tendsto_subseq (fun n => hbox (ns n) (hp (ns n)).1)
  have hseq : Tendsto (fun n => ns (ms n)) atTop atTop := hns.comp hms.tendsto_atTop
  have hH : CapHausdorffTendsto (fun n => U (ns (ms n))) K := h.comp hseq
  have hnormal := (continuous_unitNormal.tendsto t).comp (hangle.comp hseq)
  have hqedge : q ∈ edge K t := ⟨hH.mem_of_tendsto (fun n => (hU _).isCompact)
    (fun n => (hU _).nonempty) hK.isCompact hK.nonempty (fun n => (hp _).1) hq,
    tendsto_nhds_unique ((hq.fst_nhds.mul hnormal.fst_nhds).add (hq.snd_nhds.mul hnormal.snd_nhds))
      ((hH.support_tendsto_moving (fun n => hU _) hK hnormal).congr fun n => (hp _).2.symm)⟩
  have hvertex := (proposition2_1_2 hK.imported_isConvexBody t).2
  rw [ht, zero_smul, add_zero] at hvertex
  rw [edge_eq_segment hK.imported_isConvexBody, ← hvertex, segment_same,
    mem_singleton_iff] at hqedge
  exact ⟨ms, hqedge ▸ hq⟩

def forwardAngularSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  (supp U (t + δ) - supp U t * Real.cos δ) / Real.sin δ

theorem IsDownwardCap.forwardAngularSecant_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {t δ : ℝ} (hsin : 0 < Real.sin δ) (hcos : 0 ≤ Real.cos δ) :
    dot (vplus U t) (vvec t) ≤ forwardAngularSecant U t δ ∧
      forwardAngularSecant U t δ ≤ dot (vplus U (t + δ)) (vvec t) := by
  obtain ⟨hpK, hnew : dot (vplus U (t + δ)) (uvec (t + δ)) = supp U (t + δ)⟩ :=
    vplus_mem_edge hU.imported_isConvexBody (t + δ)
  rw [dot_uvec_eq_cos_add_sin _ _ t, add_sub_cancel_left] at hnew
  exact ⟨(le_div_iff₀ hsin).mpr (ang_dplus_mul_sin_le hU.imported_isConvexBody t δ),
    (div_le_iff₀ hsin).mpr <| by
      linarith [mul_le_mul_of_nonneg_right (dot_le_supp hU.isCompact hpK t) hcos]⟩

theorem CapHausdorffTendsto.forwardAngularSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n)) (ht : sigmaAt K t = 0) :
    Tendsto (fun n => forwardAngularSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (dot (vplus K t) (vvec t))) := by
  have hv := (continuous_vvec.tendsto t).comp hangle
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ((continuous_dot_pair.tendsto _).comp
    ((h.supporting_points_tendsto hU hK hB hbox
      (fun n => vplus_mem_edge (hU n).imported_isConvexBody (angle n)) hangle ht).prodMk_nhds hv))
    ((continuous_dot_pair.tendsto _).comp ((h.supporting_points_tendsto hU hK hB hbox
      (fun n => vplus_mem_edge (hU n).imported_isConvexBody (angle n + δ n))
      (by simpa using hangle.add hδ) ht).prodMk_nhds hv))
    (fun n => ((hU n).forwardAngularSecant_bounds (hsin n) (hcos n)).1)
    (fun n => ((hU n).forwardAngularSecant_bounds (hsin n) (hcos n)).2)

def backwardAngularSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  (supp U t * Real.cos δ - supp U (t - δ)) / Real.sin δ

theorem IsDownwardCap.backwardAngularSecant_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {t δ : ℝ} (hsin : 0 < Real.sin δ) (hcos : 0 ≤ Real.cos δ) :
    dot (vplus U (t - δ)) (vvec t) ≤ backwardAngularSecant U t δ ∧
      backwardAngularSecant U t δ ≤ dot (vminus U t) (vvec t) := by
  obtain ⟨hpK, hold : dot (vplus U (t - δ)) (uvec (t - δ)) = supp U (t - δ)⟩ :=
    vplus_mem_edge hU.imported_isConvexBody (t - δ)
  rw [dot_uvec_eq_cos_add_sin _ _ t, sub_sub_cancel_left, Real.cos_neg, Real.sin_neg] at hold
  exact ⟨(le_div_iff₀ hsin).mpr <| by
      linarith [mul_le_mul_of_nonneg_right (dot_le_supp hU.isCompact hpK t) hcos],
    (div_le_iff₀ hsin).mpr (ang_le_dminus_mul_sin hU.imported_isConvexBody t δ)⟩

theorem CapHausdorffTendsto.backwardAngularSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n)) (ht : sigmaAt K t = 0) :
    Tendsto (fun n => backwardAngularSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (dot (vplus K t) (vvec t))) := by
  have hv := (continuous_vvec.tendsto t).comp hangle
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ((continuous_dot_pair.tendsto _).comp
    ((h.supporting_points_tendsto hU hK hB hbox
      (fun n => vplus_mem_edge (hU n).imported_isConvexBody (angle n - δ n))
      (by simpa using hangle.sub hδ) ht).prodMk_nhds hv))
    ((continuous_dot_pair.tendsto _).comp ((h.supporting_points_tendsto hU hK hB hbox
      (fun n => vminus_mem_edge (hU n).imported_isConvexBody (angle n)) hangle ht).prodMk_nhds hv))
    (fun n => ((hU n).backwardAngularSecant_bounds (hsin n) (hcos n)).1)
    (fun n => ((hU n).backwardAngularSecant_bounds (hsin n) (hcos n)).2)

end AmbidextrousSofa
