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

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem CapHausdorffTendsto.support_tendsto_moving
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {v : ℕ → Plane} {w : Plane} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => support (U n) (v n)) atTop (𝓝 (support K w)) := by
  have hcap := IsDownwardCap.tendsto_toCompactCap hU hK h
  exact (continuous_capSupport.tendsto (hK.toCompactCap, w)).comp (hcap.prodMk_nhds hv)

theorem IsDownwardCap.edge_eq_singleton_of_no_atom {K : Set Plane}
    (hK : IsDownwardCap K) {t : ℝ} (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    MovingSofaOptimality.edge K t = {MovingSofaOptimality.vplus K t} := by
  have hvertex := (MovingSofaOptimality.proposition2_1_2 hK.imported_isConvexBody t).2
  rw [ht, zero_smul, add_zero] at hvertex
  rw [MovingSofaOptimality.edge_eq_segment hK.imported_isConvexBody, ← hvertex, segment_same]

/-- Supporting points converge at every non-atomic target normal. Both
the cap and its normal may vary. -/
theorem CapHausdorffTendsto.supporting_points_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {p : ℕ → Plane} {angle : ℕ → ℝ} {t : ℝ}
    (hp : ∀ n, p n ∈ MovingSofaOptimality.edge (U n) (angle n))
    (hangle : Tendsto angle atTop (𝓝 t)) (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    Tendsto p atTop (𝓝 (MovingSofaOptimality.vplus K t)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨q, _, ms, hms, hq⟩ := hB.tendsto_subseq
    (fun n => hbox (ns n) (hp (ns n)).1)
  let seq := fun n => ns (ms n)
  have hseq : Tendsto seq atTop atTop := hns.comp hms.tendsto_atTop
  have hH : CapHausdorffTendsto (fun n => U (seq n)) K := h.comp hseq
  have hqt : Tendsto (fun n => p (seq n)) atTop (𝓝 q) := hq
  have hqK : q ∈ K := hH.mem_of_tendsto
    (fun n => (hU (seq n)).isCompact) (fun n => (hU (seq n)).nonempty)
    hK.isCompact hK.nonempty (fun n => (hp (seq n)).1) hqt
  have hθ := hangle.comp hseq
  have hnormal : Tendsto (fun n => unitNormal (angle (seq n))) atTop (𝓝 (unitNormal t)) :=
    (Real.continuous_cos.tendsto t |>.comp hθ).prodMk_nhds
      (Real.continuous_sin.tendsto t |>.comp hθ)
  have hsupport := hH.support_tendsto_moving (fun n => hU (seq n)) hK hnormal
  have hdot : Tendsto (fun n => MovingSofaOptimality.dot (p (seq n)) (MovingSofaOptimality.uvec (angle (seq n))))
      atTop (𝓝 (MovingSofaOptimality.dot q (MovingSofaOptimality.uvec t))) :=
    (hqt.fst_nhds.mul hnormal.fst_nhds).add (hqt.snd_nhds.mul hnormal.snd_nhds)
  have heq : MovingSofaOptimality.dot q (MovingSofaOptimality.uvec t) = MovingSofaOptimality.supp K t :=
    tendsto_nhds_unique hdot (hsupport.congr' (Eventually.of_forall
      (fun n => (hp (seq n)).2.symm)))
  have hqedge : q ∈ MovingSofaOptimality.edge K t := ⟨hqK, heq⟩
  rw [hK.edge_eq_singleton_of_no_atom ht, mem_singleton_iff] at hqedge
  exact ⟨ms, by simpa only [seq, hqedge] using hqt⟩

def forwardAngularSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  (MovingSofaOptimality.supp U (t + δ) - MovingSofaOptimality.supp U t * Real.cos δ) / Real.sin δ

theorem IsDownwardCap.forwardAngularSecant_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {t δ : ℝ} (hsin : 0 < Real.sin δ) (hcos : 0 ≤ Real.cos δ) :
    MovingSofaOptimality.dot (MovingSofaOptimality.vplus U t) (MovingSofaOptimality.vvec t) ≤ forwardAngularSecant U t δ ∧
      forwardAngularSecant U t δ ≤
        MovingSofaOptimality.dot (MovingSofaOptimality.vplus U (t + δ)) (MovingSofaOptimality.vvec t) := by
  constructor
  · exact (le_div_iff₀ hsin).mpr
      (MovingSofaOptimality.ang_dplus_mul_sin_le hU.imported_isConvexBody t δ)
  · have hp := MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody (t + δ)
    have hpoint := MovingSofaOptimality.dot_le_supp hU.isCompact hp.1 t
    have hmul := mul_le_mul_of_nonneg_right hpoint hcos
    have hnew : MovingSofaOptimality.dot (MovingSofaOptimality.vplus U (t + δ))
        (MovingSofaOptimality.uvec (t + δ)) = MovingSofaOptimality.supp U (t + δ) := hp.2
    rw [MovingSofaOptimality.dot_uvec_eq_cos_add_sin _ _ t, add_sub_cancel_left] at hnew
    apply (div_le_iff₀ hsin).mpr
    nlinarith

theorem CapHausdorffTendsto.forwardAngularSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    Tendsto (fun n => forwardAngularSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vplus K t) (MovingSofaOptimality.vvec t))) := by
  have hp := h.supporting_points_tendsto hU hK hB hbox
    (fun n => MovingSofaOptimality.vplus_mem_edge (hU n).imported_isConvexBody (angle n)) hangle ht
  have hq := h.supporting_points_tendsto hU hK hB hbox
    (fun n => MovingSofaOptimality.vplus_mem_edge (hU n).imported_isConvexBody (angle n + δ n))
    (by simpa only [add_zero] using hangle.add hδ) ht
  have hv := (MovingSofaOptimality.continuous_vvec.tendsto t).comp hangle
  have hlo : Tendsto
      (fun n => MovingSofaOptimality.dot (MovingSofaOptimality.vplus (U n) (angle n)) (MovingSofaOptimality.vvec (angle n)))
      atTop (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vplus K t) (MovingSofaOptimality.vvec t))) :=
    (hp.fst_nhds.mul hv.fst_nhds).add (hp.snd_nhds.mul hv.snd_nhds)
  have hhi : Tendsto
      (fun n => MovingSofaOptimality.dot (MovingSofaOptimality.vplus (U n) (angle n + δ n)) (MovingSofaOptimality.vvec (angle n)))
      atTop (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vplus K t) (MovingSofaOptimality.vvec t))) :=
    (hq.fst_nhds.mul hv.fst_nhds).add (hq.snd_nhds.mul hv.snd_nhds)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun n => ((hU n).forwardAngularSecant_bounds (hsin n) (hcos n)).1)
    (fun n => ((hU n).forwardAngularSecant_bounds (hsin n) (hcos n)).2)

def backwardAngularSecant (U : Set Plane) (t δ : ℝ) : ℝ :=
  (MovingSofaOptimality.supp U t * Real.cos δ - MovingSofaOptimality.supp U (t - δ)) / Real.sin δ

theorem IsDownwardCap.backwardAngularSecant_bounds {U : Set Plane} (hU : IsDownwardCap U)
    {t δ : ℝ} (hsin : 0 < Real.sin δ) (hcos : 0 ≤ Real.cos δ) :
    MovingSofaOptimality.dot (MovingSofaOptimality.vplus U (t - δ)) (MovingSofaOptimality.vvec t) ≤ backwardAngularSecant U t δ ∧
      backwardAngularSecant U t δ ≤ MovingSofaOptimality.dot (MovingSofaOptimality.vminus U t) (MovingSofaOptimality.vvec t) := by
  constructor
  · have hp := MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody (t - δ)
    have hpoint := MovingSofaOptimality.dot_le_supp hU.isCompact hp.1 t
    have hmul := mul_le_mul_of_nonneg_right hpoint hcos
    have hold : MovingSofaOptimality.dot (MovingSofaOptimality.vplus U (t - δ))
        (MovingSofaOptimality.uvec (t - δ)) = MovingSofaOptimality.supp U (t - δ) := hp.2
    rw [MovingSofaOptimality.dot_uvec_eq_cos_add_sin _ _ t, sub_sub_cancel_left,
      Real.cos_neg, Real.sin_neg] at hold
    apply (le_div_iff₀ hsin).mpr
    nlinarith
  · exact (div_le_iff₀ hsin).mpr
      (MovingSofaOptimality.ang_le_dminus_mul_sin hU.imported_isConvexBody t δ)

theorem CapHausdorffTendsto.backwardAngularSecant_tendsto
    {U : ℕ → Set Plane} {K B : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hB : IsCompact B) (hbox : ∀ n, U n ⊆ B)
    {angle δ : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hsin : ∀ n, 0 < Real.sin (δ n)) (hcos : ∀ n, 0 ≤ Real.cos (δ n))
    (ht : MovingSofaOptimality.sigmaAt K t = 0) :
    Tendsto (fun n => backwardAngularSecant (U n) (angle n) (δ n)) atTop
      (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vplus K t) (MovingSofaOptimality.vvec t))) := by
  have hp := h.supporting_points_tendsto hU hK hB hbox
    (fun n => MovingSofaOptimality.vplus_mem_edge (hU n).imported_isConvexBody (angle n - δ n))
    (by simpa only [sub_zero] using hangle.sub hδ) ht
  have hq := h.supporting_points_tendsto hU hK hB hbox
    (fun n => MovingSofaOptimality.vminus_mem_edge (hU n).imported_isConvexBody (angle n)) hangle ht
  have hv := (MovingSofaOptimality.continuous_vvec.tendsto t).comp hangle
  have hlo : Tendsto
      (fun n => MovingSofaOptimality.dot (MovingSofaOptimality.vplus (U n) (angle n - δ n)) (MovingSofaOptimality.vvec (angle n)))
      atTop (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vplus K t) (MovingSofaOptimality.vvec t))) :=
    (hp.fst_nhds.mul hv.fst_nhds).add (hp.snd_nhds.mul hv.snd_nhds)
  have hhi : Tendsto
      (fun n => MovingSofaOptimality.dot (MovingSofaOptimality.vminus (U n) (angle n)) (MovingSofaOptimality.vvec (angle n)))
      atTop (𝓝 (MovingSofaOptimality.dot (MovingSofaOptimality.vplus K t) (MovingSofaOptimality.vvec t))) :=
    (hq.fst_nhds.mul hv.fst_nhds).add (hq.snd_nhds.mul hv.snd_nhds)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
    (fun n => ((hU n).backwardAngularSecant_bounds (hsin n) (hcos n)).1)
    (fun n => ((hU n).backwardAngularSecant_bounds (hsin n) (hcos n)).2)

end AmbidextrousSofa
