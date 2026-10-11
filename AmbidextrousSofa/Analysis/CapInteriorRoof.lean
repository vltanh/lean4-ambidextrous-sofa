module

public import AmbidextrousSofa.Analysis.CapCompactness
public import Mathlib.Analysis.Convex.Continuous

@[expose] public section

/-!
# Actual roofs at moving interior points

Hausdorff convergence alone does not make the heights of vertical endpoint
faces continuous. At an interior projection point, however, concavity and
the unit height bound give a common local Lipschitz constant. Actual points
approximating the limiting roof then provide a lower bound. Nearest points
in the limiting cap and relative continuity of its roof provide the upper
bound. Both bounds apply to the original compact fibers.
-/

open Set Filter
open scoped ENNReal NNReal
open scoped Topology

namespace AmbidextrousSofa

/-- A neighborhood strictly inside the limiting projection has one
Lipschitz constant for every sufficiently late actual cap roof. -/
theorem CapHausdorffTendsto.exists_eventually_lipschitz_capRoof
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) {x : ℝ}
    (hx : x ∈ Ioo (horizontalLeft K) (horizontalRight K)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : ℝ≥0, ∀ᶠ n in atTop,
      LipschitzOnWith L (capRoof (U n)) (Metric.ball x δ) := by
  have hm := lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  obtain ⟨δ, hδ, hl, hr⟩ : ∃ δ > 0, horizontalLeft K < x - 2 * δ ∧ x + 2 * δ < horizontalRight K :=
    ⟨_, div_pos hm four_pos,
      by linarith [min_le_left (x - horizontalLeft K) (horizontalRight K - x)],
      by linarith [min_le_right (x - horizontalLeft K) (horizontalRight K - x)]⟩
  refine ⟨δ, hδ, (2 / δ).toNNReal, ?_⟩
  filter_upwards [(h.horizontalLeft_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
      hK.isCompact hK.nonempty).eventually (Iio_mem_nhds hl),
    (h.horizontalRight_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
      hK.isCompact hK.nonempty).eventually (Ioi_mem_nhds hr)] with n hnleft hnright
  have hball : Metric.ball x (2 * δ) ⊆ horizontalProjection (U n) := by
    rw [Real.ball_eq_Ioo, (hU n).horizontalProjection_eq_Icc]
    exact Ioo_subset_Icc_self.trans (Icc_subset_Icc hnleft.le hnright.le)
  have hLip := ((hU n).concaveOn_capRoof.subset hball
    (convex_ball x (2 * δ))).lipschitzOnWith_of_abs_le hδ fun z _ => by
      rw [abs_of_nonneg (capRoof_nonneg (hU n).isCompact (fun p hp => ((hU n).inStrip hp).1) z)]
      exact capRoof_le_one (hU n).isCompact (hU n).inStrip z
  simpa only [mul_one, show 2 * δ - δ = δ by ring] using hLip

/-- Interior convergence uses actual attained roof points in both caps.
The moving abscissae may approach from either side and need not be monotone. -/
theorem CapHausdorffTendsto.capRoof_tendsto_of_interior
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {x : ℝ} {t : ℕ → ℝ}
    (hx : x ∈ Ioo (horizontalLeft K) (horizontalRight K))
    (htmem : ∀ n, t n ∈ horizontalProjection (U n))
    (ht : Tendsto t atTop (𝓝 x)) :
    Tendsto (fun n => capRoof (U n) (t n)) atTop (𝓝 (capRoof K x)) := by
  have hxK : x ∈ horizontalProjection K := by
    rw [hK.horizontalProjection_eq_Icc]
    exact Ioo_subset_Icc_self hx
  obtain ⟨δ, hδ, L, hLip⟩ := h.exists_eventually_lipschitz_capRoof hU hK hx
  obtain ⟨q, hq, hqlim⟩ := h.exists_points_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty (capRoof_mem hK.isCompact hxK)
  choose z hz hdist using fun n => exists_mem_dist_le_hausdorff (hU n).isCompact
    (hU n).nonempty hK.isCompact hK.nonempty (capRoof_mem (hU n).isCompact (htmem n))
  simp only [Prod.dist_eq, max_le_iff, Real.dist_eq] at hdist
  have hlower : Tendsto (fun n => (q n).2 - (L : ℝ) * dist (q n).1 (t n)) atTop
      (𝓝 (capRoof K x)) := by
    simpa only [dist_self, mul_zero, sub_zero] using
      hqlim.snd_nhds.sub ((hqlim.fst_nhds.dist ht).const_mul (L : ℝ))
  have hzlim : Tendsto (fun n => (z n).1) atTop (𝓝 x) := ht.congr_dist
    (squeeze_zero (fun _ => dist_nonneg) (fun n => (Real.dist_eq _ _).trans_le (hdist n).1) h)
  have hupper : Tendsto (fun n => capRoof K (z n).1 + Metric.hausdorffDist (U n) K) atTop
      (𝓝 (capRoof K x)) := by
    simpa only [add_zero, Function.comp_apply] using ((hK.continuousOn_capRoof x hxK).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hzlim, Eventually.of_forall fun n => ⟨z n, hz n, rfl⟩⟩)).add h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_
    (Eventually.of_forall fun n => ?_)
  · filter_upwards [hLip, hqlim.fst_nhds.eventually (Metric.ball_mem_nhds x hδ),
      ht.eventually (Metric.ball_mem_nhds x hδ)] with n hn hqn htn
    have hL := hn.dist_le_mul (q n).1 hqn (t n) htn
    rw [Real.dist_eq] at hL
    linarith [le_capRoof (hU n).isCompact (hq n),
      le_abs_self (capRoof (U n) (q n).1 - capRoof (U n) (t n))]
  · linarith [le_capRoof hK.isCompact (hz n), (abs_le.mp (hdist n).2).2]

theorem CapHausdorffTendsto.middleLeft_roof_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => capRoof (U n)
      (horizontalLeft (U n) + (horizontalRight (U n) - horizontalLeft (U n)) / 4))
      atTop (𝓝 (capRoof K (horizontalLeft K + (horizontalRight K - horizontalLeft K) / 4))) := by
  have hl := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  refine h.capRoof_tendsto_of_interior hU hK ⟨by linarith, by linarith⟩ (fun n => ?_)
    (hl.add ((hr.sub hl).div_const 4))
  have hlr := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
  rw [(hU n).horizontalProjection_eq_Icc]
  exact ⟨by linarith, by linarith⟩

theorem CapHausdorffTendsto.middleRight_roof_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => capRoof (U n)
      (horizontalRight (U n) - (horizontalRight (U n) - horizontalLeft (U n)) / 4))
      atTop (𝓝 (capRoof K (horizontalRight K - (horizontalRight K - horizontalLeft K) / 4))) := by
  have hl := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  refine h.capRoof_tendsto_of_interior hU hK ⟨by linarith, by linarith⟩ (fun n => ?_)
    (hr.sub ((hr.sub hl).div_const 4))
  have hlr := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
  rw [(hU n).horizontalProjection_eq_Icc]
  exact ⟨by linarith, by linarith⟩

end AmbidextrousSofa
