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

noncomputable section

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
  let δ : ℝ := min (x - horizontalLeft K) (horizontalRight K - x) / 4
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    (by norm_num)
  have hδleft : 4 * δ ≤ x - horizontalLeft K := by
    dsimp [δ]
    linarith [min_le_left (x - horizontalLeft K) (horizontalRight K - x)]
  have hδright : 4 * δ ≤ horizontalRight K - x := by
    dsimp [δ]
    linarith [min_le_right (x - horizontalLeft K) (horizontalRight K - x)]
  have hl : horizontalLeft K < x - 2 * δ := by linarith
  have hr : x + 2 * δ < horizontalRight K := by linarith
  have hleft := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hright := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  refine ⟨δ, hδ, (2 / δ).toNNReal, ?_⟩
  filter_upwards [hleft.eventually (Iio_mem_nhds hl),
    hright.eventually (Ioi_mem_nhds hr)] with n hnleft hnright
  have hball : Metric.ball x (2 * δ) ⊆ horizontalProjection (U n) := by
    intro z hz
    have hz' : |z - x| < 2 * δ := by
      simpa only [Metric.mem_ball, Real.dist_eq] using hz
    rw [horizontalProjection_eq_Icc (hU n).nonempty (hU n).isCompact (hU n).convex]
    have hbounds := abs_lt.mp hz'
    exact ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩
  have hconcave := (hU n).concaveOn_capRoof.subset hball (convex_ball x (2 * δ))
  have hbound : ∀ z : ℝ, dist z x < 2 * δ → |capRoof (U n) z| ≤ 1 := by
    intro z _
    rw [abs_of_nonneg (capRoof_nonneg (hU n).isCompact
      (fun p hp => ((hU n).inStrip hp).1) z)]
    exact capRoof_le_one (hU n).isCompact (hU n).inStrip z
  have hLip := hconcave.lipschitzOnWith_of_abs_le hδ hbound
  have hradius : 2 * δ - δ = δ := by ring
  simpa only [mul_one, hradius] using hLip

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
  classical
  have hxK : x ∈ horizontalProjection K := by
    rw [horizontalProjection_eq_Icc hK.nonempty hK.isCompact hK.convex]
    exact ⟨hx.1.le, hx.2.le⟩
  obtain ⟨δ, hδ, L, hLip⟩ := h.exists_eventually_lipschitz_capRoof hU hK hx
  obtain ⟨q, hq, hqlim⟩ := h.exists_points_tendsto
    (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
    hK.isCompact hK.nonempty (capRoof_mem hK.isCompact hxK)
  have hqx : Tendsto (fun n => (q n).1) atTop (𝓝 x) := hqlim.fst_nhds
  have hqy : Tendsto (fun n => (q n).2) atTop (𝓝 (capRoof K x)) := hqlim.snd_nhds
  have hlower : Tendsto
      (fun n => (q n).2 - (L : ℝ) * dist (q n).1 (t n)) atTop (𝓝 (capRoof K x)) := by
    simpa only [dist_self, mul_zero, sub_zero] using
      hqy.sub ((hqx.dist ht).const_mul (L : ℝ))
  have hnear : ∀ n, ∃ z ∈ K,
      dist (t n, capRoof (U n) (t n)) z ≤ Metric.hausdorffDist (U n) K := by
    intro n
    exact exists_mem_dist_le_hausdorff (hU n).isCompact (hU n).nonempty
      hK.isCompact hK.nonempty (capRoof_mem (hU n).isCompact (htmem n))
  choose z hz hdist using hnear
  have hzdist : ∀ n, dist (z n).1 (t n) ≤ Metric.hausdorffDist (U n) K := by
    intro n
    calc
      dist (z n).1 (t n) = dist (t n) (z n).1 := dist_comm _ _
      _ ≤ dist (t n, capRoof (U n) (t n)) (z n) := by
        simpa only [Prod.dist_eq] using
          (le_max_left (dist (t n) (z n).1) (dist (capRoof (U n) (t n)) (z n).2))
      _ ≤ Metric.hausdorffDist (U n) K := hdist n
  have hzlim : Tendsto (fun n => (z n).1) atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n => dist_nonneg)
      (fun n => (dist_triangle (z n).1 (t n) x).trans
        (add_le_add_left (hzdist n) (dist (t n) x)))
    simpa only [zero_add] using h.add (tendsto_iff_dist_tendsto_zero.mp ht)
  have hzprojection : ∀ n, (z n).1 ∈ horizontalProjection K :=
    fun n => ⟨z n, hz n, rfl⟩
  have hrooflim : Tendsto (fun n => capRoof K (z n).1) atTop (𝓝 (capRoof K x)) :=
    (hK.continuousOn_capRoof x hxK).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hzlim, Eventually.of_forall hzprojection⟩)
  have hupper : Tendsto
      (fun n => capRoof K (z n).1 + Metric.hausdorffDist (U n) K)
      atTop (𝓝 (capRoof K x)) := by
    simpa only [add_zero] using hrooflim.add h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hLip, hqx.eventually (Metric.ball_mem_nhds x hδ),
      ht.eventually (Metric.ball_mem_nhds x hδ)] with n hn hqn htn
    have hL := hn.dist_le_mul (q n).1 hqn (t n) htn
    have hqroof : (q n).2 ≤ capRoof (U n) (q n).1 :=
      le_capRoof (hU n).isCompact (by simpa only [Prod.mk.eta] using hq n)
    have hdiff := (le_abs_self (capRoof (U n) (q n).1 - capRoof (U n) (t n))).trans
      ((Real.dist_eq _ _).symm.le.trans hL)
    linarith
  · apply Eventually.of_forall
    intro n
    have hvertical : |capRoof (U n) (t n) - (z n).2| ≤
        Metric.hausdorffDist (U n) K := by
      calc
        |capRoof (U n) (t n) - (z n).2| ≤
            dist (t n, capRoof (U n) (t n)) (z n) := by
          simpa only [Prod.dist_eq, Real.dist_eq] using
            (le_max_right (dist (t n) (z n).1) (dist (capRoof (U n) (t n)) (z n).2))
        _ ≤ Metric.hausdorffDist (U n) K := hdist n
    have hzroof : (z n).2 ≤ capRoof K (z n).1 :=
      le_capRoof hK.isCompact (by simpa only [Prod.mk.eta] using hz n)
    linarith [(abs_le.mp hvertical).2]

theorem CapHausdorffTendsto.middleLeft_roof_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => capRoof (U n)
      (horizontalLeft (U n) + (horizontalRight (U n) - horizontalLeft (U n)) / 4))
      atTop (𝓝 (capRoof K (horizontalLeft K + (horizontalRight K - horizontalLeft K) / 4))) := by
  apply h.capRoof_tendsto_of_interior hU hK ⟨by linarith, by linarith⟩
  · intro n
    rw [horizontalProjection_eq_Icc (hU n).nonempty (hU n).isCompact (hU n).convex]
    have hlr := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    exact ⟨by linarith, by linarith⟩
  · have hl := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
      (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
    have hr := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
      (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
    exact hl.add ((hr.sub hl).div_const 4)

theorem CapHausdorffTendsto.middleRight_roof_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hwidth : horizontalLeft K < horizontalRight K) :
    Tendsto (fun n => capRoof (U n)
      (horizontalRight (U n) - (horizontalRight (U n) - horizontalLeft (U n)) / 4))
      atTop (𝓝 (capRoof K (horizontalRight K - (horizontalRight K - horizontalLeft K) / 4))) := by
  apply h.capRoof_tendsto_of_interior hU hK ⟨by linarith, by linarith⟩
  · intro n
    rw [horizontalProjection_eq_Icc (hU n).nonempty (hU n).isCompact (hU n).convex]
    have hlr := horizontalLeft_le_horizontalRight (hU n).nonempty (hU n).isCompact
    exact ⟨by linarith, by linarith⟩
  · have hl := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
      (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
    have hr := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
      (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
    exact hr.sub ((hr.sub hl).div_const 4)

end AmbidextrousSofa
