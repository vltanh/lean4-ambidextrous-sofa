module

public import AmbidextrousSofa.Analysis.CapCompactness

@[expose] public section

/-!
# Area continuity for compact convex caps

Interior points eventually belong to every nearby cap. Exterior points
eventually stay outside, and the frontier of a convex set has zero planar
measure. Dominated convergence in a common compact box then gives continuity
of the actual Lebesgue area, including lower-dimensional limiting caps.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- A corner of the product unit ball maximizing a coordinate linear form. -/
def supportBoxCorner (v : Plane) : Plane :=
  (if 0 ≤ v.1 then 1 else -1, if 0 ≤ v.2 then 1 else -1)

/-- An interior product ball gives a support margin in every direction,
with the dual one-norm matching the Hausdorff support estimate. -/
theorem support_margin_of_ball_subset {K : Set Plane} (hK : IsCompact K)
    {p : Plane} {r : ℝ} (hr : 0 < r) (hball : Metric.ball p r ⊆ K) (v : Plane) :
    coordDot p v + r / 2 * (|v.1| + |v.2|) ≤ support K v := by
  have hc : ‖supportBoxCorner v‖ = 1 := by unfold supportBoxCorner; split_ifs <;> simp
  have hd : coordDot (supportBoxCorner v) v = |v.1| + |v.2| := by
    unfold supportBoxCorner coordDot
    split_ifs <;> simp_all [abs_of_nonneg, abs_of_neg]
  have hmem : p + (r / 2) • supportBoxCorner v ∈ K :=
    hball (by simpa [norm_smul, hc, abs_of_pos hr] using half_lt_self hr)
  simpa only [coordDot_add_left, coordDot_smul_left, hd] using coordDot_le_support hK hmem v

theorem CapHausdorffTendsto.eventually_mem_of_mem_interior
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {p : Plane} (hp : p ∈ interior K) : ∀ᶠ n in atTop, p ∈ U n := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  filter_upwards [h.eventually (Iio_mem_nhds (half_pos hr))] with n hn
  refine (mem_iff_forall_coordDot_le_support (hU n).isCompact (hU n).nonempty
    (hU n).convex p).2 fun v => ?_
  have hsupport := support_le_add_hausdorff hK.isCompact hK.nonempty
    (hU n).isCompact (hU n).nonempty v
  rw [Metric.hausdorffDist_comm] at hsupport
  linarith [support_margin_of_ball_subset hK.isCompact hr (hball.trans interior_subset) v,
    mul_le_mul_of_nonneg_right hn.le (add_nonneg (abs_nonneg v.1) (abs_nonneg v.2))]

theorem CapHausdorffTendsto.eventually_notMem_of_notMem
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {p : Plane} (hp : p ∉ K) : ∀ᶠ n in atTop, p ∉ U n := by
  filter_upwards [h.eventually (Iio_mem_nhds
    ((hK.isCompact.isClosed.notMem_iff_infDist_pos hK.nonempty).1 hp))] with n hn hpn
  exact hn.not_ge (Metric.infDist_le_hausdorffDist_of_mem hpn
    (hausdorffEDist_ne_top_of_compact (hU n).isCompact (hU n).nonempty hK.isCompact hK.nonempty))

/-- Actual indicator functions converge away from the null frontier. The
statement includes a limiting segment or point because its whole set is null. -/
theorem CapHausdorffTendsto.indicator_tendsto_ae
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    ∀ᵐ p : Plane ∂volume, Tendsto (fun n => (U n).indicator (fun _ => (1 : ℝ)) p)
      atTop (𝓝 (K.indicator (fun _ => (1 : ℝ)) p)) := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Convex.addHaar_frontier volume hK.convex)]
    with p hp
  by_cases hpK : p ∈ K
  · rw [indicator_of_mem hpK]
    exact tendsto_const_nhds.congr' ((h.eventually_mem_of_mem_interior hU hK
      (by_contra fun hnot => hp ⟨subset_closure hpK, hnot⟩)).mono
      fun n hn => (indicator_of_mem hn _).symm)
  · rw [indicator_of_notMem hpK]
    exact tendsto_const_nhds.congr' ((h.eventually_notMem_of_notMem hU hK hpK).mono
      fun n hn => (indicator_of_notMem hn _).symm)

end AmbidextrousSofa
