import AmbidextrousSofa.Analysis.CapCompactness

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

theorem norm_supportBoxCorner (v : Plane) : ‖supportBoxCorner v‖ = 1 := by
  simp only [supportBoxCorner, Prod.norm_def, Real.norm_eq_abs]
  split_ifs <;> norm_num

theorem coordDot_supportBoxCorner (v : Plane) :
    coordDot (supportBoxCorner v) v = |v.1| + |v.2| := by
  unfold supportBoxCorner coordDot
  split_ifs with hx hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    ring
  · rw [abs_of_nonneg hx, abs_of_nonpos (le_of_not_ge hy)]
    ring
  · rw [abs_of_nonpos (le_of_not_ge hx), abs_of_nonneg hy]
    ring
  · rw [abs_of_nonpos (le_of_not_ge hx), abs_of_nonpos (le_of_not_ge hy)]
    ring

/-- An interior product ball gives a support margin in every direction,
with the dual one-norm matching the Hausdorff support estimate. -/
theorem support_margin_of_ball_subset {K : Set Plane} (hK : IsCompact K)
    {p : Plane} {r : ℝ} (hr : 0 < r) (hball : Metric.ball p r ⊆ K) (v : Plane) :
    coordDot p v + r / 2 * (|v.1| + |v.2|) ≤ support K v := by
  have hmem : p + (r / 2) • supportBoxCorner v ∈ K := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (half_pos hr).le, norm_supportBoxCorner, mul_one]
    linarith
  have h := coordDot_le_support hK hmem v
  simpa only [coordDot_add_left, coordDot_smul_left, coordDot_supportBoxCorner] using h

theorem CapHausdorffTendsto.eventually_mem_of_mem_interior
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {p : Plane} (hp : p ∈ interior K) : ∀ᶠ n in atTop, p ∈ U n := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  have hballK : Metric.ball p r ⊆ K := hball.trans interior_subset
  filter_upwards [h.eventually (Iio_mem_nhds (half_pos hr))] with n hn
  apply (mem_iff_forall_coordDot_le_support (hU n).isCompact (hU n).nonempty
    (hU n).convex p).mpr
  intro v
  have hmargin := support_margin_of_ball_subset hK.isCompact hr hballK v
  have hsupport := support_le_add_hausdorff hK.isCompact hK.nonempty
    (hU n).isCompact (hU n).nonempty v
  rw [Metric.hausdorffDist_comm] at hsupport
  have hsmall := mul_le_mul_of_nonneg_right hn.le
    (add_nonneg (abs_nonneg v.1) (abs_nonneg v.2))
  linarith

theorem CapHausdorffTendsto.eventually_notMem_of_notMem
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {p : Plane} (hp : p ∉ K) : ∀ᶠ n in atTop, p ∉ U n := by
  have hzero : Metric.infDist p K ≠ 0 := by
    intro hz
    apply hp
    rw [← hK.isCompact.isClosed.closure_eq, Metric.mem_closure_iff_infDist_zero hK.nonempty]
    exact hz
  have hpos : 0 < Metric.infDist p K := lt_of_le_of_ne Metric.infDist_nonneg hzero.symm
  filter_upwards [h.eventually (Iio_mem_nhds hpos)] with n hn
  intro hpn
  have hbound := Metric.infDist_le_hausdorffDist_of_mem hpn
    (hausdorffEDist_ne_top_of_compact (hU n).isCompact (hU n).nonempty
      hK.isCompact hK.nonempty)
  exact hn.not_ge hbound

/-- Actual indicator functions converge away from the null frontier. The
statement includes a limiting segment or point because its whole set is null. -/
theorem CapHausdorffTendsto.indicator_tendsto_ae
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    ∀ᵐ p : Plane ∂volume, Tendsto (fun n => (U n).indicator (fun _ => (1 : ℝ)) p)
      atTop (𝓝 (K.indicator (fun _ => (1 : ℝ)) p)) := by
  have hfrontier : ∀ᵐ p : Plane ∂volume, p ∉ frontier K :=
    measure_eq_zero_iff_ae_notMem.mp (Convex.addHaar_frontier volume hK.convex)
  filter_upwards [hfrontier] with p hp
  by_cases hpK : p ∈ K
  · have hpInt : p ∈ interior K := by
      by_contra hnot
      exact hp ⟨subset_closure hpK, hnot⟩
    rw [indicator_of_mem hpK]
    apply tendsto_const_nhds.congr'
    filter_upwards [h.eventually_mem_of_mem_interior hU hK hpInt] with n hn
    simp only [indicator_of_mem hn]
  · rw [indicator_of_notMem hpK]
    apply tendsto_const_nhds.congr'
    filter_upwards [h.eventually_notMem_of_notMem hU hK hpK] with n hn
    simp only [indicator_of_notMem hn]

theorem CapHausdorffTendsto.volumeReal_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {B : Set Plane} (hB : IsCompact B) (hsub : ∀ n, U n ⊆ B) :
    Tendsto (fun n => volume.real (U n)) atTop (𝓝 (volume.real K)) := by
  have hmeas : ∀ n, AEStronglyMeasurable ((U n).indicator (fun _ => (1 : ℝ))) volume := by
    intro n
    exact (measurable_const.indicator (hU n).isCompact.measurableSet).aestronglyMeasurable
  have hbound : Integrable (B.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hB.measurableSet).mpr (integrableOn_const hB.measure_ne_top)
  have hdom : ∀ n, ∀ᵐ p : Plane ∂volume,
      ‖(U n).indicator (fun _ => (1 : ℝ)) p‖ ≤ B.indicator (fun _ => (1 : ℝ)) p := by
    intro n
    apply Eventually.of_forall
    intro p
    by_cases hp : p ∈ U n
    · simp only [indicator_of_mem hp, indicator_of_mem (hsub n hp), norm_one, le_refl]
    · by_cases hpB : p ∈ B <;> simp [hp, hpB]
  have hlim := tendsto_integral_of_dominated_convergence (B.indicator (fun _ => (1 : ℝ)))
    hmeas hbound hdom (h.indicator_tendsto_ae hU hK)
  have hArea (n : ℕ) := integral_indicator_one (μ := (volume : Measure Plane))
    (hU n).isCompact.measurableSet
  simpa only [hArea,
    integral_indicator_one hK.isCompact.measurableSet] using hlim

end AmbidextrousSofa
