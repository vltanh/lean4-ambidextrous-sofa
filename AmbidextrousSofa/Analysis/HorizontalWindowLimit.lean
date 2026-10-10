module

public import AmbidextrousSofa.Analysis.HorizontalCutoff

@[expose] public section

/-!
# Spatial domination away from an actual top segment

Above the strict interior of an actual top segment, a supporting normal
of a Hausdorff-nearby cap must approach the top normal. A selected outer
source separated from that normal therefore disappears there. Elsewhere
its horizontal density is at most one. Dominated convergence gives an
upper envelope whose integral tends to the ordinary length of the moving
window outside the top segment. No continuity of individual facet lengths
or top atoms is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

open FinitePolygon

def topRemovedWindowEnvelope (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (l r a b : ℝ) (x : ℝ) : ℝ :=
  (Icc l r).indicator (fun x =>
    if x ∈ Ioo a b then horizontalOuterDensity U grid E x else 1) x

theorem measurable_topRemovedWindowEnvelope (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (l r a b : ℝ) :
    Measurable (topRemovedWindowEnvelope U grid E l r a b) :=
  (Measurable.ite measurableSet_Ioo (measurable_horizontalOuterDensity U grid E)
    measurable_const).indicator measurableSet_Icc

theorem topRemovedWindowEnvelope_bounds (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (l r a b x : ℝ) :
    0 ≤ topRemovedWindowEnvelope U grid E l r a b x ∧
      topRemovedWindowEnvelope U grid E l r a b x ≤ (Icc l r).indicator (fun _ => 1) x := by
  by_cases hx : x ∈ Icc l r
  · rw [topRemovedWindowEnvelope, indicator_of_mem hx, indicator_of_mem hx]
    by_cases htop : x ∈ Ioo a b
    · rw [if_pos htop]
      exact horizontalOuterDensity_bounds U grid E x
    · simp only [if_neg htop, zero_le_one, le_refl, and_self]
  · simp only [topRemovedWindowEnvelope, indicator_of_notMem hx, le_refl, and_self]

theorem integrable_topRemovedWindowEnvelope (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (l r a b : ℝ) :
    Integrable (topRemovedWindowEnvelope U grid E l r a b) volume := by
  have hB : Integrable ((Icc l r).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  apply Integrable.mono' hB (measurable_topRemovedWindowEnvelope U grid E l r a b).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (topRemovedWindowEnvelope_bounds U grid E l r a b x).1]
    exact (topRemovedWindowEnvelope_bounds U grid E l r a b x).2)

theorem integral_horizontalOuterDensity_le_envelope (U : Set Plane)
    (grid : Finset QuarterAngle) (E : Set ℝ) {l r : ℝ} (hlr : l ≤ r) (a b : ℝ) :
    (∫ x in l..r, horizontalOuterDensity U grid E x) ≤
      ∫ x : ℝ, topRemovedWindowEnvelope U grid E l r a b x := by
  have hleft : Integrable ((Icc l r).indicator (horizontalOuterDensity U grid E)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mp
        (intervalIntegrable_horizontalOuterDensity U grid E l r))
  rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_mono hleft (integrable_topRemovedWindowEnvelope U grid E l r a b)
  intro x
  by_cases hx : x ∈ Icc l r
  · rw [indicator_of_mem hx, topRemovedWindowEnvelope, indicator_of_mem hx]
    by_cases htop : x ∈ Ioo a b
    · simp only [if_pos htop, le_refl]
    · simpa only [if_neg htop] using (horizontalOuterDensity_bounds U grid E x).2
  · simp only [indicator_of_notMem hx, topRemovedWindowEnvelope, le_refl]

theorem topRemovedWindowEnvelope_tendsto_ae
    {U : ℕ → Set Plane} {K : Set Plane} {grid : ℕ → Finset QuarterAngle}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n)))
    {a b τ : ℝ} {E : Set ℝ} (ha : (a, 1) ∈ K) (hb : (b, 1) ∈ K)
    (hheight : capHeight K = 1) (hτ : 0 < τ)
    (hE : ∀ t ∈ E, 0 ≤ Real.sin t ∧ τ ≤ |Real.cos t|)
    {l r : ℕ → ℝ} {l₀ r₀ : ℝ}
    (hl : Tendsto l atTop (𝓝 l₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hwindow : ∀ n, Icc (l n) (r n) ⊆ horizontalProjection (U n)) :
    ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => topRemovedWindowEnvelope (U n) (grid n) E (l n) (r n) a b x)
        atTop (𝓝 ((Icc l₀ r₀ \ Ioo a b).indicator (fun _ => 1) x)) := by
  have hface : support K (-(0 : ℝ), 1) = 1 := by simpa only [neg_zero, capHeight] using hheight
  filter_upwards [eventually_mem_Icc_iff_ae_of_tendsto hl hr] with x hmem
  by_cases hx : x ∈ Icc l₀ r₀
  · by_cases htop : x ∈ Ioo a b
    · have hno := h.eventually_no_middle_edge hU hK
        (m := 0) (c := 1) (by simpa using ha) (by simpa using hb) hface htop hτ
        (fun t ht => by simpa only [zero_mul, add_zero] using hE t ht)
      have hzero : ∀ᶠ n in atTop,
          topRemovedWindowEnvelope (U n) (grid n) E (l n) (r n) a b x = 0 := by
        filter_upwards [hmem, hno] with n hn hno
        have hxN := hn.mpr hx
        rw [topRemovedWindowEnvelope, indicator_of_mem hxN, if_pos htop]
        exact horizontalOuterDensity_eq_zero_of_no_edge (hU n) (grid n) (hpoly n)
          E (hwindow n hxN) hno
      have hxout : x ∉ Icc l₀ r₀ \ Ioo a b := fun hm => hm.2 htop
      rw [indicator_of_notMem hxout]
      exact tendsto_const_nhds.congr' (hzero.mono fun _ hn => hn.symm)
    · rw [indicator_of_mem (show x ∈ Icc l₀ r₀ \ Ioo a b from ⟨hx, htop⟩)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hmem] with n hn
      simp only [topRemovedWindowEnvelope, indicator_of_mem (hn.mpr hx), if_neg htop]
  · have hxout : x ∉ Icc l₀ r₀ \ Ioo a b := fun hm => hx hm.1
    rw [indicator_of_notMem hxout]
    apply tendsto_const_nhds.congr'
    filter_upwards [hmem] with n hn
    have hxN : x ∉ Icc (l n) (r n) := fun hm => hx (hn.mp hm)
    simp only [topRemovedWindowEnvelope, indicator_of_notMem hxN]

theorem integral_topRemovedWindowEnvelope_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} {grid : ℕ → Finset QuarterAngle}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (hpoly : ∀ n, U n = circumscription (U n) (normal (grid n)))
    {a b τ : ℝ} {E : Set ℝ} (ha : (a, 1) ∈ K) (hb : (b, 1) ∈ K)
    (hheight : capHeight K = 1) (hτ : 0 < τ)
    (hE : ∀ t ∈ E, 0 ≤ Real.sin t ∧ τ ≤ |Real.cos t|)
    {l r : ℕ → ℝ} {l₀ r₀ L R : ℝ}
    (hl : Tendsto l atTop (𝓝 l₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hwindow : ∀ n, Icc (l n) (r n) ⊆ horizontalProjection (U n))
    (hbox : ∀ n, Icc (l n) (r n) ⊆ Icc L R) :
    Tendsto (fun n => ∫ x : ℝ, topRemovedWindowEnvelope (U n) (grid n) E
        (l n) (r n) a b x) atTop (𝓝 (volume.real (Icc l₀ r₀ \ Ioo a b))) := by
  have hB : Integrable ((Icc L R).indicator (fun _ : ℝ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hdom : ∀ n, ∀ᵐ x : ℝ ∂volume,
      ‖topRemovedWindowEnvelope (U n) (grid n) E (l n) (r n) a b x‖ ≤
        (Icc L R).indicator (fun _ => 1) x := by
    intro n
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (topRemovedWindowEnvelope_bounds (U n) (grid n) E
      (l n) (r n) a b x).1]
    by_cases hx : x ∈ Icc (l n) (r n)
    · simpa only [indicator_of_mem hx, indicator_of_mem (hbox n hx)] using
        (topRemovedWindowEnvelope_bounds (U n) (grid n) E (l n) (r n) a b x).2
    · rw [topRemovedWindowEnvelope, indicator_of_notMem hx]
      exact indicator_nonneg (fun _ _ => zero_le_one) x
  have hlim := topRemovedWindowEnvelope_tendsto_ae h hU hK hpoly ha hb hheight hτ hE
    hl hr hwindow
  have hIntegral := tendsto_integral_of_dominated_convergence
    ((Icc L R).indicator (fun _ : ℝ => (1 : ℝ)))
    (fun n => (measurable_topRemovedWindowEnvelope (U n) (grid n) E
      (l n) (r n) a b).aestronglyMeasurable) hB hdom hlim
  simpa only [integral_indicator_const (1 : ℝ) (measurableSet_Icc.diff measurableSet_Ioo),
    smul_eq_mul, mul_one] using hIntegral

end AngularGrid

end AmbidextrousSofa
