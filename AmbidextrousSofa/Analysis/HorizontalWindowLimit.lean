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

theorem norm_topRemovedWindowEnvelope_le (U : Set Plane) (grid : Finset QuarterAngle)
    (E : Set ℝ) (l r a b x : ℝ) :
    ‖topRemovedWindowEnvelope U grid E l r a b x‖ ≤ (Icc l r).indicator (fun _ => 1) x := by
  obtain ⟨h0, h1⟩ := horizontalOuterDensity_bounds U grid E x
  rw [topRemovedWindowEnvelope, norm_indicator_eq_indicator_norm]
  refine indicator_le_indicator ?_
  split_ifs <;> simp [abs_of_nonneg h0, h1]

theorem integral_horizontalOuterDensity_le_envelope (U : Set Plane)
    (grid : Finset QuarterAngle) (E : Set ℝ) {l r : ℝ} (hlr : l ≤ r) (a b : ℝ) :
    (∫ x in l..r, horizontalOuterDensity U grid E x) ≤
      ∫ x : ℝ, topRemovedWindowEnvelope U grid E l r a b x := by
  have hint : Integrable (topRemovedWindowEnvelope U grid E l r a b) :=
    (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).mono'
      (measurable_topRemovedWindowEnvelope U grid E l r a b).aestronglyMeasurable
      (ae_of_all _ (norm_topRemovedWindowEnvelope_le U grid E l r a b))
  rw [intervalIntegral.integral_of_le hlr, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  refine integral_mono (((intervalIntegrable_iff_integrableOn_Icc_of_le hlr).mp
    (intervalIntegrable_horizontalOuterDensity U grid E l r)).integrable_indicator
    measurableSet_Icc) hint fun x => indicator_le_indicator ?_
  split_ifs
  exacts [le_rfl, (horizontalOuterDensity_bounds U grid E x).2]

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
  have hface : support K (-(0 : ℝ), 1) = 1 := by simpa only [neg_zero, capHeight] using hheight
  have hlim : ∀ᵐ x : ℝ ∂volume,
      Tendsto (fun n => topRemovedWindowEnvelope (U n) (grid n) E (l n) (r n) a b x)
        atTop (𝓝 ((Icc l₀ r₀ \ Ioo a b).indicator (fun _ => 1) x)) := by
    filter_upwards [eventually_mem_Icc_iff_ae_of_tendsto hl hr] with x hmem
    refine tendsto_const_nhds.congr' ?_
    by_cases htop : x ∈ Ioo a b
    · filter_upwards [h.eventually_no_middle_edge hU hK (m := 0) (c := 1) (by simpa using ha)
        (by simpa using hb) hface htop hτ (fun t ht => by simpa using hE t ht)] with n hno
      rw [indicator_of_notMem (fun hm => hm.2 htop), topRemovedWindowEnvelope]
      by_cases hxN : x ∈ Icc (l n) (r n)
      · rw [indicator_of_mem hxN, ite_eq_left htop, horizontalOuterDensity_eq_zero_of_no_edge
          (hU n) (grid n) (hpoly n) E (hwindow n hxN) hno]
      · rw [indicator_of_notMem hxN]
    · filter_upwards [hmem] with n hn
      simp only [topRemovedWindowEnvelope, indicator_apply, Set.mem_sdiff, htop, hn, ite_false,
        not_false_eq_true, and_true]
  simpa only [integral_indicator_const (1 : ℝ) (measurableSet_Icc.diff measurableSet_Ioo),
    smul_eq_mul, mul_one] using tendsto_integral_of_dominated_convergence
      ((Icc L R).indicator (fun _ : ℝ => (1 : ℝ)))
      (fun n => (measurable_topRemovedWindowEnvelope (U n) (grid n) E
        (l n) (r n) a b).aestronglyMeasurable)
      (continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc)
      (fun n => ae_of_all _ fun x => (norm_topRemovedWindowEnvelope_le _ _ _ _ _ _ _ x).trans
        (indicator_le_indicator_of_subset (hbox n) (fun _ => zero_le_one) x)) hlim

end AngularGrid

end AmbidextrousSofa
