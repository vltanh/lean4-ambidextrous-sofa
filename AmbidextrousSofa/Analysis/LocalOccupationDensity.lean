module

public import AmbidextrousSofa.Analysis.VisibleFluxDensity
public import AmbidextrousSofa.Analysis.RegularCorner

@[expose] public section

/-!
# Saturation from local interval occupation

A lower bound for every short image increment gives the reverse
inequality to graph-projection domination. Differentiating the actual
integral at its Lebesgue points proves equality of the occupation and
the graph velocity. No strict monotonicity assumption is needed, so
zero-speed plateaus are retained.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem ae_eq_deriv_of_local_interval_occupation
    {S : Set ℝ} {X XD w : ℝ → ℝ}
    (hS : IsOpen S) (hw : Integrable w volume)
    (hD : ∀ᵐ t ∂volume.restrict S, HasDerivAt X (XD t) t)
    (hupper : ∀ᵐ t ∂volume.restrict S, w t ≤ XD t)
    (hlower : ∀ s r : ℝ, s < r → Icc s r ⊆ S →
      X r - X s ≤ ∫ t in s..r, w t) :
    ∀ᵐ t ∂volume.restrict S, w t = XD t := by
  filter_upwards [ae_restrict_mem hS.measurableSet, hD, hupper,
    ae_restrict_of_ae (LocallyIntegrable.ae_hasDerivAt_integral hw.locallyIntegrable)]
    with t ht hd hu hLeb
  apply le_antisymm hu
  obtain ⟨l, r, hti, hsub⟩ := exists_closed_interval_within_open hS ht
  let d : ℕ → ℝ := AngularGrid.selectionRate
  have hd0 : Tendsto d atTop (𝓝 0) := AngularGrid.selectionRate_tendsto
  have hdpos : ∀ n, 0 < d n := AngularGrid.selectionRate_pos
  have hsmall : ∀ᶠ n in atTop, t + d n < r := by
    filter_upwards [hd0.eventually (Iio_mem_nhds (sub_pos.mpr hti.2))] with n hn
    linarith only [hn]
  have hXlim := HasDerivAt.forward_increment_div_tendsto hd hd0 hdpos
  have hwlim : Tendsto (fun n => (∫ s in t..t + d n, w s) / d n)
      atTop (𝓝 (w t)) := by
    simpa only [intervalIntegral.integral_same, sub_zero] using
      HasDerivAt.forward_increment_div_tendsto (hLeb t) hd0 hdpos
  apply le_of_tendsto_of_tendsto hXlim hwlim
  filter_upwards [hsmall] with n hn
  apply div_le_div_of_nonneg_right _ (hdpos n).le
  apply hlower t (t + d n) (by linarith only [hdpos n])
  intro x hx
  exact hsub ⟨hti.1.le.trans hx.1, hx.2.trans hn.le⟩

end AmbidextrousSofa
