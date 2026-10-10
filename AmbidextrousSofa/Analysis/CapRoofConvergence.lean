module

public import AmbidextrousSofa.Analysis.CapVolumeContinuity
public import AmbidextrousSofa.Measure.CapScore

@[expose] public section

/-!
# Almost-everywhere convergence of actual cap roofs

Fubini passes planar indicator convergence to almost every vertical line.
The unit strip supplies a single integrable bound on each such line. The
fiber integral is the actual roof, including its zero extension off the
projection. No strict convexity or positive limiting width is required.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem IsDownwardCap.integral_vertical_indicator {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) :
    (∫ y : ℝ, U.indicator (fun _ => (1 : ℝ)) (x, y)) = capRoof U x := by
  change (∫ y : ℝ, (verticalFiber U x).indicator (1 : ℝ → ℝ) y) = capRoof U x
  rw [integral_indicator_one (isCompact_verticalFiber hU.isCompact x).measurableSet]
  by_cases hx : x ∈ horizontalProjection U
  · rw [hU.verticalFiber_eq_Icc hx, Real.volume_real_Icc_of_le
      (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x), sub_zero]
  · have hempty : verticalFiber U x = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      exact fun hne => hx (verticalFiber_nonempty_iff.mp hne)
    rw [hempty, measureReal_empty, capRoof_eq_zero_of_not_mem hx]

theorem CapHausdorffTendsto.capRoof_tendsto_ae
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    ∀ᵐ x : ℝ ∂volume, Tendsto (fun n => capRoof (U n) x) atTop (𝓝 (capRoof K x)) := by
  have hprod : ∀ᵐ p : Plane ∂volume.prod volume,
      Tendsto (fun n => (U n).indicator (fun _ => (1 : ℝ)) p)
        atTop (𝓝 (K.indicator (fun _ => (1 : ℝ)) p)) := by
    simpa only [← Measure.volume_eq_prod] using h.indicator_tendsto_ae hU hK
  filter_upwards [Measure.ae_ae_of_ae_prod hprod] with x hx
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun y : ℝ => (U n).indicator (fun _ => (1 : ℝ)) (x, y)) volume := by
    intro n
    exact ((measurable_const.indicator (hU n).isCompact.measurableSet).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hbound : Integrable ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hdom : ∀ n, ∀ᵐ y : ℝ ∂volume,
      ‖(U n).indicator (fun _ => (1 : ℝ)) (x, y)‖ ≤
        (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) y := by
    intro n
    apply Eventually.of_forall
    intro y
    by_cases hp : (x, y) ∈ U n
    · simp only [indicator_of_mem hp,
        indicator_of_mem (show y ∈ Icc (0 : ℝ) 1 from (hU n).inStrip hp), norm_one, le_refl]
    · by_cases hy : y ∈ Icc (0 : ℝ) 1 <;> simp [hp, hy]
  have hlim := tendsto_integral_of_dominated_convergence
    ((Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) hmeas hbound hdom hx
  have hFiber (n : ℕ) := (hU n).integral_vertical_indicator x
  simpa only [hFiber,
    IsDownwardCap.integral_vertical_indicator hK x] using hlim

/-- Away from the limiting endpoints, membership in a moving closed interval
eventually agrees with membership in the limiting interval. -/
theorem eventually_mem_Icc_iff_of_tendsto {a b : ℕ → ℝ} {l r x : ℝ}
    (ha : Tendsto a atTop (𝓝 l)) (hb : Tendsto b atTop (𝓝 r))
    (hxl : x ≠ l) (hxr : x ≠ r) :
    ∀ᶠ n in atTop, (x ∈ Icc (a n) (b n) ↔ x ∈ Icc l r) := by
  by_cases hx : x ∈ Icc l r
  · have hl : l < x := lt_of_le_of_ne hx.1 hxl.symm
    have hr : x < r := lt_of_le_of_ne hx.2 hxr
    filter_upwards [ha.eventually (Iio_mem_nhds hl), hb.eventually (Ioi_mem_nhds hr)] with n hn hm
    exact iff_of_true ⟨hn.le, hm.le⟩ hx
  · by_cases hl : x < l
    · filter_upwards [ha.eventually (Ioi_mem_nhds hl)] with n hn
      exact iff_of_false (fun hmem => hn.not_ge hmem.1) hx
    · have hr : r < x := by
        by_contra hnot
        exact hx ⟨le_of_not_gt hl, le_of_not_gt hnot⟩
      filter_upwards [hb.eventually (Iio_mem_nhds hr)] with n hn
      exact iff_of_false (fun hmem => hn.not_ge hmem.2) hx

theorem eventually_mem_Icc_iff_ae_of_tendsto {a b : ℕ → ℝ} {l r : ℝ}
    (ha : Tendsto a atTop (𝓝 l)) (hb : Tendsto b atTop (𝓝 r)) :
    ∀ᵐ x : ℝ ∂volume, ∀ᶠ n in atTop,
      (x ∈ Icc (a n) (b n) ↔ x ∈ Icc l r) := by
  have hl : ∀ᵐ x : ℝ ∂volume, x ≠ l := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton l : volume {l} = 0))
  have hr : ∀ᵐ x : ℝ ∂volume, x ≠ r := by
    simpa only [mem_singleton_iff] using
      (measure_eq_zero_iff_ae_notMem.mp (measure_singleton r : volume {r} = 0))
  filter_upwards [hl, hr] with x hxl hxr
  exact eventually_mem_Icc_iff_of_tendsto ha hb hxl hxr

theorem CapHausdorffTendsto.projection_membership_ae
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    ∀ᵐ x : ℝ ∂volume, ∀ᶠ n in atTop,
      (x ∈ Icc (horizontalLeft (U n)) (horizontalRight (U n)) ↔
        x ∈ Icc (horizontalLeft K) (horizontalRight K)) :=
  eventually_mem_Icc_iff_ae_of_tendsto
    (h.horizontalLeft_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
      hK.isCompact hK.nonempty)
    (h.horizontalRight_tendsto (fun n => (hU n).isCompact) (fun n => (hU n).nonempty)
      hK.isCompact hK.nonempty)

theorem CapHausdorffTendsto.middle_membership_ae
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K) :
    ∀ᵐ x : ℝ ∂volume, ∀ᶠ n in atTop,
      (x ∈ middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) ↔
        x ∈ middleHalfInterval (horizontalLeft K) (horizontalRight K)) := by
  have hl := h.horizontalLeft_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  have hr := h.horizontalRight_tendsto (fun n => (hU n).isCompact)
    (fun n => (hU n).nonempty) hK.isCompact hK.nonempty
  exact eventually_mem_Icc_iff_ae_of_tendsto
    (hl.add ((hr.sub hl).div_const 4)) (hr.sub ((hr.sub hl).div_const 4))

end AmbidextrousSofa
