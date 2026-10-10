import AmbidextrousSofa.Analysis.JointSourceFlux

/-!
# Passing literal source contact equations to the joint limit

The tags below retain both the sampled normal and the physical source
abscissa. A continuous nonnegative error which vanishes at every limit
of these actual tags vanishes almost everywhere for the common weak
limit. Compactness is used on the literal fixed source box, and the open
set inequality for finite measures passes the conclusion through the
already selected common filter.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa
namespace AngularGrid
namespace SelectedJointSourceLimit

variable {target : Set Plane} {a b : ℝ} (J : SelectedJointSourceLimit target a b)

def finiteSourceTags (n : ℕ) : Set Plane :=
  {z | z.2 ∈ Ioc (horizontalLeft (J.caps n) + capWidth (J.caps n) / 4)
      (horizontalRight (J.caps n) - capWidth (J.caps n) / 4) ∧
    ∃ j : SourceIndex (dyadic (J.level n)),
      z.1 = fullAngle (dyadic (J.level n)) j ∧
        z.2 ∈ innerSourceSet (J.caps n) (dyadic (J.level n)) j}

theorem finiteSourceTags_subset_box (n : ℕ) :
    J.finiteSourceTags n ⊆ Icc (0 : ℝ) Real.pi ×ˢ Icc a b := by
  rintro z ⟨hx, j, hθ, _hsource⟩
  have hw : 0 ≤ capWidth (J.caps n) := by
    unfold capWidth
    exact sub_nonneg.mpr (horizontalLeft_le_horizontalRight
      (J.isCap n).nonempty (J.isCap n).isCompact)
  refine ⟨?_, (J.isCap n).projection_subset_Icc_of_box (J.selected n).inBox ?_⟩
  · rw [hθ]
    exact Ioo_subset_Icc_self (fullAngle_mem _ j)
  · constructor <;> linarith only [hx.1, hx.2, hw]

theorem eventually_source_values_lt
    {f : Plane → ℝ} (hf : Continuous f)
    (hzero : ∀ (seq : ℕ → ℕ), Tendsto seq atTop atTop →
      ∀ (point : ℕ → Plane), (∀ n, point n ∈ J.finiteSourceTags (seq n)) →
      ∀ z : Plane, Tendsto point atTop (𝓝 z) → f z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z ∈ J.finiteSourceTags n, f z < ε := by
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n, k ≤ n ∧ ∃ z ∈ J.finiteSourceTags n, ¬ f z < ε := by
    intro k
    by_contra hk
    apply hnot
    refine eventually_atTop.mpr ⟨k, ?_⟩
    intro n hn z hz
    by_contra hlarge
    exact hk ⟨n, hn, z, hz, hlarge⟩
  choose ns hns point hpoint hlarge using hbad
  have hbox : ∀ n, point n ∈ Icc (0 : ℝ) Real.pi ×ˢ Icc a b :=
    fun n => J.finiteSourceTags_subset_box (ns n) (hpoint n)
  obtain ⟨z, _hz, ms, hms, hlim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hbox
  let seq : ℕ → ℕ := fun n => ns (ms n)
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hseq : Tendsto seq atTop atTop := hnsTop.comp hms.tendsto_atTop
  have hz := hzero seq hseq (fun n => point (ms n)) (fun n => hpoint (ms n)) z hlim
  have hsmall : Tendsto (fun n => f (point (ms n))) atTop (𝓝 0) := by
    simpa only [hz] using (hf.tendsto z).comp hlim
  have hle : ε ≤ 0 := ge_of_tendsto hsmall
    (Eventually.of_forall (fun n => le_of_not_gt (hlarge (ms n))))
  exact not_le_of_gt hε hle

theorem ae_zero_of_source_limits
    {f : Plane → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    (hzero : ∀ (seq : ℕ → ℕ), Tendsto seq atTop atTop →
      ∀ (point : ℕ → Plane), (∀ n, point n ∈ J.finiteSourceTags (seq n)) →
      ∀ z : Plane, Tendsto point atTop (𝓝 z) → f z = 0) :
    ∀ᵐ z ∂(J.measure : Measure Plane), f z = 0 := by
  have hbound (k : ℕ) : ∀ᵐ z ∂(J.measure : Measure Plane), f z ≤ selectionRate k := by
    have hsmall := J.eventually_source_values_lt hf hzero (selectionRate_pos k)
    have hfinite : ∀ᶠ n in atTop,
        (J.finiteMeasure n : Measure Plane) {z | selectionRate k < f z} = 0 := by
      filter_upwards [hsmall] with n hn
      have hnull := innerJointMeasure_compl_eq_zero_of_source
        (J.caps n) (dyadic (J.level n))
        (horizontalLeft (J.caps n) + capWidth (J.caps n) / 4)
        (horizontalRight (J.caps n) - capWidth (J.caps n) / 4)
        (E := {z | f z ≤ selectionRate k})
        (isClosed_le hf continuous_const).measurableSet
        (fun j x hx hsource => (hn (fullAngle (dyadic (J.level n)) j, x)
          ⟨hx, j, rfl, hsource⟩).le)
      simpa only [compl_setOf, not_le] using hnull
    have hreal : (J.measure : Measure Plane).real {z | selectionRate k < f z} ≤ 0 := by
      apply finiteMeasure_real_open_le_of_tendsto_bound J.converges
        (isOpen_lt continuous_const hf) le_rfl tendsto_const_nhds
      filter_upwards [hfinite.filter_mono sourceLimitFilter_le_atTop] with n hn
      simp only [Measure.real, hn, ENNReal.toReal_zero, le_rfl]
    have hnull : (J.measure : Measure Plane) {z | selectionRate k < f z} = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
        (le_antisymm hreal measureReal_nonneg)
    simpa only [mem_setOf_eq, not_lt] using measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [ae_all_iff.mpr hbound] with z hz
  exact le_antisymm
    (ge_of_tendsto selectionRate_tendsto (Eventually.of_forall hz)) (hf0 z)

/-- In particular, the moving physical middle interval leaves no mass
outside its actual limiting closed interval. -/
theorem ae_spatial_mem_middle (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.2 ∈ Icc (horizontalLeft target + capWidth target / 4)
        (horizontalRight target - capWidth target / 4) := by
  let f : Plane → ℝ := fun z =>
    max (horizontalLeft target + capWidth target / 4 - z.2) 0 +
      max (z.2 - (horizontalRight target - capWidth target / 4)) 0
  have hf : Continuous f := by dsimp only [f]; fun_prop
  have hf0 : ∀ z, 0 ≤ f z := fun z => add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hzero := J.ae_zero_of_source_limits hf hf0 (by
    intro seq hseq point hpoint z hz
    have hl := (J.hausdorff.horizontalLeft_tendsto (fun n => (J.isCap n).isCompact)
      (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty).comp hseq
    have hr := (J.hausdorff.horizontalRight_tendsto (fun n => (J.isCap n).isCompact)
      (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty).comp hseq
    have hw := ((J.hausdorff.capWidth_tendsto J.isCap hTarget).div_const 4).comp hseq
    have hleft : horizontalLeft target + capWidth target / 4 ≤ z.2 :=
      le_of_tendsto_of_tendsto (hl.add hw) hz.snd
        (Eventually.of_forall (fun n => (hpoint n).1.1.le))
    have hright : z.2 ≤ horizontalRight target - capWidth target / 4 :=
      le_of_tendsto_of_tendsto hz.snd (hr.sub hw)
        (Eventually.of_forall (fun n => (hpoint n).1.2))
    simp only [f, max_eq_right (sub_nonpos.mpr hleft),
      max_eq_right (sub_nonpos.mpr hright), add_zero])
  filter_upwards [hzero] with z hz
  have hleft := le_max_left (horizontalLeft target + capWidth target / 4 - z.2) 0
  have hright := le_max_left (z.2 - (horizontalRight target - capWidth target / 4)) 0
  have hleft0 := le_max_right (horizontalLeft target + capWidth target / 4 - z.2) 0
  have hright0 := le_max_right (z.2 - (horizontalRight target - capWidth target / 4)) 0
  dsimp only [f] at hz
  constructor <;> linarith

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
