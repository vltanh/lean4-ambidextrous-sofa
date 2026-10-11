module

public import AmbidextrousSofa.Analysis.JointSourceFlux

@[expose] public section

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
  rintro z ⟨hx, j, hθ, -⟩
  have hw : 0 ≤ capWidth (J.caps n) := sub_nonneg.mpr
    (horizontalLeft_le_horizontalRight (J.isCap n).nonempty (J.isCap n).isCompact)
  exact ⟨hθ ▸ Ioo_subset_Icc_self (fullAngle_mem _ j),
    (J.isCap n).projection_subset_Icc_of_box (J.selected n).inBox
      ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩

theorem ae_zero_of_source_limits
    {f : Plane → ℝ} (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    (hzero : ∀ (seq : ℕ → ℕ), Tendsto seq atTop atTop →
      ∀ (point : ℕ → Plane), (∀ n, point n ∈ J.finiteSourceTags (seq n)) →
      ∀ z : Plane, Tendsto point atTop (𝓝 z) → f z = 0) :
    ∀ᵐ z ∂(J.measure : Measure Plane), f z = 0 := by
  -- Compactness of the source box: eventually every tag has a small error.
  have hsmall {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ z ∈ J.finiteSourceTags n, f z < ε := by
    by_contra hnot
    rw [not_eventually, frequently_atTop] at hnot
    push Not at hnot
    choose ns hns point hpoint hlarge using hnot
    obtain ⟨z, -, ms, hms, hlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq
      fun n => J.finiteSourceTags_subset_box (ns n) (hpoint n)
    have := ge_of_tendsto ((hf.tendsto z).comp hlim) (.of_forall fun n => hlarge (ms n))
    linarith [hzero _ ((tendsto_atTop_mono hns tendsto_id).comp hms.tendsto_atTop) _
      (fun n => hpoint (ms n)) z hlim]
  have hbound (k : ℕ) : ∀ᵐ z ∂(J.measure : Measure Plane), f z ≤ selectionRate k := by
    have hE := isClosed_le hf (continuous_const (y := selectionRate k))
    have hreal : (J.measure : Measure Plane).real {z | f z ≤ selectionRate k}ᶜ ≤ 0 := by
      refine finiteMeasure_real_open_le_of_tendsto_bound J.converges hE.isOpen_compl le_rfl
        tendsto_const_nhds ?_
      filter_upwards [(hsmall (selectionRate_pos k)).filter_mono sourceLimitFilter_le_atTop]
        with n hn
      rw [innerJointFiniteMeasure, FiniteMeasure.toMeasure_mk, measureReal_def,
        innerJointMeasure_compl_eq_zero_of_source _ _ _ _ hE.measurableSet
          fun j x hx hs => (hn (fullAngle _ j, x) ⟨hx, j, rfl, hs⟩).le, ENNReal.toReal_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp ((measureReal_eq_zero_iff
      (measure_ne_top _ _)).mp (hreal.antisymm measureReal_nonneg))] with z hz
    exact not_not.1 hz
  filter_upwards [ae_all_iff.mpr hbound] with z hz
  exact le_antisymm (ge_of_tendsto selectionRate_tendsto (.of_forall hz)) (hf0 z)

/-- In particular, the moving physical middle interval leaves no mass
outside its actual limiting closed interval. -/
theorem ae_spatial_mem_middle (hTarget : IsDownwardCap target) :
    ∀ᵐ z ∂(J.measure : Measure Plane),
      z.2 ∈ Icc (horizontalLeft target + capWidth target / 4)
        (horizontalRight target - capWidth target / 4) := by
  set L := horizontalLeft target + capWidth target / 4
  set R := horizontalRight target - capWidth target / 4
  have hzero := J.ae_zero_of_source_limits (f := fun z => max (max (L - z.2) (z.2 - R)) 0)
    (by fun_prop) (fun _ => le_max_right _ _) fun seq hseq point hpoint z hz => by
      have hl := (J.hausdorff.horizontalLeft_tendsto (fun n => (J.isCap n).isCompact)
        (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty).comp hseq
      have hr := (J.hausdorff.horizontalRight_tendsto (fun n => (J.isCap n).isCompact)
        (fun n => (J.isCap n).nonempty) hTarget.isCompact hTarget.nonempty).comp hseq
      have hw := ((J.hausdorff.capWidth_tendsto J.isCap hTarget).div_const 4).comp hseq
      refine max_eq_right (max_le (sub_nonpos.2 ?_) (sub_nonpos.2 ?_))
      · exact le_of_tendsto_of_tendsto (hl.add hw) hz.snd_nhds
          (.of_forall fun n => (hpoint n).1.1.le)
      · exact le_of_tendsto_of_tendsto hz.snd_nhds (hr.sub hw)
          (.of_forall fun n => (hpoint n).1.2)
  filter_upwards [hzero] with z hz
  have h := max_le_iff.1 (max_eq_right_iff.1 hz)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end SelectedJointSourceLimit
end AngularGrid
end AmbidextrousSofa
