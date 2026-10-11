module

public import AmbidextrousSofa.Analysis.PartialShadowCurvature

@[expose] public section

/-!
# Actual proper curvature vanishes below the floor

A sampled paired source is above the floor and below its own corner.
The unpaired whole terminal wall is excluded explicitly. Uniform strict
negativity on compact angular intervals empties every sampled source;
the actual atom inequalities and their vanishing errors then force the
limiting curvature measure to vanish there.
-/

noncomputable section

open Set Filter MeasureTheory

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

theorem scaled_innerSource_corner_height_nonneg {α : TerminalAngle}
    {hαL : (α : ℝ) < Real.pi / 2} (U : Set Plane) (grid : Finset QuarterAngle)
    (j : AngularGrid.SourceIndex grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid j)) :
    0 ≤ sourceCornerHeight U (fullAngle α grid (scaledSource α grid j)) := by
  have key (t : InteriorPoint grid) (h : 0 ≤ cornerWall U (scaleAngle α t.val) x) :
      0 ≤ (attachedCorner U (scaleAngle α t.val)).2 := by
    have ht := scaleAngle_mem_open α (interiorPoint_mem grid t)
    have htL : (scaleAngle α t.val : ℝ) < Real.pi / 2 := ht.2.trans hαL
    exact h.trans (cornerWall_le_attachedCorner_snd U
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [Real.pi_pos]))
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], htL⟩) x)
  have h0 := (finiteBarrier_nonneg U _ _ _ x).trans_eq (innerSource_height U α hαL grid _ hx)
  rw [sourceCornerHeight, sourceQuarterAngle_scaledSource]
  rcases j with t | t
  · exact key t (le_min (h0.trans_eq (supportWall_unitNormal U _ x))
      ((h0.trans (first_source_le_companion U α hαL grid t hx)).trans_eq
        (supportWall_companionNormal U _ x)))
  · exact key t (le_min ((h0.trans (second_source_le_first U α hαL grid t hx)).trans_eq
      (supportWall_unitNormal U _ x)) (h0.trans_eq (supportWall_companionNormal U _ x)))

end PartialGrid

/-- No source occupation or density bound is supplied by the caller:
the selected sequence and both endpoint non-atoms are constructed from
this actual proper maximizer. -/
theorem IsJointCapMaximizer.upperCurvature_proper_Ioc_eq_zero_of_negative_corners
    {U : Set Plane} {α m c a b : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hab : a ≤ b) (hregular : Icc a b ⊆ regularProperCurvatureDomain α m)
    (hnegative : ∀ θ ∈ Icc a b, sourceCornerHeight U θ < 0) :
    upperCurvature U (Ioc a b) = 0 := by
  have hR : 0 ≤ |horizontalLeft U| + |horizontalRight U| + 1 := by positivity
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence ⟨α, hU.angle_mem⟩ hproper hU (neg_le_self hR)
      (subset_symmetricBox_of_horizontalBox fun p hp =>
        ⟨hU.isCap.fst_mem_Icc hp, hU.isCap.inStrip hp⟩)
  have hevent := hHausdorff.eventually_sourceCornerHeight_neg_on_compact (fun n => (hV n).isCap)
    hU.isCap isCompact_Icc (fun ht => (mem_regularCurvatureDomain_iff.mp (hregular ht).1).2.2.1 rfl)
    hnegative
  have hbound := PartialGrid.curvature_Ioc_le_of_eventual_sampled_atom_bound hU.isCap hV hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate (fun n => (hV n).inBox)
    (by linarith only [hU.width_bounds.1, one_lt_M]) haffine le_rfl hab hregular
    (hU.sigmaAt_eq_zero_on_regular_proper_domain hproper haffine (hregular ⟨le_rfl, hab⟩))
    (hU.sigmaAt_eq_zero_on_regular_proper_domain hproper haffine (hregular ⟨hab, le_rfl⟩)) (by
      filter_upwards [hevent] with n hn j hj
      simpa only [zero_mul, zero_add] using
        (hV n).curvature_atom_le_error_of_source_empty (hc n).le _
        (eq_empty_iff_forall_notMem.mpr fun x hx =>
          (PartialGrid.scaled_innerSource_corner_height_nonneg (V n) _ j hx).not_gt (hn _ hj)))
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset Ioc_subset_Icc_self
    (isCompact_Icc.measure_ne_top (μ := upperCurvature U)))).mp
    (le_antisymm (by simpa only [zero_mul] using hbound) ENNReal.toReal_nonneg)

/-- Local null neighborhoods cover arbitrary negative-corner sets;
there is no finite-component or switching assumption. -/
theorem IsJointCapMaximizer.upperCurvature_proper_negative_corners_eq_zero
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U {θ ∈ regularProperCurvatureDomain α m | sourceCornerHeight U θ < 0} = 0 := by
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp <| inter_mem
    ((isOpen_regularProperCurvatureDomain α m).mem_nhds hx.1)
    ((continuousAt_sourceCornerHeight hU.isCap.isCompact
      (mem_regularCurvatureDomain_iff.mp hx.1.1).2.2.1).tendsto.eventually_lt_const hx.2)
  obtain ⟨a, hla, hax⟩ := exists_between hl
  obtain ⟨b, hxb, hbr⟩ := exists_between hr
  have habsub := (Icc_subset_Ioo hla hbr).trans hsub
  exact ⟨Ioc a b, nhdsWithin_le_nhds (Ioc_mem_nhds hax hxb),
    hU.upperCurvature_proper_Ioc_eq_zero_of_negative_corners hproper haffine (hax.trans hxb).le
      (fun θ hθ => (habsub hθ).1) (fun θ hθ => (habsub hθ).2)⟩

end AmbidextrousSofa
