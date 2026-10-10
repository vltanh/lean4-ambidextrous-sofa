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
open scoped Topology

namespace AmbidextrousSofa
namespace PartialGrid

open FinitePolygon AngularGrid

variable {α : TerminalAngle} {hαL : (α : ℝ) < Real.pi / 2}

theorem scaled_innerSource_corner_height_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : AngularGrid.SourceIndex grid) {x : ℝ}
    (hx : x ∈ innerSourceSet U α hαL grid (scaledSource α grid j)) :
    0 ≤ sourceCornerHeight U (fullAngle α grid (scaledSource α grid j)) := by
  cases j with
  | inl t =>
    have ht := scaleAngle_mem_open α (interiorPoint_mem grid t)
    have htL : (scaleAngle α t.val : ℝ) < Real.pi / 2 := ht.2.trans hαL
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [htL, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], htL⟩
    have hsource := innerSource_height U α hαL grid (scaledSource α grid (Sum.inl t)) hx
    have hcomp := first_source_le_companion U α hαL grid t hx
    change finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x =
      supportWall U (unitNormal (scaleAngle α t.val)) x at hsource
    rw [supportWall_unitNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    rw [sourceCornerHeight, sourceQuarterAngle_scaledSource]
    change 0 ≤ (attachedCorner U (scaleAngle α t.val)).2
    calc
      0 ≤ finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x :=
        finiteBarrier_nonneg U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x
      _ = firstWall U (scaleAngle α t.val) x := hsource
      _ = cornerWall U (scaleAngle α t.val) x := (min_eq_left hcomp).symm
      _ ≤ _ := cornerWall_le_attachedCorner_snd U hs hc x
  | inr t =>
    have ht := scaleAngle_mem_open α (interiorPoint_mem grid t)
    have htL : (scaleAngle α t.val : ℝ) < Real.pi / 2 := ht.2.trans hαL
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith only [htL, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith only [ht.1, Real.pi_pos], htL⟩
    have hsource := innerSource_height U α hαL grid (scaledSource α grid (Sum.inr t)) hx
    have hcomp := second_source_le_first U α hαL grid t hx
    change finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x =
      supportWall U (companionNormal (scaleAngle α t.val)) x at hsource
    rw [supportWall_companionNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    rw [sourceCornerHeight, sourceQuarterAngle_scaledSource]
    change 0 ≤ (attachedCorner U (scaleAngle α t.val)).2
    calc
      0 ≤ finiteBarrier U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x :=
        finiteBarrier_nonneg U (normal α grid) (pairList α grid) (some (terminalIndex α hαL grid)) x
      _ = secondWall U (scaleAngle α t.val) x := hsource
      _ = cornerWall U (scaleAngle α t.val) x := (min_eq_right hcomp).symm
      _ ≤ _ := cornerWall_le_attachedCorner_snd U hs hc x

theorem scaled_innerSourceSet_eq_empty_of_corner_neg (U : Set Plane)
    (grid : Finset QuarterAngle) (j : AngularGrid.SourceIndex grid)
    (hnegative : sourceCornerHeight U (fullAngle α grid (scaledSource α grid j)) < 0) :
    innerSourceSet U α hαL grid (scaledSource α grid j) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact not_lt_of_ge (scaled_innerSource_corner_height_nonneg U grid j hx) hnegative

theorem curvature_Ioc_eq_zero_of_negative_corners
    {target : Set Plane} {U : ℕ → Set Plane}
    {boxLeft boxRight R m c a b : ℝ} {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsDownwardCap target)
    (hU : ∀ n, IsSelectedPolygon target α hαL boxLeft boxRight (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hbox : ∀ n, U n ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
    (hwidth : 0 < capWidth target)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hab : a ≤ b) (hregular : Icc a b ⊆ regularProperCurvatureDomain α m)
    (ha : MovingSofaOptimality.sigmaAt target a = 0) (hb : MovingSofaOptimality.sigmaAt target b = 0)
    (hnegative : ∀ θ ∈ Icc a b, sourceCornerHeight target θ < 0) :
    upperCurvature target (Ioc a b) = 0 := by
  have htop : Real.pi / 2 ∉ Icc a b := by
    intro ht
    exact (mem_regularCurvatureDomain_iff.mp (hregular ht).1).2.2.1 rfl
  have hevent := hHausdorff.eventually_sourceCornerHeight_neg_on_compact
    (fun n => (hU n).isCap) hTarget isCompact_Icc htop hnegative
  have hbound := curvature_Ioc_le_of_eventual_sampled_atom_bound
    hTarget hU hHausdorff hlevel hc hrate hbox hwidth haffine
    (C := 0) le_rfl hab hregular ha hb (by
      filter_upwards [hevent] with n hn
      intro j hj
      have hzero := scaled_innerSourceSet_eq_empty_of_corner_neg (hαL := hαL) (U n) (dyadic (level n)) j
        (hn _ hj)
      simpa only [zero_mul, zero_add] using
        (hU n).curvature_atom_le_error_of_source_empty (hc n) _ hzero)
  have hreal : (upperCurvature target).real (Ioc a b) = 0 :=
    le_antisymm (by simpa only [zero_mul] using hbound) ENNReal.toReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset Ioc_subset_Icc_self
    (isCompact_Icc.measure_ne_top (μ := upperCurvature target)))).mp hreal

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
  let R := |horizontalLeft U| + |horizontalRight U| + 1
  let β : TerminalAngle := ⟨α, hU.angle_mem⟩
  have hR : 0 ≤ R := by positivity
  have hbox : U ⊆ Icc (-R) R ×ˢ Icc (0 : ℝ) 1 := by
    apply subset_symmetricBox_of_horizontalBox
    intro p hp
    refine ⟨?_, hU.isCap.inStrip hp⟩
    rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
    exact ⟨p, hp, rfl⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    PartialGrid.exists_selected_sequence β hproper hU
      (by linarith only [hR] : -R ≤ R) hbox
  exact PartialGrid.curvature_Ioc_eq_zero_of_negative_corners hU.isCap hV hHausdorff
    (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate
    (fun n => (hV n).inBox) (by linarith only [hU.width_bounds.1, one_lt_M]) haffine
    hab hregular
    (hU.sigmaAt_eq_zero_on_regular_proper_domain hproper haffine (hregular ⟨le_rfl, hab⟩))
    (hU.sigmaAt_eq_zero_on_regular_proper_domain hproper haffine (hregular ⟨hab, le_rfl⟩))
    hnegative

/-- Local null neighborhoods cover arbitrary negative-corner sets;
there is no finite-component or switching assumption. -/
theorem IsJointCapMaximizer.upperCurvature_proper_negative_corners_eq_zero
    {U : Set Plane} {α m c : ℝ} (hU : IsJointCapMaximizer U α)
    (hproper : α < Real.pi / 2)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U {θ ∈ regularProperCurvatureDomain α m | sourceCornerHeight U θ < 0} = 0 := by
  apply measure_null_of_locally_null _
  intro x hx
  have htop := (mem_regularCurvatureDomain_iff.mp hx.1.1).2.2.1
  have hneg : ∀ᶠ θ in 𝓝 x, sourceCornerHeight U θ < 0 :=
    (continuousAt_sourceCornerHeight hU.isCap.isCompact htop).tendsto.eventually_lt_const hx.2
  have hnhds : {θ ∈ regularProperCurvatureDomain α m | sourceCornerHeight U θ < 0} ∈ 𝓝 x :=
    inter_mem ((isOpen_regularProperCurvatureDomain α m).mem_nhds hx.1) hneg
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  let a := (l + x) / 2
  let b := (x + r) / 2
  have hax : a < x := by dsimp only [a]; linarith only [hl]
  have hxb : x < b := by dsimp only [b]; linarith only [hr]
  have hab : a ≤ b := (hax.trans hxb).le
  have habsub : Icc a b ⊆
      {θ ∈ regularProperCurvatureDomain α m | sourceCornerHeight U θ < 0} := by
    intro θ hθ
    apply hsub
    constructor <;> dsimp only [a, b] at hθ <;> linarith only [hθ.1, hθ.2, hl, hr]
  refine ⟨Ioc a b, nhdsWithin_le_nhds ?_, ?_⟩
  · exact mem_of_superset (Ioo_mem_nhds hax hxb) Ioo_subset_Ioc_self
  · exact hU.upperCurvature_proper_Ioc_eq_zero_of_negative_corners hproper haffine hab
      (fun θ hθ => (habsub hθ).1) (fun θ hθ => (habsub hθ).2)

end AmbidextrousSofa
