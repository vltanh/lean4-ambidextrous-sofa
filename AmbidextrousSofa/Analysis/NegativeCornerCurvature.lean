module

public import AmbidextrousSofa.Analysis.SourceOccupation
public import AmbidextrousSofa.Analysis.CornerConfinement

@[expose] public section

/-!
# Actual curvature vanishes at corners below the floor

The minimum of the two inner walls never exceeds their intersection
height. A selected finite inner source is nonnegative, so its own corner
cannot lie below the floor. Strict corner negativity persists uniformly
on compact angular sets under actual cap Hausdorff convergence. The
proved finite source-occupation limit then forces the actual limiting
curvature to vanish on every regular interval of negative corners.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem cornerWall_le_attachedCorner_snd (U : Set Plane) {θ : ℝ}
    (hs : 0 < Real.sin θ) (hc : 0 < Real.cos θ) (x : ℝ) :
    cornerWall U θ x ≤ (attachedCorner U θ).2 := by
  have _ := And.intro hs hc -- not needed by the proof; they stay in the statement for the callers
  have hmean : firstWall U θ x * Real.sin θ ^ 2 + secondWall U θ x * Real.cos θ ^ 2 =
      (attachedCorner U θ).2 := by
    simp only [firstWall, secondWall, attachedCorner]
    field_simp
    ring
  rw [← hmean, cornerWall]
  linarith [mul_le_mul_of_nonneg_right (min_le_left (firstWall U θ x) (secondWall U θ x))
      (sq_nonneg (Real.sin θ)),
    mul_le_mul_of_nonneg_right (min_le_right (firstWall U θ x) (secondWall U θ x))
      (sq_nonneg (Real.cos θ)),
    congrArg (min (firstWall U θ x) (secondWall U θ x) * ·) (Real.sin_sq_add_cos_sq θ)]

/-- Both upper source normals are indexed by the angle of their own
quarter-turn corner. The top normal itself is excluded when continuity
of this fold is used. -/
def sourceQuarterAngle (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then t else t - Real.pi / 2

def sourceCornerHeight (U : Set Plane) (t : ℝ) : ℝ :=
  (attachedCorner U (sourceQuarterAngle t)).2

theorem continuousAt_sourceQuarterAngle {t : ℝ} (htop : t ≠ Real.pi / 2) :
    ContinuousAt sourceQuarterAngle t := by
  rcases htop.lt_or_gt with hlt | hgt
  · exact continuousAt_id.congr
      (eventuallyEq_of_mem (Iio_mem_nhds hlt) fun s hs => (ite_eq_left hs).symm)
  · exact (continuousAt_id.sub continuousAt_const).congr (eventuallyEq_of_mem (Ioi_mem_nhds hgt)
      fun s hs => (ite_eq_right (not_lt.mpr (le_of_lt hs))).symm)

theorem sourceQuarterAngle_tendsto {ι : Type*} {l : Filter ι} {angle : ι → ℝ} {t : ℝ}
    (hangle : Tendsto angle l (𝓝 t)) (htop : t ≠ Real.pi / 2) :
    Tendsto (fun n => sourceQuarterAngle (angle n)) l (𝓝 (sourceQuarterAngle t)) :=
  (continuousAt_sourceQuarterAngle htop).tendsto.comp hangle

theorem continuous_attachedCorner {U : Set Plane} (hU : IsCompact U) :
    Continuous (attachedCorner U) := by
  have := continuous_support hU
  have := continuous_unitNormal
  have := continuous_companionNormal
  unfold attachedCorner
  fun_prop

theorem continuousAt_sourceCornerHeight {U : Set Plane} (hU : IsCompact U)
    {t : ℝ} (htop : t ≠ Real.pi / 2) : ContinuousAt (sourceCornerHeight U) t :=
  ((continuous_attachedCorner hU).continuousAt.comp
    (continuousAt_sourceQuarterAngle htop)).snd

/-- Compactness upgrades the moving-angle limit to eventual uniform
strict negativity. This applies to arbitrary actual caps, independently
of selection or polygonality. -/
theorem CapHausdorffTendsto.eventually_sourceCornerHeight_neg_on_compact
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {F : Set ℝ} (hF : IsCompact F) (htop : Real.pi / 2 ∉ F)
    (hnegative : ∀ t ∈ F, sourceCornerHeight K t < 0) :
    ∀ᶠ n in atTop, ∀ t ∈ F, sourceCornerHeight (U n) t < 0 := by
  by_contra hnot
  push Not at hnot
  choose ns hns angle hangleF hfail using frequently_atTop.mp hnot
  obtain ⟨t, ht, ms, hms, hangle⟩ := hF.tendsto_subseq hangleF
  have hH : CapHausdorffTendsto (fun n => U (ns (ms n))) K :=
    h.comp ((tendsto_atTop_mono hns tendsto_id).comp hms.tendsto_atTop)
  have hθ := sourceQuarterAngle_tendsto hangle (fun heq => htop (heq ▸ ht))
  have hfirst := hH.support_tendsto_moving (fun n => hU _) hK
    ((continuous_unitNormal.tendsto _).comp hθ)
  have hsecond := hH.support_tendsto_moving (fun n => hU _) hK
    ((continuous_companionNormal.tendsto _).comp hθ)
  have hlim : Tendsto (fun n => sourceCornerHeight (U (ns (ms n))) (angle (ms n))) atTop
      (𝓝 (sourceCornerHeight K t)) :=
    ((hfirst.sub_const 1).mul ((Real.continuous_sin.tendsto _).comp hθ)).add
      ((hsecond.sub_const 1).mul ((Real.continuous_cos.tendsto _).comp hθ))
  exact (hnegative t ht).not_ge (ge_of_tendsto hlim (Eventually.of_forall fun n => hfail (ms n)))

namespace AngularGrid

open FinitePolygon

theorem sourceQuarterAngle_fullAngle (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    sourceQuarterAngle (fullAngle grid j) =
      Sum.elim (fun t : InteriorPoint grid => (t.val : ℝ))
        (fun t : InteriorPoint grid => (t.val : ℝ)) j := by
  rcases j with t | t
  · exact ite_eq_left (interiorPoint_mem grid t).2
  · exact (ite_eq_right (not_lt.mpr (by linarith [(interiorPoint_mem grid t).1] :
      Real.pi / 2 ≤ (t.val : ℝ) + Real.pi / 2))).trans (add_sub_cancel_right _ _)

/-- An actual selected finite inner source lies above the floor and
below its own corner apex. In particular that apex is nonnegative. -/
theorem innerSource_corner_height_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    0 ≤ sourceCornerHeight U (fullAngle grid j) := by
  have hcorner (t : InteriorPoint grid) : cornerWall U t x ≤ (attachedCorner U t).2 := by
    have ht := interiorPoint_mem grid t
    exact cornerWall_le_attachedCorner_snd U (Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [Real.pi_pos])) (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ht.2⟩) x
  have h0 := (finiteBarrier_nonneg U (normal grid) (pairList grid) none x).trans_eq
    (innerSource_height U grid j hx)
  rw [sourceCornerHeight, sourceQuarterAngle_fullAngle]
  rcases j with t | t
  · have hcomp := first_source_le_companion U grid t hx
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    exact h0.trans ((min_eq_left hcomp).symm.le.trans (hcorner t))
  · have hcomp := second_source_le_first U grid t hx
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    exact h0.trans (((supportWall_companionNormal U t x).trans
      (min_eq_right hcomp).symm).le.trans (hcorner t))

theorem innerAngularMass_eq_zero_of_corner_neg (U : Set Plane) (grid : Finset QuarterAngle)
    {E : Set ℝ} (hnegative : ∀ t ∈ E, sourceCornerHeight U t < 0) :
    innerAngularMass U grid E = 0 := by
  classical
  refine Finset.sum_eq_zero fun j hj => ?_
  have hzero : innerDensity U grid j = fun _ => 0 := funext fun x => by
    unfold innerDensity
    rw [outwardVelocity_eq_single, WallExpr.sourceDensity_single]
    exact indicator_of_notMem (fun hx => (innerSource_corner_height_nonneg U grid j hx).not_gt
      (hnegative _ (Finset.mem_filter.mp hj).2)) _
  rw [innerSourceMass, hzero, intervalIntegral.integral_zero]

end AngularGrid

/-- The zero-curvature conclusion constructs its own actual selected
sequence in a box with strict endpoint slack. -/
theorem IsFullCapMaximizer.upperCurvature_Ioc_eq_zero_of_negative_corners
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c s t : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hnegative : ∀ θ ∈ Icc s t, sourceCornerHeight U θ < 0) :
    upperCurvature U (Ioc s t) = 0 := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hbox : U ⊆ Icc (horizontalLeft U - 1) (horizontalRight U + 1) ×ˢ Icc (0 : ℝ) 1 :=
    fun p hp => ⟨⟨by linarith [(hU.isCap.fst_mem_Icc hp).1],
      by linarith [(hU.isCap.fst_mem_Icc hp).2]⟩, hU.isCap.inStrip hp⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU (by linarith) hbox
  have htop : Real.pi / 2 ∉ Icc s t := fun ht =>
    (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.1 rfl
  have hzero : Tendsto (fun n => AngularGrid.innerAngularMass (V n)
      (AngularGrid.dyadic (level n)) (Ioc s t)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((hHausdorff.eventually_sourceCornerHeight_neg_on_compact
      (fun n => (hV n).isCap) hU.isCap isCompact_Icc htop hnegative).mono fun n hn =>
        (AngularGrid.innerAngularMass_eq_zero_of_corner_neg _ _
          fun θ hθ => hn θ (Ioc_subset_Icc_self hθ)).symm)
  have hreal := tendsto_nhds_unique (AngularGrid.innerAngularMass_Ioc_tendsto_of_canonical_maximum
    hU hheight haffine hbox hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id)
    (fun n => (hc n).le) hrate (by linarith) (by linarith) hst hregular) hzero
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset Ioc_subset_Icc_self
    (isCompact_Icc.measure_ne_top (μ := upperCurvature U)))).mp hreal

/-- Every negative-corner direction in the regular upper domain has a
zero-curvature neighborhood. Second countability gives the statement
for the entire actual set, including arbitrarily many components. -/
theorem IsFullCapMaximizer.upperCurvature_negative_corners_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} = 0 := by
  have hopen : IsOpen (regularCurvatureDomain m) :=
    regularCurvatureDomain_eq_three m ▸ (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  refine measure_null_of_locally_null _ fun x hx => ?_
  have hnhds : {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} ∈ 𝓝 x :=
    inter_mem (hopen.mem_nhds hx.1) ((continuousAt_sourceCornerHeight hU.isCap.isCompact
      (mem_regularCurvatureDomain_iff.mp hx.1).2.2.1).tendsto.eventually_lt_const hx.2)
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  have habsub : Icc ((l + x) / 2) ((x + r) / 2) ⊆
      {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} := fun θ hθ =>
    hsub ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  exact ⟨Ioc ((l + x) / 2) ((x + r) / 2), nhdsWithin_le_nhds (mem_of_superset
    (Ioo_mem_nhds (by linarith) (by linarith)) Ioo_subset_Ioc_self),
    hU.upperCurvature_Ioc_eq_zero_of_negative_corners hheight haffine (by linarith)
      (fun θ hθ => (habsub hθ).1) (fun θ hθ => (habsub hθ).2)⟩

end AmbidextrousSofa
