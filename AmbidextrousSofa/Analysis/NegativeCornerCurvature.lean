module

public import AmbidextrousSofa.Analysis.SourceOccupation
public import AmbidextrousSofa.Analysis.CornerConfinement

@[expose] public section

/-!
# Actual curvature vanishes at corners below the floor

The corner apex height is a convex combination of the two inner walls.
A selected finite inner source is nonnegative, so its own corner cannot
lie below the floor. Strict corner negativity persists uniformly on
compact angular sets under actual cap Hausdorff convergence. The proved
finite source-occupation limit then forces the actual limiting curvature
to vanish on every regular interval of negative corners. A local covering
argument, shared with the proper-angle case, extends this to the whole
set of negative corners.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

/-- The corner apex height is a convex combination of the two inner walls,
so it is nonnegative wherever both walls are. -/
theorem attachedCorner_snd_nonneg (U : Set Plane) {θ x : ℝ} (hfirst : 0 ≤ firstWall U θ x)
    (hsecond : 0 ≤ secondWall U θ x) : 0 ≤ (attachedCorner U θ).2 := by
  have hmean : firstWall U θ x * Real.sin θ ^ 2 + secondWall U θ x * Real.cos θ ^ 2 =
      (attachedCorner U θ).2 := by
    simp only [firstWall, secondWall, attachedCorner]
    field_simp
    ring
  rw [← hmean]
  positivity

theorem isOpen_regularCurvatureDomain (m : ℝ) : IsOpen (regularCurvatureDomain m) :=
  isOpen_Ioo.sdiff (toFinite _).isClosed

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
  have h0 := (finiteBarrier_nonneg U (normal grid) (pairList grid) none x).trans_eq
    (innerSource_height U grid j hx)
  rw [sourceCornerHeight, sourceQuarterAngle_fullAngle]
  rcases j with t | t
  · exact attachedCorner_snd_nonneg U h0
      ((h0.trans (first_source_le_companion U grid t hx)).trans_eq
        (supportWall_companionNormal U _ x))
  · exact attachedCorner_snd_nonneg U (h0.trans (second_source_le_first U grid t hx))
      (h0.trans_eq (supportWall_companionNormal U _ x))

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
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, hHausdorff⟩ :=
    hU.exists_symmetric_selected_sequence
  have htop : Real.pi / 2 ∉ Icc s t := fun ht =>
    (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.1 rfl
  have hzero : Tendsto (fun n => AngularGrid.innerAngularMass (V n)
      (AngularGrid.dyadic (level n)) (Ioc s t)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' ((hHausdorff.eventually_sourceCornerHeight_neg_on_compact
      (fun n => (hV n).isCap) hU.isCap isCompact_Icc htop hnegative).mono fun n hn =>
        (AngularGrid.innerAngularMass_eq_zero_of_corner_neg _ _
          fun θ hθ => hn θ (Ioc_subset_Icc_self hθ)).symm)
  have hreal := tendsto_nhds_unique (AngularGrid.innerAngularMass_Ioc_tendsto_of_canonical_maximum
    hU hheight haffine (subset_symmetricBox_of_horizontalBox fun p hp =>
      ⟨hU.isCap.fst_mem_Icc hp, hU.isCap.inStrip hp⟩) hV hHausdorff hlevel hc hrate
    (by linarith [neg_abs_le (horizontalLeft U), abs_nonneg (horizontalRight U)])
    (by linarith [le_abs_self (horizontalRight U), abs_nonneg (horizontalLeft U)]) hst hregular)
    hzero
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset Ioc_subset_Icc_self
    (isCompact_Icc.measure_ne_top (μ := upperCurvature U)))).mp hreal

/-- Curvature vanishes on the negative corners of an open set of normals
avoiding the top once it vanishes on every compact interval of negative
corners inside it: each such direction has a zero-curvature neighborhood,
and second countability gives the statement for the entire set, including
arbitrarily many components. -/
theorem upperCurvature_negative_corners_eq_zero_of_Ioc {U : Set Plane} (hU : IsCompact U)
    {D : Set ℝ} (hD : IsOpen D) (htop : ∀ θ ∈ D, θ ≠ Real.pi / 2)
    (h : ∀ a b, a ≤ b → Icc a b ⊆ D → (∀ θ ∈ Icc a b, sourceCornerHeight U θ < 0) →
      upperCurvature U (Ioc a b) = 0) :
    upperCurvature U {θ ∈ D | sourceCornerHeight U θ < 0} = 0 := by
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp <| inter_mem (hD.mem_nhds hx.1)
    ((continuousAt_sourceCornerHeight hU (htop x hx.1)).tendsto.eventually_lt_const hx.2)
  obtain ⟨a, hla, hax⟩ := exists_between hl
  obtain ⟨b, hxb, hbr⟩ := exists_between hr
  have habsub := (Icc_subset_Ioo hla hbr).trans hsub
  exact ⟨Ioc a b, nhdsWithin_le_nhds (Ioc_mem_nhds hax hxb),
    h a b (hax.trans hxb).le (fun θ hθ => (habsub hθ).1) fun θ hθ => (habsub hθ).2⟩

theorem IsFullCapMaximizer.upperCurvature_negative_corners_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} = 0 :=
  upperCurvature_negative_corners_eq_zero_of_Ioc hU.isCap.isCompact
    (isOpen_regularCurvatureDomain m) (fun _ hθ => (mem_regularCurvatureDomain_iff.mp hθ).2.2.1)
    fun _ _ hst hregular hnegative =>
      hU.upperCurvature_Ioc_eq_zero_of_negative_corners hheight haffine hst hregular hnegative

end AmbidextrousSofa
