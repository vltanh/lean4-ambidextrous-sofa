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
  have hmean : firstWall U θ x * Real.sin θ ^ 2 +
      secondWall U θ x * Real.cos θ ^ 2 = (attachedCorner U θ).2 := by
    unfold firstWall secondWall attachedCorner
    dsimp only
    field_simp [hs.ne', hc.ne']
    ring
  have hfirst := mul_le_mul_of_nonneg_right
    (min_le_left (firstWall U θ x) (secondWall U θ x)) (sq_nonneg (Real.sin θ))
  have hsecond := mul_le_mul_of_nonneg_right
    (min_le_right (firstWall U θ x) (secondWall U θ x)) (sq_nonneg (Real.cos θ))
  have hcircle := congrArg (fun v : ℝ => cornerWall U θ x * v)
    (Real.sin_sq_add_cos_sq θ)
  change min (firstWall U θ x) (secondWall U θ x) ≤ _
  dsimp only [cornerWall] at hcircle
  nlinarith

/-- Both upper source normals are indexed by the angle of their own
quarter-turn corner. The top normal itself is excluded when continuity
of this fold is used. -/
def sourceQuarterAngle (t : ℝ) : ℝ :=
  if t < Real.pi / 2 then t else t - Real.pi / 2

def sourceCornerHeight (U : Set Plane) (t : ℝ) : ℝ :=
  (attachedCorner U (sourceQuarterAngle t)).2

theorem sourceQuarterAngle_tendsto {ι : Type*} {l : Filter ι} {angle : ι → ℝ} {t : ℝ}
    (hangle : Tendsto angle l (𝓝 t)) (htop : t ≠ Real.pi / 2) :
    Tendsto (fun n => sourceQuarterAngle (angle n)) l (𝓝 (sourceQuarterAngle t)) := by
  by_cases hlt : t < Real.pi / 2
  · have heq : (fun n => angle n) =ᶠ[l] (fun n => sourceQuarterAngle (angle n)) := by
      filter_upwards [hangle.eventually_lt_const hlt] with n hn
      simp only [sourceQuarterAngle, if_pos hn]
    simpa only [sourceQuarterAngle, if_pos hlt] using hangle.congr' heq
  · have hgt : Real.pi / 2 < t := lt_of_le_of_ne (le_of_not_gt hlt) htop.symm
    have heq : (fun n => angle n - Real.pi / 2) =ᶠ[l]
        (fun n => sourceQuarterAngle (angle n)) := by
      filter_upwards [hangle.eventually_const_lt hgt] with n hn
      simp only [sourceQuarterAngle, if_neg (not_lt.mpr hn.le)]
    simpa only [sourceQuarterAngle, if_neg hlt] using
      (hangle.sub_const (Real.pi / 2)).congr' heq

theorem continuousAt_sourceQuarterAngle {t : ℝ} (htop : t ≠ Real.pi / 2) :
    ContinuousAt sourceQuarterAngle t :=
  sourceQuarterAngle_tendsto tendsto_id htop

theorem continuous_attachedCorner {U : Set Plane} (hU : IsCompact U) :
    Continuous (attachedCorner U) := by
  have hfirst := (continuous_support hU).comp continuous_unitNormal
  have hsecond := (continuous_support hU).comp continuous_companionNormal
  exact (((hfirst.sub continuous_const).mul Real.continuous_cos).sub
    ((hsecond.sub continuous_const).mul Real.continuous_sin)).prodMk
    (((hfirst.sub continuous_const).mul Real.continuous_sin).add
      ((hsecond.sub continuous_const).mul Real.continuous_cos))

theorem continuousAt_sourceCornerHeight {U : Set Plane} (hU : IsCompact U)
    {t : ℝ} (htop : t ≠ Real.pi / 2) : ContinuousAt (sourceCornerHeight U) t :=
  ((continuous_attachedCorner hU).continuousAt.comp
    (continuousAt_sourceQuarterAngle htop)).snd

theorem CapHausdorffTendsto.attachedCorner_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {angle : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t)) :
    Tendsto (fun n => attachedCorner (U n) (angle n)) atTop (𝓝 (attachedCorner K t)) := by
  have hfirst := h.support_tendsto_moving hU hK
    ((continuous_unitNormal.tendsto t).comp hangle)
  have hsecond := h.support_tendsto_moving hU hK
    ((continuous_companionNormal.tendsto t).comp hangle)
  have hs := (Real.continuous_sin.tendsto t).comp hangle
  have hc := (Real.continuous_cos.tendsto t).comp hangle
  exact (((hfirst.sub_const 1).mul hc).sub ((hsecond.sub_const 1).mul hs)).prodMk_nhds
    (((hfirst.sub_const 1).mul hs).add ((hsecond.sub_const 1).mul hc))

theorem CapHausdorffTendsto.sourceCornerHeight_tendsto
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {angle : ℕ → ℝ} {t : ℝ} (hangle : Tendsto angle atTop (𝓝 t))
    (htop : t ≠ Real.pi / 2) :
    Tendsto (fun n => sourceCornerHeight (U n) (angle n)) atTop
      (𝓝 (sourceCornerHeight K t)) :=
  (h.attachedCorner_tendsto hU hK (sourceQuarterAngle_tendsto hangle htop)).snd

/-- Compactness upgrades the moving-angle limit to eventual uniform
strict negativity. This applies to arbitrary actual caps, independently
of selection or polygonality. -/
theorem CapHausdorffTendsto.eventually_sourceCornerHeight_neg_on_compact
    {U : ℕ → Set Plane} {K : Set Plane} (h : CapHausdorffTendsto U K)
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {F : Set ℝ} (hF : IsCompact F) (htop : Real.pi / 2 ∉ F)
    (hnegative : ∀ t ∈ F, sourceCornerHeight K t < 0) :
    ∀ᶠ n in atTop, ∀ t ∈ F, sourceCornerHeight (U n) t < 0 := by
  classical
  by_contra hnot
  have hbad : ∀ k : ℕ, ∃ n, k ≤ n ∧
      ∃ t ∈ F, ¬ sourceCornerHeight (U n) t < 0 := by
    intro k
    by_contra hk
    apply hnot
    refine eventually_atTop.mpr ⟨k, ?_⟩
    intro n hn t ht
    by_contra hneg
    exact hk ⟨n, hn, t, ht, hneg⟩
  choose ns hns angle hangleF hnegativeFail using hbad
  obtain ⟨t, ht, ms, hms, hangle⟩ := hF.tendsto_subseq hangleF
  let seq : ℕ → ℕ := fun n => ns (ms n)
  have hnsTop : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  have hseq : Tendsto seq atTop atTop := hnsTop.comp hms.tendsto_atTop
  have hlim : Tendsto (fun n => sourceCornerHeight (U (seq n)) (angle (ms n))) atTop
      (𝓝 (sourceCornerHeight K t)) :=
    (h.comp hseq).sourceCornerHeight_tendsto (fun n => hU (seq n)) hK hangle
      (fun heq => htop (heq ▸ ht))
  have hnonneg : 0 ≤ sourceCornerHeight K t := ge_of_tendsto hlim
    (Eventually.of_forall (fun n => le_of_not_gt (hnegativeFail (ms n))))
  exact not_lt_of_ge hnonneg (hnegative t ht)

namespace AngularGrid

open FinitePolygon

theorem sourceQuarterAngle_fullAngle (grid : Finset QuarterAngle) (j : SourceIndex grid) :
    sourceQuarterAngle (fullAngle grid j) =
      Sum.elim (fun t : InteriorPoint grid => (t.val : ℝ))
        (fun t : InteriorPoint grid => (t.val : ℝ)) j := by
  cases j with
  | inl t => simp only [fullAngle, sourceQuarterAngle, if_pos (interiorPoint_mem grid t).2,
      Sum.elim_inl]
  | inr t =>
    have hnot : ¬ (t.val : ℝ) + Real.pi / 2 < Real.pi / 2 := by
      linarith [(interiorPoint_mem grid t).1]
    simp only [fullAngle, sourceQuarterAngle, if_neg hnot, add_sub_cancel_right, Sum.elim_inr]

/-- An actual selected finite inner source lies above the floor and
below its own corner apex. In particular that apex is nonnegative. -/
theorem innerSource_corner_height_nonneg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) {x : ℝ} (hx : x ∈ innerSourceSet U grid j) :
    0 ≤ sourceCornerHeight U (fullAngle grid j) := by
  cases j with
  | inl t =>
    have ht := interiorPoint_mem grid t
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    have hsource := innerSource_height U grid (Sum.inl t) hx
    have hcomp := first_source_le_companion U grid t hx
    simp only [normal, supportWall_unitNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    rw [sourceCornerHeight, sourceQuarterAngle_fullAngle]
    change 0 ≤ (attachedCorner U (t.val : ℝ)).2
    calc
      0 ≤ finiteBarrier U (normal grid) (pairList grid) none x :=
        finiteBarrier_nonneg U (normal grid) (pairList grid) none x
      _ = firstWall U t.val x := hsource
      _ = cornerWall U t.val x := (min_eq_left hcomp).symm
      _ ≤ _ := cornerWall_le_attachedCorner_snd U hs hc x
  | inr t =>
    have ht := interiorPoint_mem grid t
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    have hsource := innerSource_height U grid (Sum.inr t) hx
    have hcomp := second_source_le_first U grid t hx
    simp only [normal, supportWall_companionNormal] at hsource
    rw [supportWall_unitNormal, supportWall_companionNormal] at hcomp
    rw [sourceCornerHeight, sourceQuarterAngle_fullAngle]
    change 0 ≤ (attachedCorner U (t.val : ℝ)).2
    calc
      0 ≤ finiteBarrier U (normal grid) (pairList grid) none x :=
        finiteBarrier_nonneg U (normal grid) (pairList grid) none x
      _ = secondWall U t.val x := hsource
      _ = cornerWall U t.val x := (min_eq_right hcomp).symm
      _ ≤ _ := cornerWall_le_attachedCorner_snd U hs hc x

theorem innerSourceSet_eq_empty_of_corner_neg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (hnegative : sourceCornerHeight U (fullAngle grid j) < 0) :
    innerSourceSet U grid j = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  exact not_lt_of_ge (innerSource_corner_height_nonneg U grid j hx) hnegative

theorem innerDensity_eq_zero_of_corner_neg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (hnegative : sourceCornerHeight U (fullAngle grid j) < 0) :
    innerDensity U grid j = fun _ => 0 := by
  classical
  funext x
  have hnot : x ∉ innerSourceSet U grid j := by
    rw [innerSourceSet_eq_empty_of_corner_neg U grid j hnegative]
    exact not_mem_empty x
  unfold innerDensity
  rw [outwardVelocity_eq_single, WallExpr.sourceDensity_single,
    indicator_of_notMem hnot]

theorem innerSourceMass_eq_zero_of_corner_neg (U : Set Plane) (grid : Finset QuarterAngle)
    (j : SourceIndex grid) (hnegative : sourceCornerHeight U (fullAngle grid j) < 0) :
    innerSourceMass U grid j = 0 := by
  rw [innerSourceMass, innerDensity_eq_zero_of_corner_neg U grid j hnegative,
    intervalIntegral.integral_zero]

theorem innerAngularMass_eq_zero_of_corner_neg (U : Set Plane) (grid : Finset QuarterAngle)
    {E : Set ℝ} (hnegative : ∀ t ∈ E, sourceCornerHeight U t < 0) :
    innerAngularMass U grid E = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro j hj
  exact innerSourceMass_eq_zero_of_corner_neg U grid j
    (hnegative (fullAngle grid j) (Finset.mem_filter.mp hj).2)

theorem innerAngularMass_eventually_zero_of_compact
    {U : ℕ → Set Plane} {K : Set Plane} {grid : ℕ → Finset QuarterAngle}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    {E F : Set ℝ} (hF : IsCompact F) (hEF : E ⊆ F) (htop : Real.pi / 2 ∉ F)
    (hnegative : ∀ t ∈ F, sourceCornerHeight K t < 0) :
    ∀ᶠ n in atTop, innerAngularMass (U n) (grid n) E = 0 := by
  filter_upwards [h.eventually_sourceCornerHeight_neg_on_compact hU hK hF htop hnegative]
    with n hn
  exact innerAngularMass_eq_zero_of_corner_neg (U n) (grid n) (fun t ht => hn t (hEF ht))

theorem upperCurvature_Ioc_eq_zero_of_negative_corners
    {target : Set Plane} {U : ℕ → Set Plane} {a b m c s t : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target),
      capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    (hst : s ≤ t) (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hnegative : ∀ θ ∈ Icc s t, sourceCornerHeight target θ < 0) :
    upperCurvature target (Ioc s t) = 0 := by
  have htop : Real.pi / 2 ∉ Icc s t := by
    intro ht
    exact (mem_regularCurvatureDomain_iff.mp (hregular ht)).2.2.1 rfl
  have hevent := innerAngularMass_eventually_zero_of_compact (grid := fun n => dyadic (level n))
    hHausdorff (fun n => (hU n).isCap) hTarget.isCap isCompact_Icc Ioc_subset_Icc_self
    htop hnegative
  have hzero : Tendsto (fun n => innerAngularMass (U n) (dyadic (level n)) (Ioc s t))
      atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hevent.mono (fun n hn => hn.symm))
  have hmass := innerAngularMass_Ioc_tendsto_of_canonical_maximum hTarget hheight haffine
    hTargetBox hU hHausdorff hlevel hc hrate hleft hright hst hregular
  have hreal : (upperCurvature target).real (Ioc s t) = 0 := tendsto_nhds_unique hmass hzero
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset Ioc_subset_Icc_self
    (isCompact_Icc.measure_ne_top (μ := upperCurvature target)))).mp hreal

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
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp [a]
      linarith [hx.1]
    · dsimp [b]
      linarith [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hab hbox
  exact AngularGrid.upperCurvature_Ioc_eq_zero_of_negative_corners hU hheight haffine hbox
    hV hHausdorff (tendsto_atTop_mono hlevel tendsto_id) (fun n => (hc n).le) hrate
    (by dsimp [a]; linarith) (by dsimp [b]; linarith) hst hregular hnegative

/-- Every negative-corner direction in the regular upper domain has a
zero-curvature neighborhood. Second countability gives the statement
for the entire actual set, including arbitrarily many components. -/
theorem IsFullCapMaximizer.upperCurvature_negative_corners_eq_zero
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    {m c : ℝ}
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    upperCurvature U {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} = 0 := by
  have hopen : IsOpen (regularCurvatureDomain m) := by
    rw [regularCurvatureDomain_eq_three]
    exact (isOpen_Ioo.union isOpen_Ioo).union isOpen_Ioo
  apply measure_null_of_locally_null _
  intro x hx
  have htop := (mem_regularCurvatureDomain_iff.mp hx.1).2.2.1
  have hneg : ∀ᶠ θ in 𝓝 x, sourceCornerHeight U θ < 0 :=
    (continuousAt_sourceCornerHeight hU.isCap.isCompact htop).tendsto.eventually_lt_const hx.2
  have hnhds : {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} ∈ 𝓝 x :=
    inter_mem (hopen.mem_nhds hx.1) hneg
  obtain ⟨l, r, ⟨hl, hr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  let a := (l + x) / 2
  let b := (x + r) / 2
  have hax : a < x := by dsimp [a]; linarith
  have hxb : x < b := by dsimp [b]; linarith
  have hab : a ≤ b := (hax.trans hxb).le
  have habsub : Icc a b ⊆
      {θ ∈ regularCurvatureDomain m | sourceCornerHeight U θ < 0} := by
    intro θ hθ
    apply hsub
    constructor <;> dsimp [a, b] at hθ <;> linarith [hθ.1, hθ.2]
  refine ⟨Ioc a b, nhdsWithin_le_nhds ?_, ?_⟩
  · exact mem_of_superset (Ioo_mem_nhds hax hxb) Ioo_subset_Ioc_self
  · exact hU.upperCurvature_Ioc_eq_zero_of_negative_corners hheight haffine hab
      (fun θ hθ => (habsub hθ).1) (fun θ hθ => (habsub hθ).2)

end AmbidextrousSofa
