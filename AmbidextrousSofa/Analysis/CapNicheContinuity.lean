import AmbidextrousSofa.Analysis.CapCompactness
import AmbidextrousSofa.Geometry.BarrierAnalysis

/-!
# Joint continuity of the actual full-turn niche

The cap varies in the Hausdorff topology. At a zero denominator, the other
wall squeezes the positive part of the two-wall minimum to zero. The resulting
closed-angle maximum is exactly the niche defined by all open angles.
Consequently the niche is jointly continuous in the cap and the abscissa.
This argument includes caps of zero width or height.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

/-- Support is jointly continuous in a nonempty compact set and its direction. -/
theorem continuous_hyperspaceSupport :
    Continuous (fun p : NonemptyCompacts Plane × Plane => support (p.1 : Set Plane) p.2) := by
  apply continuous_iff_seqContinuous.mpr
  intro z p hz
  have hd : Tendsto (fun n => Metric.hausdorffDist (z n).1 p.1) atTop (𝓝 0) := by
    simpa only [NonemptyCompacts.dist_eq] using tendsto_iff_dist_tendsto_zero.mp hz.fst
  have hv : Tendsto (fun n => |(z n).2.1| + |(z n).2.2|)
      atTop (𝓝 (|p.2.1| + |p.2.2|)) := hz.snd.fst.abs.add hz.snd.snd.abs
  have hsmall : Tendsto (fun n => |support ((z n).1 : Set Plane) (z n).2 -
      support (p.1 : Set Plane) (z n).2|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _)
      (fun n => abs_support_sub_le_hausdorff (z n).1.isCompact (z n).1.nonempty
        p.1.isCompact p.1.nonempty (z n).2)
      (by simpa only [zero_mul] using hd.mul hv)
  have hdiff : Tendsto (fun n => support ((z n).1 : Set Plane) (z n).2 -
      support (p.1 : Set Plane) (z n).2) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa only [Real.dist_eq, sub_zero] using hsmall
  have hbase := ((continuous_support p.1.isCompact).tendsto p.2).comp hz.snd
  simpa only [sub_add_cancel, zero_add] using hdiff.add hbase

/-- The original compact downward-cap domain, with its Hausdorff topology. -/
def CompactCap := {K : NonemptyCompacts Plane // IsDownwardCap (K : Set Plane)}

def CompactCap.carrier (U : CompactCap) : Set Plane := U.val

theorem CompactCap.isCap (U : CompactCap) : IsDownwardCap U.carrier := U.property

def IsDownwardCap.toCompactCap {U : Set Plane} (hU : IsDownwardCap U) : CompactCap :=
  ⟨⟨⟨U, hU.isCompact⟩, hU.nonempty⟩, hU⟩

@[simp]
theorem IsDownwardCap.toCompactCap_carrier {U : Set Plane} (hU : IsDownwardCap U) :
    hU.toCompactCap.carrier = U := rfl

theorem continuous_capSupport :
    Continuous (fun p : CompactCap × Plane => support p.1.carrier p.2) :=
  continuous_hyperspaceSupport.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem CompactCap.tendsto_iff_hausdorff {U : ℕ → CompactCap} {K : CompactCap} :
    Tendsto U atTop (𝓝 K) ↔
      CapHausdorffTendsto (fun n => (U n).carrier) K.carrier := by
  rw [tendsto_iff_dist_tendsto_zero]
  rfl

theorem IsDownwardCap.tendsto_toCompactCap {U : ℕ → Set Plane} {K : Set Plane}
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (h : CapHausdorffTendsto U K) :
    Tendsto (fun n => (hU n).toCompactCap) atTop (𝓝 hK.toCompactCap) :=
  CompactCap.tendsto_iff_hausdorff.mpr h

def fullWallClip (U : CompactCap) (x t : ℝ) : ℝ :=
  max (cornerWall U.carrier t x) 0

theorem fullWallClip_nonneg (U : CompactCap) (x t : ℝ) : 0 ≤ fullWallClip U x t :=
  le_max_right _ _

theorem fullWallClip_zero (U : CompactCap) (x : ℝ) : fullWallClip U x 0 = 0 := by
  apply max_eq_right
  change min (firstWall U.carrier 0 x) (secondWall U.carrier 0 x) ≤ 0
  exact (min_le_left _ _).trans (by simp [firstWall])

theorem fullWallClip_pi_div_two (U : CompactCap) (x : ℝ) :
    fullWallClip U x (Real.pi / 2) = 0 := by
  apply max_eq_right
  change min (firstWall U.carrier (Real.pi / 2) x)
    (secondWall U.carrier (Real.pi / 2) x) ≤ 0
  exact (min_le_right _ _).trans (by simp [secondWall])

/-- Both support directions vary jointly with the cap. -/
theorem continuous_capFirstSupport :
    Continuous (fun z : (CompactCap × ℝ) × ℝ => support z.1.1.carrier (unitNormal z.2)) :=
  continuous_capSupport.comp
    ((continuous_fst.comp continuous_fst).prodMk
      (continuous_unitNormal.comp continuous_snd))

theorem continuous_capSecondSupport :
    Continuous (fun z : (CompactCap × ℝ) × ℝ =>
      support z.1.1.carrier (companionNormal z.2)) := by
  have hc : Continuous companionNormal := by unfold companionNormal; fun_prop
  exact continuous_capSupport.comp
    ((continuous_fst.comp continuous_fst).prodMk (hc.comp continuous_snd))

theorem continuousAt_fullWallClip {z : (CompactCap × ℝ) × ℝ}
    (hz : z.2 ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ContinuousAt (fun p : (CompactCap × ℝ) × ℝ => fullWallClip p.1.1 p.1.2 p.2) z := by
  have hf := continuous_capFirstSupport
  have hg := continuous_capSecondSupport
  by_cases hz0 : z.2 = 0
  · let upper : (CompactCap × ℝ) × ℝ → ℝ := fun p =>
      max (secondWall p.1.1.carrier p.2 p.1.2) 0
    have hupper : ContinuousAt upper z := by
      unfold upper secondWall
      fun_prop (disch := simp [hz0])
    have hupper0 : upper z = 0 := by
      change max (secondWall z.1.1.carrier z.2 z.1.2) 0 = 0
      apply max_eq_right
      simp only [hz0, secondWall, companionNormal, Real.sin_zero, Real.cos_zero,
        neg_zero, mul_zero, add_zero, div_one]
      linarith [z.1.1.isCap.support_upward_le_one]
    have hvalue : fullWallClip z.1.1 z.1.2 z.2 = 0 := by rw [hz0, fullWallClip_zero]
    change Tendsto _ _ (𝓝 (fullWallClip z.1.1 z.1.2 z.2))
    rw [hvalue]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [hupper0] using hupper)
    · intro p
      exact fullWallClip_nonneg _ _ _
    · intro p
      exact max_le_max_right 0 (min_le_right _ _)
  by_cases hzL : z.2 = Real.pi / 2
  · let upper : (CompactCap × ℝ) × ℝ → ℝ := fun p =>
      max (firstWall p.1.1.carrier p.2 p.1.2) 0
    have hupper : ContinuousAt upper z := by
      unfold upper firstWall
      fun_prop (disch := simp [hzL])
    have hupper0 : upper z = 0 := by
      change max (firstWall z.1.1.carrier z.2 z.1.2) 0 = 0
      apply max_eq_right
      rw [hzL, firstWall_pi_div_two]
      linarith [z.1.1.isCap.support_upward_le_one]
    have hvalue : fullWallClip z.1.1 z.1.2 z.2 = 0 := by
      rw [hzL, fullWallClip_pi_div_two]
    change Tendsto _ _ (𝓝 (fullWallClip z.1.1 z.1.2 z.2))
    rw [hvalue]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [hupper0] using hupper)
    · intro p
      exact fullWallClip_nonneg _ _ _
    · intro p
      exact max_le_max_right 0 (min_le_left _ _)
  · have hsin : Real.sin z.2 ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (lt_of_le_of_ne hz.1 (Ne.symm hz0)) (by linarith [hz.2, Real.pi_pos]))
    have hcos : Real.cos z.2 ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hz.1, Real.pi_pos], lt_of_le_of_ne hz.2 hzL⟩)
    unfold fullWallClip cornerWall firstWall secondWall
    fun_prop (disch := assumption)

theorem continuous_fullWallClip_on_angles :
    Continuous (fun p : (CompactCap × ℝ) × Icc (0 : ℝ) (Real.pi / 2) =>
      fullWallClip p.1.1 p.1.2 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (continuousAt_fullWallClip (z := (p.1, (p.2 : ℝ))) p.2.property).comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousAt

theorem sweptNiche_eq_sSup_clipped (U : CompactCap) (x : ℝ) :
    sweptNiche U.carrier (Real.pi / 2) x =
      sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) => fullWallClip U x t) '' Set.univ) := by
  let zeroAngle : Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, by linarith [Real.pi_pos]⟩
  have hcont : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) => fullWallClip U x t) :=
    continuous_fullWallClip_on_angles.comp (continuous_const.prodMk continuous_id)
  have hbounded := (isCompact_univ : IsCompact
    (Set.univ : Set (Icc (0 : ℝ) (Real.pi / 2)))).bddAbove_image hcont.continuousOn
  have hzero : 0 ≤ sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) =>
      fullWallClip U x t) '' Set.univ) := by
    have h := le_csSup hbounded (mem_image_of_mem _ (mem_univ zeroAngle))
    simpa only [zeroAngle, fullWallClip_zero] using h
  apply le_antisymm
  · apply sweptNiche_le_of_forall (by linarith [Real.pi_pos]) hzero
    intro t ht
    calc
      cornerWall U.carrier t x ≤ fullWallClip U x t := le_max_left _ _
      _ ≤ _ := le_csSup hbounded (mem_image_of_mem _
        (mem_univ (⟨t, ht.1.le, ht.2.le⟩ : Icc (0 : ℝ) (Real.pi / 2))))
  · apply csSup_le ⟨fullWallClip U x zeroAngle, zeroAngle, mem_univ _, rfl⟩
    rintro y ⟨t, _, rfl⟩
    by_cases ht0 : (t : ℝ) = 0
    · rw [ht0, fullWallClip_zero]
      exact sweptNiche_nonneg _ _ _
    by_cases htL : (t : ℝ) = Real.pi / 2
    · rw [htL, fullWallClip_pi_div_two]
      exact sweptNiche_nonneg _ _ _
    · apply max_le _ (sweptNiche_nonneg _ _ _)
      exact cornerWall_le_sweptNiche
        (sweptWallValues_bddAbove U.isCap.isCompact le_rfl x)
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 htL⟩

theorem continuous_capSweptNiche :
    Continuous (fun p : CompactCap × ℝ => sweptNiche p.1.carrier (Real.pi / 2) p.2) := by
  have h := (isCompact_univ : IsCompact
    (Set.univ : Set (Icc (0 : ℝ) (Real.pi / 2)))).continuous_sSup
    continuous_fullWallClip_on_angles
  simpa only [← sweptNiche_eq_sSup_clipped] using h

theorem CapHausdorffTendsto.sweptNiche_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => sweptNiche (U n) (Real.pi / 2) (x n))
      atTop (𝓝 (sweptNiche K (Real.pi / 2) y)) :=
  (continuous_capSweptNiche.tendsto (hK.toCompactCap, y)).comp
    ((IsDownwardCap.tendsto_toCompactCap hU hK h).prodMk_nhds hx)

end AmbidextrousSofa
