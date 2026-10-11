module

public import AmbidextrousSofa.Analysis.CapCompactness
public import AmbidextrousSofa.Geometry.BarrierAnalysis

@[expose] public section

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

/-- The original compact downward-cap domain, with its Hausdorff topology. -/
abbrev CompactCap := {K : NonemptyCompacts Plane // IsDownwardCap (K : Set Plane)}

def CompactCap.carrier (U : CompactCap) : Set Plane := U.val

theorem CompactCap.isCap (U : CompactCap) : IsDownwardCap U.carrier := U.property

def IsDownwardCap.toCompactCap {U : Set Plane} (hU : IsDownwardCap U) : CompactCap :=
  ⟨⟨⟨U, hU.isCompact⟩, hU.nonempty⟩, hU⟩

@[simp]
theorem IsDownwardCap.toCompactCap_carrier {U : Set Plane} (hU : IsDownwardCap U) :
    hU.toCompactCap.carrier = U := rfl

theorem continuous_capSupport :
    Continuous (fun p : CompactCap × Plane => support p.1.carrier p.2) := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  have hd := (tendsto_iff_dist_tendsto_zero.1 (continuous_fst.tendsto p)).mul
    ((continuous_snd.fst.abs.add continuous_snd.snd.abs).tendsto p)
  rw [zero_mul] at hd
  have h := (tendsto_zero_iff_abs_tendsto_zero _).2 (squeeze_zero (fun _ => abs_nonneg _)
    (fun q : CompactCap × Plane => abs_support_sub_le_hausdorff q.1.isCap.isCompact
      q.1.isCap.nonempty p.1.isCap.isCompact p.1.isCap.nonempty q.2) hd)
  simpa [ContinuousAt] using h.add (((continuous_support p.1.isCap.isCompact).tendsto p.2).comp
    continuous_snd.continuousAt)

theorem CompactCap.tendsto_iff_hausdorff {U : ℕ → CompactCap} {K : CompactCap} :
    Tendsto U atTop (𝓝 K) ↔
      CapHausdorffTendsto (fun n => (U n).carrier) K.carrier :=
  tendsto_iff_dist_tendsto_zero

theorem IsDownwardCap.tendsto_toCompactCap {U : ℕ → Set Plane} {K : Set Plane}
    (hU : ∀ n, IsDownwardCap (U n)) (hK : IsDownwardCap K)
    (h : CapHausdorffTendsto U K) :
    Tendsto (fun n => (hU n).toCompactCap) atTop (𝓝 hK.toCompactCap) :=
  CompactCap.tendsto_iff_hausdorff.mpr h

def fullWallClip (U : CompactCap) (x t : ℝ) : ℝ :=
  max (cornerWall U.carrier t x) 0

theorem fullWallClip_zero (U : CompactCap) (x : ℝ) : fullWallClip U x 0 = 0 :=
  max_eq_right ((min_le_left _ _).trans (by simp [firstWall]))

theorem fullWallClip_pi_div_two (U : CompactCap) (x : ℝ) :
    fullWallClip U x (Real.pi / 2) = 0 :=
  max_eq_right ((min_le_right _ _).trans (by simp [secondWall]))

theorem continuous_capSupport_comp {v : ℝ → Plane} (hv : Continuous v) :
    Continuous fun p : (CompactCap × ℝ) × ℝ => support p.1.1.carrier (v p.2) :=
  continuous_capSupport.comp (f := fun p : (CompactCap × ℝ) × ℝ => (p.1.1, v p.2)) (by fun_prop)

theorem continuousAt_fullWallClip {z : (CompactCap × ℝ) × ℝ}
    (hz : z.2 ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ContinuousAt (fun p : (CompactCap × ℝ) × ℝ => fullWallClip p.1.1 p.1.2 p.2) z := by
  have hf := continuous_capSupport_comp continuous_unitNormal
  have hg := continuous_capSupport_comp continuous_companionNormal
  -- At an endpoint angle, one wall bounds the clip from above and tends to a nonpositive value.
  have squeeze (W : (CompactCap × ℝ) × ℝ → ℝ) (hW : ContinuousAt W z) (hW0 : W z ≤ 0)
      (hle : ∀ p : (CompactCap × ℝ) × ℝ, cornerWall p.1.1.carrier p.2 p.1.2 ≤ W p) :
      ContinuousAt (fun p : (CompactCap × ℝ) × ℝ => fullWallClip p.1.1 p.1.2 p.2) z := by
    rw [ContinuousAt, show fullWallClip z.1.1 z.1.2 z.2 = 0 from max_eq_right ((hle z).trans hW0)]
    exact squeeze_zero (fun p => le_max_right _ _) (fun p => max_le_max_right 0 (hle p))
      (by simpa only [max_eq_right hW0] using hW.max (tendsto_const_nhds (x := 0)))
  have hU := z.1.1.isCap.support_upward_le_one
  rcases hz.1.eq_or_lt with h0 | h0
  · refine squeeze _ (by unfold secondWall; fun_prop (disch := simp [← h0])) ?_
      fun p => min_le_right _ _
    simpa [secondWall, ← h0, companionNormal]
  rcases hz.2.eq_or_lt with h1 | h1
  · refine squeeze _ (by unfold firstWall; fun_prop (disch := simp [h1])) ?_
      fun p => min_le_left _ _
    simpa [h1, firstWall_pi_div_two]
  have hsin := (sin_cos_pos_of_mem_quarter ⟨h0, h1⟩).1.ne'
  have hcos := (sin_cos_pos_of_mem_quarter ⟨h0, h1⟩).2.ne'
  unfold fullWallClip cornerWall firstWall secondWall
  fun_prop (disch := assumption)

theorem continuous_fullWallClip_on_angles :
    Continuous (fun p : (CompactCap × ℝ) × Icc (0 : ℝ) (Real.pi / 2) =>
      fullWallClip p.1.1 p.1.2 p.2) :=
  continuous_iff_continuousAt.2 fun p => (continuousAt_fullWallClip (z := (p.1, p.2)) p.2.2).comp
    (f := fun q : (CompactCap × ℝ) × Icc (0 : ℝ) (Real.pi / 2) => (q.1, (q.2 : ℝ))) (by fun_prop)

theorem sweptNiche_eq_sSup_clipped (U : CompactCap) (x : ℝ) :
    sweptNiche U.carrier (Real.pi / 2) x =
      sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) => fullWallClip U x t) '' Set.univ) := by
  have h0 : (0 : ℝ) ∈ Icc 0 (Real.pi / 2) := ⟨le_rfl, by positivity⟩
  have hb := isCompact_univ.bddAbove_image
    (continuous_fullWallClip_on_angles.comp (.prodMk_right (U, x))).continuousOn
  have hle (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (Real.pi / 2)) : fullWallClip U x t ≤
      sSup ((fun t : Icc (0 : ℝ) (Real.pi / 2) => fullWallClip U x t) '' univ) :=
    le_csSup hb ⟨⟨t, ht⟩, mem_univ _, rfl⟩
  refine le_antisymm (sweptNiche_le_of_forall (by positivity)
    ((le_max_right _ _).trans (hle 0 h0))
    fun t ht => (le_max_left _ _).trans (hle t (Ioo_subset_Icc_self ht)))
    (csSup_le ⟨_, ⟨0, h0⟩, mem_univ _, rfl⟩ ?_)
  rintro _ ⟨⟨t, ht⟩, -, rfl⟩
  rcases ht.1.eq_or_lt with rfl | h0
  · simp [fullWallClip_zero, sweptNiche_nonneg]
  rcases ht.2.eq_or_lt with rfl | h1
  · simp [fullWallClip_pi_div_two, sweptNiche_nonneg]
  exact max_le (cornerWall_le_sweptNiche (sweptWallValues_bddAbove U.isCap.isCompact le_rfl x)
    ⟨h0, h1⟩) (sweptNiche_nonneg _ _ _)

theorem continuous_capSweptNiche :
    Continuous (fun p : CompactCap × ℝ => sweptNiche p.1.carrier (Real.pi / 2) p.2) := by
  simpa only [← sweptNiche_eq_sSup_clipped] using isCompact_univ.continuous_sSup
    (f := fun (p : CompactCap × ℝ) (t : Icc (0 : ℝ) (Real.pi / 2)) => fullWallClip p.1 p.2 t)
    continuous_fullWallClip_on_angles

theorem CapHausdorffTendsto.sweptNiche_tendsto {U : ℕ → Set Plane} {K : Set Plane}
    (h : CapHausdorffTendsto U K) (hU : ∀ n, IsDownwardCap (U n))
    (hK : IsDownwardCap K) {x : ℕ → ℝ} {y : ℝ} (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => sweptNiche (U n) (Real.pi / 2) (x n))
      atTop (𝓝 (sweptNiche K (Real.pi / 2) y)) := by
  simpa only [Function.comp_def, IsDownwardCap.toCompactCap_carrier] using
    (continuous_capSweptNiche.tendsto (hK.toCompactCap, y)).comp
      ((IsDownwardCap.tendsto_toCompactCap hU hK h).prodMk_nhds hx)

end AmbidextrousSofa
