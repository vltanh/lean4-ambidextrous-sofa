import AmbidextrousSofa.Analysis.PartialCapContinuity
import AmbidextrousSofa.Analysis.DyadicGrid

/-!
# Rescaled finite histories with the whole outgoing wall

The quarter grid is rescaled onto the actual visited interval. Its
terminal sample is harmless inside the history maximum because the whole
terminal first wall is retained separately. The finite barriers converge
uniformly on compact cap, angle and spatial domains, including degenerate
caps and the full-turn endpoint.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace PartialGrid

open AngularGrid

def unitParameter (t : QuarterAngle) : Icc (0 : ℝ) 1 :=
  ⟨(t : ℝ) / (Real.pi / 2), div_nonneg t.property.1 (by linarith [Real.pi_pos]), by
    apply (div_le_one (by linarith [Real.pi_pos] : 0 < Real.pi / 2)).mpr
    exact t.property.2⟩

def scaleAngle (α : TerminalAngle) (t : QuarterAngle) : QuarterAngle :=
  ⟨(α : ℝ) * (unitParameter t : ℝ), mul_nonneg α.pos.le (unitParameter t).property.1,
    (by
      have h : (α : ℝ) * (unitParameter t : ℝ) ≤ (α : ℝ) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (unitParameter t).property.2 α.pos.le
      exact h.trans α.property.2)⟩

theorem scaleAngle_zero (α : TerminalAngle) : (scaleAngle α zeroAngle : ℝ) = 0 := by
  simp only [scaleAngle, unitParameter, zeroAngle, zero_div, mul_zero]

theorem scaleAngle_le_terminal (α : TerminalAngle) (t : QuarterAngle) :
    (scaleAngle α t : ℝ) ≤ (α : ℝ) := by
  change (α : ℝ) * (unitParameter t : ℝ) ≤ (α : ℝ)
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (unitParameter t).property.2 α.pos.le

theorem scaleAngle_mem_open (α : TerminalAngle) {t : QuarterAngle}
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < Real.pi / 2) :
    (scaleAngle α t : ℝ) ∈ Ioo (0 : ℝ) (α : ℝ) := by
  have hL : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have ht0 : 0 < (unitParameter t : ℝ) := div_pos ht.1 hL
  have ht1 : (unitParameter t : ℝ) < 1 := (div_lt_one hL).mpr ht.2
  exact ⟨mul_pos α.pos ht0, by
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht1 α.pos⟩

theorem continuous_unitParameter : Continuous unitParameter := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.div_const _

def niche (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle) (x : ℝ) : ℝ := by
  classical
  exact (insert zeroAngle grid).sup' (Finset.insert_nonempty _ _)
    (fun t => max (cornerWall U (scaleAngle α t) x) 0)

def barrier (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle) (x : ℝ) : ℝ :=
  max (niche U α grid x) (firstWall U α x)

theorem clip_le_niche (U : Set Plane) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) {t : QuarterAngle} (ht : t ∈ grid) :
    max (cornerWall U (scaleAngle α t) x) 0 ≤ niche U α grid x := by
  classical
  exact Finset.le_sup' _ (Finset.mem_insert_of_mem ht)

theorem niche_nonneg (U : Set Plane) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) : 0 ≤ niche U α grid x := by
  classical
  exact (le_max_right _ _).trans
    (Finset.le_sup' (fun t => max (cornerWall U (scaleAngle α t) x) 0)
      (Finset.mem_insert_self zeroAngle grid))

theorem niche_le_iff (U : Set Plane) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x b : ℝ) :
    niche U α grid x ≤ b ↔ 0 ≤ b ∧
      ∀ t ∈ grid, max (cornerWall U (scaleAngle α t) x) 0 ≤ b := by
  classical
  constructor
  · intro h
    exact ⟨(niche_nonneg U α grid x).trans h,
      fun t ht => (clip_le_niche U α grid x ht).trans h⟩
  · rintro ⟨hb, hgrid⟩
    unfold niche
    rw [Finset.sup'_le_iff]
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rw [scaleAngle_zero]
      have hfirst : firstWall U 0 x = 0 := by simp [firstWall]
      exact max_le (((min_le_left _ _).trans hfirst.le).trans hb) hb
    · exact hgrid t ht

theorem niche_mono (U : Set Plane) (α : TerminalAngle)
    {grid other : Finset QuarterAngle} (h : grid ⊆ other) (x : ℝ) :
    niche U α grid x ≤ niche U α other x := by
  apply (niche_le_iff U α grid x _).mpr
  exact ⟨niche_nonneg U α other x, fun t ht => clip_le_niche U α other x (h ht)⟩

theorem continuous_niche (grid : Finset QuarterAngle) :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ => niche p.1.1.carrier p.1.2 grid p.2) := by
  classical
  unfold niche
  apply Continuous.finset_sup'_apply
  intro t _
  exact continuous_rescaledFullWallClip.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ => unitParameter t)))

theorem continuous_barrier (grid : Finset QuarterAngle) :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ => barrier p.1.1.carrier p.1.2 grid p.2) :=
  (continuous_niche grid).max continuous_partialCapFirstWall

theorem niche_le_sweptNiche (U : CompactCap) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) : niche U.carrier α grid x ≤ sweptNiche U.carrier α x := by
  apply (niche_le_iff U.carrier α grid x _).mpr
  refine ⟨sweptNiche_nonneg _ _ _, ?_⟩
  intro t _
  exact fullWallClip_le_sweptNiche_of_mem_Icc U α.pos α.property.2 x
    ⟨(scaleAngle α t).property.1, scaleAngle_le_terminal α t⟩

theorem barrier_le_partialBarrier (U : CompactCap) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) : barrier U.carrier α grid x ≤ partialBarrier U.carrier α x :=
  max_le_max (niche_le_sweptNiche U α grid x) le_rfl

theorem isLUB_niche (grids : ℕ → Finset QuarterAngle)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap)
    (α : TerminalAngle) (x : ℝ) :
    IsLUB (range (fun n => niche U.carrier α (grids n) x)) (sweptNiche U.carrier α x) := by
  refine ⟨?_, ?_⟩
  · rintro y ⟨n, rfl⟩
    exact niche_le_sweptNiche U α (grids n) x
  · intro b hb
    have hclip : ∀ t : QuarterAngle, fullWallClip U x (scaleAngle α t) ≤ b := by
      intro t
      apply hdense.induction ?_ ?_ t
      · intro s hs
        obtain ⟨n, hn⟩ := mem_iUnion.mp hs
        exact (clip_le_niche U.carrier α (grids n) x hn).trans (hb (mem_range_self n))
      · exact isClosed_le
          (continuous_rescaledFullWallClip.comp
            (continuous_const.prodMk continuous_unitParameter)) continuous_const
    have hb0 := (niche_nonneg U.carrier α (grids 0) x).trans (hb (mem_range_self 0))
    apply sweptNiche_le_of_forall α.pos hb0
    intro θ hθ
    let t : QuarterAngle := ⟨(θ / α) * (Real.pi / 2), by
      have hr : 0 ≤ θ / α := div_nonneg hθ.1.le α.pos.le
      have hr1 : θ / α ≤ 1 := (div_le_one α.pos).mpr hθ.2.le
      refine ⟨mul_nonneg hr (by linarith [Real.pi_pos]), ?_⟩
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hr1 (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 2)⟩
    have ht : (scaleAngle α t : ℝ) = θ := by
      dsimp [scaleAngle, unitParameter, t]
      field_simp [α.pos.ne', (by linarith [Real.pi_pos] : Real.pi / 2 ≠ 0)] <;> ring
    have h := hclip t
    rw [ht] at h
    exact (le_max_left _ _).trans h

theorem tendsto_niche (grids : ℕ → Finset QuarterAngle) (hmono : Monotone grids)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap)
    (α : TerminalAngle) (x : ℝ) :
    Tendsto (fun n => niche U.carrier α (grids n) x) atTop (𝓝 (sweptNiche U.carrier α x)) :=
  tendsto_atTop_isLUB (fun _ _ h => niche_mono U.carrier α (hmono h) x)
    (isLUB_niche grids hdense U α x)

theorem tendstoUniformlyOn_dyadic_box {B : Set Plane} (hB : IsCompact B) (l r : ℝ) :
    TendstoUniformlyOn (fun n (p : (CompactCap × TerminalAngle) × ℝ) =>
        barrier p.1.1.carrier p.1.2 (dyadic n) p.2)
      (fun p => partialBarrier p.1.1.carrier p.1.2 p.2) atTop
      ((boxedCaps B ×ˢ (univ : Set TerminalAngle)) ×ˢ Icc l r) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto
    (((isCompact_boxedCaps hB).prod isCompact_univ).prod isCompact_Icc)
    (fun n => (continuous_barrier (dyadic n)).continuousOn)
    (fun p _ _ _ h => max_le_max
      (niche_mono p.1.1.carrier p.1.2 (dyadic_mono h) p.2) le_rfl)
    continuous_partialCapBarrier.continuousOn
  intro p _
  exact (tendsto_niche dyadic dyadic_mono dense_iUnion_dyadic p.1.1 p.1.2 p.2).max
    tendsto_const_nhds

end PartialGrid

end AmbidextrousSofa
