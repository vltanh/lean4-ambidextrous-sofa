module

public import AmbidextrousSofa.Analysis.PartialCapContinuity
public import AmbidextrousSofa.Analysis.DyadicGrid

@[expose] public section

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
  ⟨(α : ℝ) * (unitParameter t : ℝ), mul_nonneg (TerminalAngle.pos α).le (unitParameter t).property.1,
    (by
      have h : (α : ℝ) * (unitParameter t : ℝ) ≤ (α : ℝ) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (unitParameter t).property.2 (TerminalAngle.pos α).le
      exact h.trans α.property.2)⟩

theorem scaleAngle_le_terminal (α : TerminalAngle) (t : QuarterAngle) :
    (scaleAngle α t : ℝ) ≤ (α : ℝ) :=
  mul_le_of_le_one_right (TerminalAngle.pos α).le (unitParameter t).property.2

theorem scaleAngle_mem_open (α : TerminalAngle) {t : QuarterAngle}
    (ht : 0 < (t : ℝ) ∧ (t : ℝ) < Real.pi / 2) :
    (scaleAngle α t : ℝ) ∈ Ioo (0 : ℝ) (α : ℝ) := by
  have hL : 0 < Real.pi / 2 := by positivity
  exact ⟨mul_pos (TerminalAngle.pos α) (div_pos ht.1 hL),
    mul_lt_of_lt_one_right (TerminalAngle.pos α) ((div_lt_one hL).mpr ht.2)⟩

def niche (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle) (x : ℝ) : ℝ := by
  classical
  exact (insert zeroAngle grid).sup' (Finset.insert_nonempty _ _)
    (fun t => max (cornerWall U (scaleAngle α t) x) 0)

def barrier (U : Set Plane) (α : TerminalAngle) (grid : Finset QuarterAngle) (x : ℝ) : ℝ :=
  max (niche U α grid x) (firstWall U α x)

theorem clip_le_niche (U : Set Plane) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) {t : QuarterAngle} (ht : t ∈ grid) :
    max (cornerWall U (scaleAngle α t) x) 0 ≤ niche U α grid x :=
  Finset.le_sup' (fun t => max (cornerWall U (scaleAngle α t) x) 0)
    (Finset.mem_insert_of_mem ht)

theorem niche_le_iff (U : Set Plane) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x b : ℝ) :
    niche U α grid x ≤ b ↔ 0 ≤ b ∧
      ∀ t ∈ grid, max (cornerWall U (scaleAngle α t) x) 0 ≤ b := by
  have h0 : cornerWall U (scaleAngle α zeroAngle) x ≤ 0 :=
    (min_le_left _ _).trans (by simp [scaleAngle, unitParameter, zeroAngle, firstWall])
  simp only [niche, Finset.sup'_le_iff, Finset.forall_mem_insert, max_eq_right h0]

theorem niche_nonneg (U : Set Plane) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) : 0 ≤ niche U α grid x :=
  ((niche_le_iff U α grid x _).mp le_rfl).1

theorem niche_mono (U : Set Plane) (α : TerminalAngle)
    {grid other : Finset QuarterAngle} (h : grid ⊆ other) (x : ℝ) :
    niche U α grid x ≤ niche U α other x :=
  (niche_le_iff U α grid x _).mpr
    ⟨niche_nonneg U α other x, fun _ ht => clip_le_niche U α other x (h ht)⟩

theorem continuous_niche (grid : Finset QuarterAngle) :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ => niche p.1.1.carrier p.1.2 grid p.2) := by
  classical
  exact Continuous.finset_sup'_apply _ fun t _ =>
    (continuous_rescaledFullWallClip.comp (continuous_id.prodMk continuous_const) :)

theorem continuous_barrier (grid : Finset QuarterAngle) :
    Continuous (fun p : (CompactCap × TerminalAngle) × ℝ => barrier p.1.1.carrier p.1.2 grid p.2) :=
  (continuous_niche grid).max continuous_partialCapFirstWall

theorem niche_le_sweptNiche (U : CompactCap) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) : niche U.carrier α grid x ≤ sweptNiche U.carrier α x :=
  (niche_le_iff U.carrier α grid x _).mpr ⟨sweptNiche_nonneg _ _ _, fun t _ =>
    fullWallClip_le_sweptNiche_of_mem_Icc U (TerminalAngle.pos α) α.property.2 x
      ⟨(scaleAngle α t).property.1, scaleAngle_le_terminal α t⟩⟩

theorem barrier_le_partialBarrier (U : CompactCap) (α : TerminalAngle)
    (grid : Finset QuarterAngle) (x : ℝ) : barrier U.carrier α grid x ≤ partialBarrier U.carrier α x :=
  max_le_max (niche_le_sweptNiche U α grid x) le_rfl

theorem isLUB_niche (grids : ℕ → Finset QuarterAngle)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap)
    (α : TerminalAngle) (x : ℝ) :
    IsLUB (range (fun n => niche U.carrier α (grids n) x)) (sweptNiche U.carrier α x) := by
  refine ⟨forall_mem_range.2 fun n => niche_le_sweptNiche U α (grids n) x, fun b hb => ?_⟩
  have hα := TerminalAngle.pos α
  have hclip (t : QuarterAngle) : fullWallClip U x (scaleAngle α t) ≤ b := by
    refine hdense.induction (P := fun t => fullWallClip U x (scaleAngle α t) ≤ b) ?_
      (isClosed_le (continuous_rescaledFullWallClip.comp (continuous_const.prodMk
        ((continuous_subtype_val.div_const _).subtype_mk _))
          (f := fun t => (((U, α), x), unitParameter t)) :) continuous_const) t
    intro s hs
    obtain ⟨n, hn⟩ := mem_iUnion.mp hs
    exact (clip_le_niche U.carrier α (grids n) x hn).trans (hb (mem_range_self n))
  refine sweptNiche_le_of_forall hα ((niche_nonneg _ α (grids 0) x).trans
    (hb (mem_range_self 0))) fun θ hθ => (le_max_left _ 0).trans ?_
  have hπ : 0 < Real.pi / 2 := by positivity
  have h : fullWallClip U x (α * (θ / α * (Real.pi / 2) / (Real.pi / 2))) ≤ b :=
    hclip ⟨θ / α * (Real.pi / 2), mul_nonneg (div_nonneg hθ.1.le hα.le) hπ.le,
      mul_le_of_le_one_left hπ.le ((div_le_one hα).2 hθ.2.le)⟩
  rwa [mul_div_cancel_right₀ _ hπ.ne', mul_div_cancel₀ _ hα.ne'] at h

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
      ((boxedCaps B ×ˢ (univ : Set TerminalAngle)) ×ˢ Icc l r) :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto
    (((isCompact_boxedCaps hB).prod isCompact_univ).prod isCompact_Icc)
    (fun n => (continuous_barrier (dyadic n)).continuousOn)
    (fun p _ _ _ h => max_le_max (niche_mono p.1.1.carrier p.1.2 (dyadic_mono h) p.2) le_rfl)
    continuous_partialCapBarrier.continuousOn fun p _ =>
      (tendsto_niche dyadic dyadic_mono dense_iUnion_dyadic p.1.1 p.1.2 p.2).max tendsto_const_nhds

end PartialGrid

end AmbidextrousSofa
