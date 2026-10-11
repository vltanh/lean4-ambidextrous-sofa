module

public import AmbidextrousSofa.Analysis.CapMaximum

@[expose] public section

/-!
# Uniform approximation of the actual niche by finite angular grids

The samples use the continuous clipped two-wall height on the closed
quarter interval. Its endpoint values are zero, so inserting the zero
angle is exactly the physical baseline clipping. For any increasing
sequence of finite grids with dense union, the actual finite maxima
increase to the whole-angle niche. Dini's theorem then makes convergence
uniform on every compact cap domain and bounded spatial interval.
-/

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology

namespace AmbidextrousSofa

namespace AngularGrid

abbrev QuarterAngle := Icc (0 : ℝ) (Real.pi / 2)

def zeroAngle : QuarterAngle := ⟨0, le_rfl, by linarith [Real.pi_pos]⟩

/-- Inserting angle zero adds exactly the zero baseline to the finite
maximum, including when the displayed grid is empty. -/
def niche (U : CompactCap) (grid : Finset QuarterAngle) (x : ℝ) : ℝ := by
  classical
  exact (insert zeroAngle grid).sup' (Finset.insert_nonempty _ _)
    (fun t => fullWallClip U x t)

theorem clip_le_niche (U : CompactCap) (grid : Finset QuarterAngle) (x : ℝ)
    {t : QuarterAngle} (ht : t ∈ grid) : fullWallClip U x t ≤ niche U grid x :=
  Finset.le_sup' (fun t : QuarterAngle => fullWallClip U x t) (Finset.mem_insert_of_mem ht)

theorem niche_le_iff (U : CompactCap) (grid : Finset QuarterAngle) (x b : ℝ) :
    niche U grid x ≤ b ↔ 0 ≤ b ∧ ∀ t ∈ grid, fullWallClip U x t ≤ b := by
  simp [niche, zeroAngle, fullWallClip_zero]

theorem niche_nonneg (U : CompactCap) (grid : Finset QuarterAngle) (x : ℝ) :
    0 ≤ niche U grid x :=
  ((niche_le_iff U grid x _).mp le_rfl).1

theorem niche_mono (U : CompactCap) {grid grid' : Finset QuarterAngle}
    (hgrid : grid ⊆ grid') (x : ℝ) : niche U grid x ≤ niche U grid' x :=
  (niche_le_iff U grid x _).mpr
    ⟨niche_nonneg U grid' x, fun _ ht => clip_le_niche U grid' x (hgrid ht)⟩

theorem continuous_niche (grid : Finset QuarterAngle) :
    Continuous (fun p : CompactCap × ℝ => niche p.1 grid p.2) := by
  unfold niche
  refine Continuous.finset_sup'_apply _ fun t _ => ?_
  exact continuous_fullWallClip_on_angles.comp (f := fun p : CompactCap × ℝ => (p, t)) (by fun_prop)

private theorem continuous_clip (U : CompactCap) (x : ℝ) :
    Continuous fun t : QuarterAngle => fullWallClip U x t :=
  continuous_fullWallClip_on_angles.comp (f := fun s : QuarterAngle => ((U, x), s)) (by fun_prop)

theorem niche_le_sweptNiche (U : CompactCap) (grid : Finset QuarterAngle) (x : ℝ) :
    niche U grid x ≤ sweptNiche U.carrier (Real.pi / 2) x := by
  refine (niche_le_iff U grid x _).mpr ⟨sweptNiche_nonneg _ _ _, fun t _ => ?_⟩
  rw [sweptNiche_eq_sSup_clipped]
  exact le_csSup (isCompact_univ.bddAbove_image (continuous_clip U x).continuousOn)
    (mem_image_of_mem _ (mem_univ t))

/-- Dense angular sampling supplies the least upper bound of the actual
finite niches; continuity is used only for the clipped physical walls. -/
theorem isLUB_niche (grids : ℕ → Finset QuarterAngle)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap) (x : ℝ) :
    IsLUB (range (fun n => niche U (grids n) x))
      (sweptNiche U.carrier (Real.pi / 2) x) := by
  refine ⟨forall_mem_range.2 fun n => niche_le_sweptNiche U (grids n) x, fun b hb => ?_⟩
  rw [sweptNiche_eq_sSup_clipped]
  refine csSup_le ⟨_, zeroAngle, mem_univ _, rfl⟩ (forall_mem_image.2 fun t _ => ?_)
  refine hdense.induction (P := fun t : QuarterAngle => fullWallClip U x t ≤ b) (fun s hs => ?_)
    (isClosed_le (continuous_clip U x) continuous_const) t
  obtain ⟨n, hn⟩ := mem_iUnion.mp hs
  exact (clip_le_niche U (grids n) x hn).trans (hb (mem_range_self n))

theorem tendsto_niche (grids : ℕ → Finset QuarterAngle) (hmono : Monotone grids)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap) (x : ℝ) :
    Tendsto (fun n => niche U (grids n) x) atTop
      (𝓝 (sweptNiche U.carrier (Real.pi / 2) x)) :=
  tendsto_atTop_isLUB (fun _ _ h => niche_mono U (hmono h) x)
    (isLUB_niche grids hdense U x)

/-- Uniform angular truncation on an entire compact cap domain. The cap,
horizontal point, height degeneracies, and zero-width limits all vary. -/
theorem tendstoUniformlyOn_niche_box (grids : ℕ → Finset QuarterAngle)
    (hmono : Monotone grids) (hdense : Dense (⋃ n, (grids n : Set QuarterAngle)))
    {B : Set Plane} (hB : IsCompact B) (l r : ℝ) :
    TendstoUniformlyOn (fun n (p : CompactCap × ℝ) => niche p.1 (grids n) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2)
      atTop (boxedCaps B ×ˢ Icc l r) :=
  Monotone.tendstoUniformlyOn_of_forall_tendsto ((isCompact_boxedCaps hB).prod isCompact_Icc)
    (fun n => (continuous_niche (grids n)).continuousOn)
    (fun p _ _ _ h => niche_mono p.1 (hmono h) p.2) continuous_capSweptNiche.continuousOn
    fun p _ => tendsto_niche grids hmono hdense p.1 p.2

end AngularGrid

end AmbidextrousSofa
