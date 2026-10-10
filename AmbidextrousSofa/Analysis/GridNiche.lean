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
    {t : QuarterAngle} (ht : t ∈ grid) : fullWallClip U x t ≤ niche U grid x := by
  classical
  unfold niche
  exact Finset.le_sup' (fun t : QuarterAngle => fullWallClip U x t) (Finset.mem_insert_of_mem ht)

theorem niche_nonneg (U : CompactCap) (grid : Finset QuarterAngle) (x : ℝ) :
    0 ≤ niche U grid x := by
  classical
  unfold niche
  have h := Finset.le_sup' (fun t : QuarterAngle => fullWallClip U x t)
    (Finset.mem_insert_self zeroAngle grid)
  simpa only [zeroAngle, fullWallClip_zero] using h

theorem niche_le_iff (U : CompactCap) (grid : Finset QuarterAngle) (x b : ℝ) :
    niche U grid x ≤ b ↔ 0 ≤ b ∧ ∀ t ∈ grid, fullWallClip U x t ≤ b := by
  classical
  unfold niche
  rw [Finset.sup'_le_iff]
  constructor
  · intro h
    refine ⟨?_, fun t ht => h t (Finset.mem_insert_of_mem ht)⟩
    simpa only [zeroAngle, fullWallClip_zero] using h zeroAngle (Finset.mem_insert_self _ _)
  · rintro ⟨hb, hgrid⟩ t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · simpa only [zeroAngle, fullWallClip_zero] using hb
    · exact hgrid t ht

theorem niche_mono (U : CompactCap) {grid grid' : Finset QuarterAngle}
    (hgrid : grid ⊆ grid') (x : ℝ) : niche U grid x ≤ niche U grid' x := by
  apply (niche_le_iff U grid x _).mpr
  exact ⟨niche_nonneg U grid' x, fun t ht => clip_le_niche U grid' x (hgrid ht)⟩

theorem continuous_niche (grid : Finset QuarterAngle) :
    Continuous (fun p : CompactCap × ℝ => niche p.1 grid p.2) := by
  classical
  unfold niche
  apply Continuous.finset_sup'_apply
  intro t _
  have h := continuous_fullWallClip_on_angles.comp
    (continuous_id.prodMk continuous_const :
      Continuous fun p : CompactCap × ℝ => ((p, t) : (CompactCap × ℝ) × QuarterAngle))
  exact h

theorem clip_le_sweptNiche (U : CompactCap) (x : ℝ) (t : QuarterAngle) :
    fullWallClip U x t ≤ sweptNiche U.carrier (Real.pi / 2) x := by
  rw [sweptNiche_eq_sSup_clipped]
  have hc' := continuous_fullWallClip_on_angles.comp
    (continuous_const.prodMk continuous_id : Continuous fun s : QuarterAngle => ((U, x), s))
  have hc : Continuous (fun t : QuarterAngle => fullWallClip U x t) := hc'
  exact le_csSup ((isCompact_univ : IsCompact (univ : Set QuarterAngle)).bddAbove_image
    hc.continuousOn) (mem_image_of_mem _ (mem_univ t))

theorem niche_le_sweptNiche (U : CompactCap) (grid : Finset QuarterAngle) (x : ℝ) :
    niche U grid x ≤ sweptNiche U.carrier (Real.pi / 2) x := by
  apply (niche_le_iff U grid x _).mpr
  exact ⟨sweptNiche_nonneg _ _ _, fun t _ => clip_le_sweptNiche U x t⟩

/-- Dense angular sampling supplies the least upper bound of the actual
finite niches; continuity is used only for the clipped physical walls. -/
theorem isLUB_niche (grids : ℕ → Finset QuarterAngle)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap) (x : ℝ) :
    IsLUB (range (fun n => niche U (grids n) x))
      (sweptNiche U.carrier (Real.pi / 2) x) := by
  refine ⟨?_, ?_⟩
  · rintro y ⟨n, rfl⟩
    exact niche_le_sweptNiche U (grids n) x
  · intro b hb
    have hclip : ∀ t : QuarterAngle, fullWallClip U x t ≤ b := by
      intro t
      refine hdense.induction (P := fun t : QuarterAngle => fullWallClip U x t ≤ b) ?_ ?_ t
      · intro s hs
        obtain ⟨n, hn⟩ := mem_iUnion.mp hs
        exact (clip_le_niche U (grids n) x hn).trans (hb (mem_range_self n))
      · have hc := continuous_fullWallClip_on_angles.comp
          (continuous_const.prodMk continuous_id : Continuous fun s : QuarterAngle => ((U, x), s))
        exact isClosed_le hc continuous_const
    rw [sweptNiche_eq_sSup_clipped]
    refine csSup_le ⟨fullWallClip U x zeroAngle, zeroAngle, mem_univ _, rfl⟩ ?_
    rintro y ⟨t, _, rfl⟩
    exact hclip t

theorem tendsto_niche (grids : ℕ → Finset QuarterAngle) (hmono : Monotone grids)
    (hdense : Dense (⋃ n, (grids n : Set QuarterAngle))) (U : CompactCap) (x : ℝ) :
    Tendsto (fun n => niche U (grids n) x) atTop
      (𝓝 (sweptNiche U.carrier (Real.pi / 2) x)) :=
  tendsto_atTop_isLUB (fun _ _ h => niche_mono U (hmono h) x)
    (isLUB_niche grids hdense U x)

/-- Uniform angular truncation on an entire compact cap domain. The cap,
horizontal point, height degeneracies, and zero-width limits all vary. -/
theorem tendstoUniformlyOn_niche (grids : ℕ → Finset QuarterAngle)
    (hmono : Monotone grids) (hdense : Dense (⋃ n, (grids n : Set QuarterAngle)))
    {C : Set CompactCap} (hC : IsCompact C) (l r : ℝ) :
    TendstoUniformlyOn (fun n (p : CompactCap × ℝ) => niche p.1 (grids n) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2) atTop (C ×ˢ Icc l r) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto (hC.prod isCompact_Icc)
    (fun n => (continuous_niche (grids n)).continuousOn)
    (fun p _ _ _ h => niche_mono p.1 (hmono h) p.2)
    continuous_capSweptNiche.continuousOn
  intro p _
  exact tendsto_niche grids hmono hdense p.1 p.2

theorem tendstoUniformlyOn_niche_box (grids : ℕ → Finset QuarterAngle)
    (hmono : Monotone grids) (hdense : Dense (⋃ n, (grids n : Set QuarterAngle)))
    {B : Set Plane} (hB : IsCompact B) (l r : ℝ) :
    TendstoUniformlyOn (fun n (p : CompactCap × ℝ) => niche p.1 (grids n) p.2)
      (fun p => sweptNiche p.1.carrier (Real.pi / 2) p.2)
      atTop (boxedCaps B ×ˢ Icc l r) :=
  tendstoUniformlyOn_niche grids hmono hdense (isCompact_boxedCaps hB) l r

/-- An explicit available dense exhaustion, useful independently of the
equally spaced grids used for adjacent-wall estimates. -/
def denseAngles : ℕ → QuarterAngle := by
  letI : Nonempty QuarterAngle := ⟨zeroAngle⟩
  exact denseSeq QuarterAngle

def exhaustion (n : ℕ) : Finset QuarterAngle := by
  classical
  exact (Finset.range n).image denseAngles

end AngularGrid

end AmbidextrousSofa
