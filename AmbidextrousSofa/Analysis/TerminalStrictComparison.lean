module

public import AmbidextrousSofa.Analysis.TerminalCompanionComparison
public import AmbidextrousSofa.Analysis.TerminalExposure
public import AmbidextrousSofa.Analysis.CanonicalOneTurn

@[expose] public section

/-!
# Two steps of the strict terminal comparison

Under the cosine cut, every companion abscissa of the terminal reserve
interval stays below the terminal sine, so the circle comparison applies
there. A continuous strict gap on a closed initial interval persists past
its right endpoint, so the measure of the strict region exceeds the length
of that interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem terminal_circle_reserve_localization {C c s z : ℝ}
    (hC : C ≤ 37 / 50) (hc : 0 < c) (hcut : 73 * c ^ 2 ≤ 9)
    (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1) (hz : z ≤ c / 2) :
    C + z < s := by
  have hslow : (187 / 200 : ℝ) < s := by nlinarith only [hs, hcs, hcut]
  linarith only [hC, hz, hslow, terminal_cosine_lt_forty_four_one_twenty_fifths hc hcut]

/-- A continuous strict gap on a complete closed initial interval
persists beyond its right endpoint. Consequently its measure is
strictly larger than the length of that interval. -/
theorem volume_real_strict_region_gt_of_initial_interval
    {f g : ℝ → ℝ} {l r w : ℝ} (hf : Continuous f) (hg : Continuous g)
    (hw : 0 ≤ w) (hwr : l + w < r)
    (hstrict : ∀ x ∈ Icc l (l + w), f x < g x) :
    w < volume.real (Icc l r ∩ {x | f x < g x}) := by
  obtain ⟨a, b, hab, hlocal⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((isOpen_lt hf hg).mem_nhds (hstrict (l + w) ⟨by linarith only [hw], le_rfl⟩))
  obtain ⟨q, hq0, hq1⟩ := exists_between (lt_min hab.2 hwr)
  have hsub : Icc l q ⊆ Icc l r ∩ {x | f x < g x} := fun x hx =>
    ⟨⟨hx.1, hx.2.trans (hq1.trans_le (min_le_right _ _)).le⟩,
      (le_or_gt x (l + w)).elim (fun hxw => hstrict x ⟨hx.1, hxw⟩) fun hxw =>
        hlocal ⟨hab.1.trans hxw, hx.2.trans_lt (hq1.trans_le (min_le_left _ _))⟩⟩
  have hmeasure := measureReal_mono (μ := volume) hsub
    (measure_ne_top_of_subset inter_subset_left measure_Icc_lt_top.ne)
  rw [Real.volume_real_Icc_of_le (by linarith only [hq0, hw])] at hmeasure
  linarith only [hq0, hmeasure]

end AmbidextrousSofa
