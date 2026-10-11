module

public import AmbidextrousSofa.Analysis.WallVisibility
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# The actual angular flux bound on two visible graph pieces

The finite graph projection is passed through the selected polygons.
Every source is localized by an actual maximizing wall angle in `(s, t)`.
Projected onto the direction `θ ∈ [s, t]`, the second family carries its
full length and the first family at most `t - s` times its length; onto
`θ - π / 2`, the roles of the two families are exchanged. The two spatial
pieces are disjoint, so each angular mass is charged only once. Thus
shrinking the angular interval produces a second-order error under the
proved bounded curvature density; no ordinary perimeter continuity is used.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

def nicheGraphProjection (U : Set Plane) (t l r : ℝ) : ℝ :=
  Real.cos t * (r - l) + Real.sin t *
    (sweptNiche U (Real.pi / 2) r - sweptNiche U (Real.pi / 2) l)

namespace AngularGrid

/-- A source whose quarter angle lies in `(s, t)` is a first-family source in `(s, t]` or a
second-family source in `(s + π / 2, t + π / 2]`. For `θ ∈ [s, t]`, the first family projects
at most `t - s` onto the direction `θ`, and the second family onto `θ - π / 2`. -/
theorem localized_quarter_source (grid : Finset QuarterAngle) {s t θ : ℝ} (hθ : θ ∈ Icc s t)
    (j : SourceIndex grid) (hj : sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t) :
    (fullAngle grid j ∈ Ioc (s + Real.pi / 2) (t + Real.pi / 2) ∨
      fullAngle grid j ∈ Ioc s t ∧ Real.sin (fullAngle grid j - θ) ≤ t - s) ∧
    (fullAngle grid j ∈ Ioc s t ∨ fullAngle grid j ∈ Ioc (s + Real.pi / 2) (t + Real.pi / 2) ∧
      Real.sin (fullAngle grid j - (θ - Real.pi / 2)) ≤ t - s) := by
  rw [sourceQuarterAngle_fullAngle] at hj
  have hsin {u : ℝ} (hu : u ∈ Ioo s t) : |Real.sin (u - θ)| ≤ t - s :=
    Real.abs_sin_le_abs.trans (abs_le.mpr ⟨by linarith [hu.1, hθ.2], by linarith [hu.2, hθ.1]⟩)
  rcases j with u | u
  · exact ⟨.inr ⟨⟨hj.1, hj.2.le⟩, (le_abs_self _).trans (hsin hj)⟩, .inl ⟨hj.1, hj.2.le⟩⟩
  · simp only [Sum.elim_inr] at hj
    simp only [fullAngle, mem_Ioc, add_lt_add_iff_right, add_le_add_iff_right,
      show (u.val : ℝ) + Real.pi / 2 - (θ - Real.pi / 2) = u.val - θ + Real.pi by ring,
      Real.sin_add_pi]
    exact ⟨.inl ⟨hj.1, hj.2.le⟩, .inr ⟨⟨hj.1, hj.2.le⟩, (neg_le_abs _).trans (hsin hj)⟩⟩

end AngularGrid

open AngularGrid in
/-- The finite flux bound of selected polygons, passed to the limit; the
polygons are constructed here. Every source over the two closed pieces has
its quarter angle in `(s, t)`, and `hsource` charges it to `Ioc a b` or,
with a projection at most `δ`, to `Ioc a' b'`. -/
theorem IsFullCapMaximizer.nicheGraphProjection_add_le_curvature
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t φ δ a b a' b' l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hab : a ≤ b) (hregular : Icc a b ⊆ regularCurvatureDomain m)
    (hab' : a' ≤ b') (hregular' : Icc a' b' ⊆ regularCurvatureDomain m) (hδ : 0 ≤ δ)
    (hsource : ∀ (grid : Finset QuarterAngle) (j : SourceIndex grid),
      sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t → fullAngle grid j ∈ Ioc a b ∨
        fullAngle grid j ∈ Ioc a' b' ∧ Real.sin (fullAngle grid j - φ) ≤ δ)
    (hL : horizontalLeft U + capWidth U / 4 < l₁)
    (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂)
    (hR : r₂ < horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂, ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
      fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x → u ∈ Ioo s t) :
    nicheGraphProjection U φ l₁ r₁ + nicheGraphProjection U φ l₂ r₂ ≤
      (upperCurvature U).real (Ioc a b) +
        δ * ((upperCurvature U).real (Ioc a b) + (upperCurvature U).real (Ioc a' b')) := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hwidth : 0 ≤ capWidth U := sub_nonneg.mpr hlr
  obtain ⟨A, B, hleft, hright, hbox⟩ : ∃ A B : ℝ, A < horizontalLeft U ∧
      horizontalRight U < B ∧ U ⊆ Icc A B ×ˢ Icc (0 : ℝ) 1 :=
    ⟨_, _, sub_one_lt _, lt_add_one _, fun P hP => ⟨Icc_subset_Icc (sub_one_lt _).le
      (lt_add_one _).le (hU.isCap.fst_mem_Icc hP), hU.isCap.inStrip hP⟩⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, -, hHausdorff⟩ :=
    exists_selected_sequence hU (by linarith) hbox
  replace hlevel := tendsto_atTop_mono hlevel tendsto_id
  have hcap n : IsDownwardCap (V n) := (hV n).isCap
  have hFbox : Icc l₁ r₁ ∪ Icc l₂ r₂ ⊆ Icc A B := by
    rintro x (hx | hx) <;> constructor <;> linarith [hx.1, hx.2]
  have hF : IsCompact (Icc l₁ r₁ ∪ Icc l₂ r₂) := isCompact_Icc.union isCompact_Icc
  have hw := (hHausdorff.capWidth_tendsto hcap hU.isCap).div_const 4
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hmass {p q : ℝ} (hpq : p ≤ q) (hreg : Icc p q ⊆ regularCurvatureDomain m) :=
    innerAngularMass_Ioc_tendsto_of_canonical_maximum hU hheight haffine hbox
      hV hHausdorff hlevel (fun n => (hc n).le) hrate hleft hright hpq hreg
  have hN {x : ℝ} (hx : x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂) := finiteBarrier_dyadic_tendsto hHausdorff hcap
    hU.isCap hlevel (fun n => (hV n).inBox) (fun _ => hFbox hx) tendsto_const_nhds
  have hg {l r : ℝ} (hl : l ∈ Icc l₁ r₁ ∪ Icc l₂ r₂) (hr : r ∈ Icc l₁ r₁ ∪ Icc l₂ r₂) :
      Tendsto (fun n => finiteGraphProjection (V n) (dyadic (level n)) φ l r) atTop
        (𝓝 (nicheGraphProjection U φ l r)) :=
    tendsto_const_nhds.add (((hN hr).sub (hN hl)).const_mul _)
  refine le_of_tendsto_of_tendsto
    ((hg (.inl (left_mem_Icc.mpr h₁)) (.inl (right_mem_Icc.mpr h₁))).add
      (hg (.inr (left_mem_Icc.mpr h₂)) (.inr (right_mem_Icc.mpr h₂))))
    ((hmass hab hregular).add (((hmass hab hregular).add (hmass hab' hregular')).const_mul δ)) ?_
  filter_upwards [eventually_finiteBarrier_pos_on_compact hHausdorff hcap hU.isCap hlevel
      (fun n => (hV n).inBox) hF hFbox hpositive,
    eventually_innerSources_in_open_of_maximizers hHausdorff hcap hU.isCap hlevel
      (fun n => (hV n).inBox) hF hFbox isOpen_Ioo hmaximizers,
    (hl.add hw).eventually_lt_const hL, (hr.sub hw).eventually_const_lt hR]
    with n hnpos hnlocal hnL hnR
  have hsub := union_subset_union (Ioc_subset_Icc_self (a := l₁) (b := r₁))
    (Ioc_subset_Icc_self (a := l₂) (b := r₂))
  exact finiteGraphProjection_add_le_sources (V n) (dyadic (level n)) hnL.le h₁ hgap h₂ hnR.le hδ
    (fun x hx => hnpos x (hsub hx)) fun x hx j hj => hsource _ j (hnlocal x (hsub hx) j hj)

end AmbidextrousSofa
