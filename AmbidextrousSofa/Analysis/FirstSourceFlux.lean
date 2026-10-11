module

public import AmbidextrousSofa.Analysis.OpenGraphFlux

@[expose] public section

/-!
# First-family flux of visible core and tangent pieces

The projection onto the increasing first-wall tangent isolates the
first-family source mass. Its transverse companion contribution is
bounded by the angular interval length times the actual total source
mass. Open spatial pieces suffice, including a collapsed first-tangency
piece. All measures and selected polygons in the comparison are the
literal ones belonging to the prescribed full maximum.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace AmbidextrousSofa

theorem AngularGrid.localized_quarter_first_source_projection (grid : Finset QuarterAngle)
    {s t θ : ℝ} (hθ : θ ∈ Icc s t) (j : SourceIndex grid)
    (hj : sourceQuarterAngle (fullAngle grid j) ∈ Ioo s t) :
    fullAngle grid j ∈ Ioc s t ∨
      (fullAngle grid j ∈ Ioc (s + Real.pi / 2) (t + Real.pi / 2) ∧
        Real.sin (fullAngle grid j - (θ - Real.pi / 2)) ≤ t - s) := by
  rw [sourceQuarterAngle_fullAngle] at hj
  rcases j with u | u
  · exact Or.inl ⟨hj.1, hj.2.le⟩
  · simp only [Sum.elim_inr] at hj
    simp only [fullAngle, mem_Ioc, add_lt_add_iff_right, add_le_add_iff_right,
      show (u.val : ℝ) + Real.pi / 2 - (θ - Real.pi / 2) = u.val - θ + Real.pi by ring,
      Real.sin_add_pi]
    exact Or.inr ⟨⟨hj.1, hj.2.le⟩, (neg_le_abs _).trans (Real.abs_sin_le_abs.trans
      (abs_le.mpr ⟨by linarith [hj.1, hθ.2], by linarith [hj.2, hθ.1]⟩))⟩

open AngularGrid in
/-- The finite flux bound of selected polygons, passed to the limit. -/
theorem IsFullCapMaximizer.firstGraphProjection_add_le_curvature
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft U + capWidth U / 4 < l₁)
    (h₁ : l₁ ≤ r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ ≤ r₂)
    (hR : r₂ < horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Icc l₁ r₁ ∪ Icc l₂ r₂,
      ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x →
          u ∈ Ioo s t) :
    nicheGraphProjection U (θ - Real.pi / 2) l₁ r₁ +
        nicheGraphProjection U (θ - Real.pi / 2) l₂ r₂ ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hwidth : 0 ≤ capWidth U := sub_nonneg.mpr hlr
  obtain ⟨a, b, hleft, hright, hbox⟩ : ∃ a b : ℝ, a < horizontalLeft U ∧
      horizontalRight U < b ∧ U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 :=
    ⟨_, _, sub_one_lt _, lt_add_one _, fun P hP => ⟨Icc_subset_Icc (sub_one_lt _).le
      (lt_add_one _).le (hU.isCap.fst_mem_Icc hP), hU.isCap.inStrip hP⟩⟩
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    exists_selected_sequence hU (by linarith) hbox
  replace hlevel := tendsto_atTop_mono hlevel tendsto_id
  have hcap n : IsDownwardCap (V n) := (hV n).isCap
  have hFbox : Icc l₁ r₁ ∪ Icc l₂ r₂ ⊆ Icc a b := by
    rintro x (hx | hx) <;> constructor <;> linarith [hx.1, hx.2]
  have hF : IsCompact (Icc l₁ r₁ ∪ Icc l₂ r₂) := isCompact_Icc.union isCompact_Icc
  have hw := (hHausdorff.capWidth_tendsto hcap hU.isCap).div_const 4
  have hl := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hr := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hU.isCap.isCompact hU.isCap.nonempty
  have hδ : 0 ≤ t - s := sub_nonneg.mpr (hθ.1.trans hθ.2)
  have hbase := innerAngularMass_Ioc_tendsto_of_canonical_maximum hU hheight haffine hbox
    hV hHausdorff hlevel (fun n => (hc n).le) hrate hleft hright (hθ.1.trans hθ.2) hregular
  have hcomp := innerAngularMass_Ioc_tendsto_of_canonical_maximum hU hheight haffine hbox
    hV hHausdorff hlevel (fun n => (hc n).le) hrate hleft hright
    (by linarith [hθ.1, hθ.2] : s + Real.pi / 2 ≤ t + Real.pi / 2) hshift
  have hg {l r : ℝ} (hl : l ∈ Icc a b) (hr : r ∈ Icc a b) := finiteGraphProjection_tendsto
    (θ := θ - Real.pi / 2) hHausdorff hcap hU.isCap hlevel (fun n => (hV n).inBox) hl hr
  refine le_of_tendsto_of_tendsto
    ((hg (hFbox (.inl (left_mem_Icc.mpr h₁))) (hFbox (.inl (right_mem_Icc.mpr h₁)))).add
      (hg (hFbox (.inr (left_mem_Icc.mpr h₂))) (hFbox (.inr (right_mem_Icc.mpr h₂)))))
    (hbase.add ((hbase.add hcomp).const_mul (t - s))) ?_
  filter_upwards [eventually_finiteBarrier_pos_on_compact hHausdorff hcap hU.isCap hlevel
      (fun n => (hV n).inBox) hF hFbox hpositive,
    eventually_innerSources_in_open_of_maximizers hHausdorff hcap hU.isCap hlevel
      (fun n => (hV n).inBox) hF hFbox isOpen_Ioo hmaximizers,
    (hl.add hw).eventually_lt_const hL, (hr.sub hw).eventually_const_lt hR]
    with n hnpos hnlocal hnL hnR
  have hbound := finiteGraphProjection_add_le_sources (V n) (dyadic (level n))
    hnL.le h₁ hgap h₂ hnR.le hδ
    (fun x hx => hnpos x (.inl (Ioc_subset_Icc_self hx)))
    (fun x hx => hnpos x (.inr (Ioc_subset_Icc_self hx)))
    (fun x hx j hj => localized_quarter_first_source_projection _ hθ j
      (hnlocal x (.inl (Ioc_subset_Icc_self hx)) j hj))
    (fun x hx j hj => localized_quarter_first_source_projection _ hθ j
      (hnlocal x (.inr (Ioc_subset_Icc_self hx)) j hj))
  have hm := innerAngularMassOn_union_le (V n) (dyadic (level n)) (Ioc s t)
    (Ioc (s + Real.pi / 2) (t + Real.pi / 2))
    (hnL.le.trans (h₁.trans (hgap.trans (h₂.trans hnR.le))))
  simp only [innerAngularMassOn_middle] at hbound hm
  exact hbound.trans (add_le_add_right (mul_le_mul_of_nonneg_left hm hδ) _)

/-- Two strict open pieces suffice: linear interior cutoffs and continuity
of the actual niche recover their closed endpoint chords. -/
theorem IsFullCapMaximizer.firstGraphProjection_add_le_curvature_of_open_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ l₁ r₁ l₂ r₂ : ℝ}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (hL : horizontalLeft U + capWidth U / 4 ≤ l₁)
    (h₁ : l₁ < r₁) (hgap : r₁ ≤ l₂) (h₂ : l₂ < r₂)
    (hR : r₂ ≤ horizontalRight U - capWidth U / 4)
    (hpositive : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂, 0 < sweptNiche U (Real.pi / 2) x)
    (hmaximizers : ∀ x ∈ Ioo l₁ r₁ ∪ Ioo l₂ r₂,
      ∀ u ∈ Icc (0 : ℝ) (Real.pi / 2),
        fullWallClip hU.isCap.toCompactCap x u = sweptNiche U (Real.pi / 2) x → u ∈ Ioo s t) :
    nicheGraphProjection U (θ - Real.pi / 2) l₁ r₁ +
        nicheGraphProjection U (θ - Real.pi / 2) l₂ r₂ ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  have hε : Tendsto (fun n => AngularGrid.selectionRate n / 4) atTop (𝓝 0) := by
    simpa only [zero_div] using AngularGrid.selectionRate_tendsto.div_const 4
  have hlim (l r : ℝ) := hU.isCap.nicheGraphProjection_tendsto (θ := θ - Real.pi / 2)
    ((tendsto_const_nhds (x := l)).add (hε.mul_const (r - l)))
    ((tendsto_const_nhds (x := r)).sub (hε.mul_const (r - l)))
  simp only [zero_mul, add_zero, sub_zero] at hlim
  refine le_of_tendsto' ((hlim l₁ r₁).add (hlim l₂ r₂)) fun n => ?_
  have hn := fluxInset_bounds n
  obtain ⟨a₁, b₁, c₁⟩ := fluxInset_interval h₁ hn.1 hn.2
  obtain ⟨a₂, b₂, c₂⟩ := fluxInset_interval h₂ hn.1 hn.2
  have hsub := union_subset_union (Icc_subset_Ioo a₁ c₁) (Icc_subset_Ioo a₂ c₂)
  exact hU.firstGraphProjection_add_le_curvature hheight haffine hθ hregular hshift
    (hL.trans_lt a₁) b₁.le (c₁.le.trans (hgap.trans a₂.le)) b₂.le (c₂.trans_le hR)
    (fun x hx => hpositive x (hsub hx)) (fun x hx => hmaximizers x (hsub hx))

/-- A literal visible core chord. Every maximizing angle over its open
spatial projection lies in the stated parameter interval. -/
structure FirstSourceCorePiece {U : Set Plane} (hU : IsDownwardCap U)
    (Z : ℝ → Plane) (s t : ℝ) : Prop where
  reversed : (Z t).1 < (Z s).1
  middle_left : horizontalLeft U + capWidth U / 4 ≤ (Z t).1
  middle_right : (Z s).1 ≤ horizontalRight U - capWidth U / 4
  contact_s : sweptNiche U (Real.pi / 2) (Z s).1 = (Z s).2
  contact_t : sweptNiche U (Real.pi / 2) (Z t).1 = (Z t).2
  positive : ∀ x ∈ Ioo (Z t).1 (Z s).1, 0 < sweptNiche U (Real.pi / 2) x
  localizes : ∀ x ∈ Ioo (Z t).1 (Z s).1, ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t

/-- Two disjoint literal graph pieces. The first tangent may be a
plateau; its zero projection is then retained exactly. -/
structure FirstSourceChargedPieces {U : Set Plane} (hU : IsDownwardCap U)
    (B Z : ℝ → Plane) (s t : ℝ) : Prop where
  core : FirstSourceCorePiece hU Z s t
  tangent_order : (B s).1 ≤ (B t).1
  separation : (Z s).1 ≤ (B s).1
  middle_right : (B t).1 ≤ horizontalRight U - capWidth U / 4
  contact_s : sweptNiche U (Real.pi / 2) (B s).1 = (B s).2
  contact_t : sweptNiche U (Real.pi / 2) (B t).1 = (B t).2
  positive : ∀ x ∈ Ioo (B s).1 (B t).1, 0 < sweptNiche U (Real.pi / 2) x
  localizes : ∀ x ∈ Ioo (B s).1 (B t).1, ∀ v ∈ Icc (0 : ℝ) (Real.pi / 2),
    fullWallClip hU.toCompactCap x v = sweptNiche U (Real.pi / 2) x → v ∈ Ioo s t

theorem IsFullCapMaximizer.first_source_flux_of_core_piece
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ : ℝ} {Z : ℝ → Plane}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (H : FirstSourceCorePiece hU.isCap Z s t) :
    Real.sin θ * ((Z s).1 - (Z t).1) - Real.cos θ * ((Z s).2 - (Z t).2) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  -- Split the core chord at its midpoint into two strict open pieces.
  have hl := left_lt_add_div_two.mpr H.reversed
  have hr := add_div_two_lt_right.mpr H.reversed
  have hsub := union_subset (Ioo_subset_Ioo_right hr.le) (Ioo_subset_Ioo_left hl.le)
  have h := hU.firstGraphProjection_add_le_curvature_of_open_pieces hheight haffine hθ
    hregular hshift H.middle_left hl le_rfl hr H.middle_right
    (fun x hx => H.positive x (hsub hx)) (fun x hx => H.localizes x (hsub hx))
  simp only [nicheGraphProjection, H.contact_s, H.contact_t, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two] at h
  linarith

theorem IsFullCapMaximizer.first_source_flux_of_charged_pieces
    {U : Set Plane} (hU : IsFullCapMaximizer U) {m c s t θ : ℝ} {B Z : ℝ → Plane}
    (hheight : capHeight U = 1)
    (haffine : ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c)
    (hθ : θ ∈ Icc s t)
    (hregular : Icc s t ⊆ regularCurvatureDomain m)
    (hshift : Icc (s + Real.pi / 2) (t + Real.pi / 2) ⊆ regularCurvatureDomain m)
    (H : FirstSourceChargedPieces hU.isCap B Z s t) :
    Real.sin θ * ((Z s).1 - (Z t).1) - Real.cos θ * ((Z s).2 - (Z t).2) +
      (Real.sin θ * ((B t).1 - (B s).1) - Real.cos θ * ((B t).2 - (B s).2)) ≤
      (upperCurvature U).real (Ioc s t) +
        (t - s) * ((upperCurvature U).real (Ioc s t) +
          (upperCurvature U).real (Ioc (s + Real.pi / 2) (t + Real.pi / 2))) := by
  rcases H.tangent_order.eq_or_lt with h | h
  · -- A collapsed tangent piece contributes zero.
    have hB : (B t).2 = (B s).2 := by rw [← H.contact_t, ← H.contact_s, h]
    simpa only [h, hB, sub_self, mul_zero, sub_zero, add_zero] using
      hU.first_source_flux_of_core_piece hheight haffine hθ hregular hshift H.core
  have h := hU.firstGraphProjection_add_le_curvature_of_open_pieces hheight haffine hθ
    hregular hshift H.core.middle_left H.core.reversed H.separation h H.middle_right
    (fun x hx => hx.elim (H.core.positive x) (H.positive x))
    (fun x hx => hx.elim (H.core.localizes x) (H.localizes x))
  simp only [nicheGraphProjection, H.core.contact_s, H.core.contact_t, H.contact_s,
    H.contact_t, Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two] at h
  linarith

end AmbidextrousSofa
