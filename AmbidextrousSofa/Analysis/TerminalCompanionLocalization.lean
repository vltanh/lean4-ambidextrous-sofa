module

public import AmbidextrousSofa.Analysis.TerminalHistory

@[expose] public section

/-!
# Actual localization of a positive companion-wall maximum

Every support point contributes a smooth scalar companion wall. Once
the sine exceeds the distance from the queried abscissa to the cap's
left projection endpoint, each such point wall is strictly decreasing.
Using an actual support attainer therefore localizes the maximum of the
whole companion support family, even when that support is nonsmooth.

At an interior maximum, a fixed attaining support point itself has a
local maximum. Its elementary derivative proves both contact-coordinate
identities.
-/

noncomputable section

open Set Filter

namespace AmbidextrousSofa

def companionPointWall (p : Plane) (x t : ℝ) : ℝ :=
  p.2 + ((x - p.1) * Real.sin t - 1) / Real.cos t

theorem companionPointWall_eq {p : Plane} {x t : ℝ} (hc : Real.cos t ≠ 0) :
    companionPointWall p x t =
      (coordDot p (companionNormal t) - 1 + x * Real.sin t) / Real.cos t := by
  unfold companionPointWall coordDot companionNormal
  field_simp
  ring

theorem companionPointWall_le_secondWall {U : Set Plane}
    (hU : IsDownwardCap U) {p : Plane} (hp : p ∈ U) {x t : ℝ}
    (hc : 0 < Real.cos t) : companionPointWall p x t ≤ secondWall U t x := by
  rw [companionPointWall_eq hc.ne', secondWall]
  exact div_le_div_of_nonneg_right
    (by linarith [coordDot_le_support hU.isCompact hp (companionNormal t)]) hc.le

theorem companionPointWall_eq_secondWall_of_support {U : Set Plane}
    {p : Plane} {x t : ℝ} (hc : Real.cos t ≠ 0)
    (hp : coordDot p (companionNormal t) = support U (companionNormal t)) :
    companionPointWall p x t = secondWall U t x := by
  rw [companionPointWall_eq hc, hp]; rfl

theorem hasDerivAt_companionPointWall {p : Plane} {x t : ℝ}
    (hc : Real.cos t ≠ 0) :
    HasDerivAt (companionPointWall p x)
      ((x - p.1 - Real.sin t) / Real.cos t ^ 2) t := by
  refine (((((Real.hasDerivAt_sin t).const_mul (x - p.1)).sub_const 1).div
    (Real.hasDerivAt_cos t) hc).const_add p.2).congr_deriv ?_
  congr 1
  linear_combination (x - p.1) * Real.sin_sq_add_cos_sq t

/-- The actual support wall is strictly lower at every angle after
the projection-controlled prefix. -/
theorem IsDownwardCap.secondWall_lt_of_late_angle {U : Set Plane}
    (hU : IsDownwardCap U) {x β t : ℝ}
    (hβ0 : 0 ≤ β) (hβt : β < t) (htL : t < Real.pi / 2)
    (hx : x - horizontalLeft U ≤ Real.sin β) :
    secondWall U t x < secondWall U β x := by
  obtain ⟨p, hp, hsupport⟩ :=
    exists_coordDot_eq_support hU.isCompact hU.nonempty (companionNormal t)
  have hp1 : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) :=
    horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex ▸ ⟨p, hp, rfl⟩
  have hcos (s : ℝ) (hs : s ∈ Icc β t) : 0 < Real.cos s :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1, Real.pi_pos], hs.2.trans_lt htL⟩
  -- The wall of the fixed support point `p` decreases on `[β, t]`.
  have hanti : StrictAntiOn (companionPointWall p x) (Icc β t) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun s hs =>
      (hasDerivAt_companionPointWall (hcos s hs).ne').continuousAt.continuousWithinAt) ?_
    intro s hs
    rw [interior_Icc] at hs
    have hcs := hcos s ⟨hs.1.le, hs.2.le⟩
    rw [(hasDerivAt_companionPointWall hcs.ne').deriv]
    have := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos])
      (hs.2.trans htL).le hs.1
    exact div_neg_of_neg_of_pos (by linarith [hp1.1]) (sq_pos_of_pos hcs)
  calc
    _ = companionPointWall p x t :=
      (companionPointWall_eq_secondWall_of_support (hcos t ⟨hβt.le, le_rfl⟩).ne' hsupport).symm
    _ < companionPointWall p x β := hanti ⟨le_rfl, hβt.le⟩ ⟨hβt.le, le_rfl⟩ hβt
    _ ≤ _ := companionPointWall_le_secondWall hU hp (hcos β ⟨le_rfl, hβt.le⟩)

/-- The localized maximum of the second wall, at an attaining support point. Stationarity is proved
for a fixed attaining point, so no differentiability of the cap support
is required, even at the localization endpoint. -/
theorem IsDownwardCap.exists_positive_localized_secondWall_max {U : Set Plane}
    (hU : IsDownwardCap U) {α B x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hB0 : 0 ≤ B) (hBα : B < Real.sin α)
    (hx : x - horizontalLeft U ≤ B)
    (hpositive : ∃ r ∈ Icc 0 α, 0 < secondWall U r x) :
    ∃ t ∈ Ioo 0 α, t ≤ Real.arcsin B ∧ IsMaxOn (fun r => secondWall U r x) (Icc 0 α) t ∧
      (MovingSofaOptimality.vplus U (t + Real.pi / 2)).1 + Real.sin t = x ∧
      secondWall U t x = (MovingSofaOptimality.vplus U (t + Real.pi / 2)).2 - Real.cos t := by
  have hcos (r : ℝ) (hr : r ∈ Icc 0 α) : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1, Real.pi_pos], hr.2.trans_lt hαL⟩
  have hβ0 : 0 ≤ Real.arcsin B := Real.arcsin_nonneg.mpr hB0
  have hβα : Real.arcsin B < α :=
    (Real.arcsin_lt_iff_lt_sin' ⟨by linarith [Real.pi_pos], hαL.le⟩).2 hBα
  -- A maximum over `[0, α]` exists, and it lies before `arcsin B`.
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hα0.le⟩ fun r hr =>
    (hU.secondWall_continuousAt_angle (hcos r hr).ne' x).continuousWithinAt
  have htB : t ≤ Real.arcsin B := not_lt.1 fun hlate => (hmax ⟨hβ0, hβα.le⟩).not_gt
    (hU.secondWall_lt_of_late_angle hβ0 hlate (ht.2.trans_lt hαL) (by
      rwa [Real.sin_arcsin (by linarith) (hBα.trans_le (Real.sin_le_one α)).le]))
  obtain ⟨r, hr, hpos⟩ := hpositive
  have htpos : 0 < secondWall U t x := hpos.trans_le (hmax hr)
  -- The wall at angle `0` is nonpositive, so the maximum is interior.
  have ht0 : 0 < t := ht.1.lt_of_ne <| by
    rintro rfl
    exact htpos.not_ge (by simpa [secondWall, companionNormal, capHeight] using hU.capHeight_le_one)
  have htα : t < α := htB.trans_lt hβα
  have hct := hcos t ⟨ht0.le, htα.le⟩
  set p := MovingSofaOptimality.vplus U (t + Real.pi / 2)
  have hp : p ∈ U := (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody _).1
  have hpeq := companionPointWall_eq_secondWall_of_support (x := x) hct.ne'
    (by rw [companionNormal_eq_unitNormal]; exact MovingSofaOptimality.dot_vplus_uvec U _)
  -- The wall of the attaining point `p` has an interior maximum at `t`.
  have hpmax : IsMaxOn (companionPointWall p x) (Icc 0 α) t := fun r hr =>
    ((companionPointWall_le_secondWall hU hp (hcos r hr)).trans (hmax hr)).trans_eq hpeq.symm
  have hstation := (div_eq_iff (pow_ne_zero 2 hct.ne')).mp
    ((hpmax.isLocalMax (Icc_mem_nhds ht0 htα)).hasDerivAt_eq_zero
      (hasDerivAt_companionPointWall hct.ne'))
  refine ⟨t, ⟨ht0, htα⟩, htB, hmax, by linarith, ?_⟩
  rw [← hpeq, companionPointWall, show x - p.1 = Real.sin t by linarith]
  field_simp
  linear_combination Real.sin_sq_add_cos_sq t

end AmbidextrousSofa
