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
identities. No curvature density or derivative of the support function
is required for this geometric step.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

def companionPointWall (p : Plane) (x t : ℝ) : ℝ :=
  p.2 + ((x - p.1) * Real.sin t - 1) / Real.cos t

theorem companionPointWall_eq {p : Plane} {x t : ℝ} (hc : Real.cos t ≠ 0) :
    companionPointWall p x t =
      (coordDot p (companionNormal t) - 1 + x * Real.sin t) / Real.cos t := by
  unfold companionPointWall coordDot companionNormal
  field_simp [hc] <;> ring

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
  rw [companionPointWall_eq hc, hp]
  rfl

theorem hasDerivAt_companionPointWall {p : Plane} {x t : ℝ}
    (hc : Real.cos t ≠ 0) :
    HasDerivAt (companionPointWall p x)
      ((x - p.1 - Real.sin t) / Real.cos t ^ 2) t := by
  have hn := ((Real.hasDerivAt_sin t).const_mul (x - p.1)).sub_const 1
  have hd := (hn.div (Real.hasDerivAt_cos t) hc).const_add p.2
  apply hd.congr_deriv
  congr 1
  have hcircle := congrArg (fun z : ℝ => (x - p.1) * z) (Real.sin_sq_add_cos_sq t)
  nlinarith only [hcircle]

theorem companionPointWall_strictAntiOn {p : Plane} {x β α : ℝ}
    (hβ0 : 0 ≤ β) (hβα : β ≤ α) (hαL : α < Real.pi / 2)
    (hx : x - p.1 ≤ Real.sin β) :
    StrictAntiOn (companionPointWall p x) (Icc β α) := by
  have hcos (t : ℝ) (ht : t ∈ Icc β α) : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2.trans_lt hαL⟩
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun t ht => (hasDerivAt_companionPointWall (hcos t ht).ne').continuousAt.continuousWithinAt)
  intro t ht
  rw [interior_Icc] at ht
  have hct := hcos t ⟨ht.1.le, ht.2.le⟩
  rw [(hasDerivAt_companionPointWall hct.ne').deriv]
  have hsin : Real.sin β < Real.sin t := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (by linarith [Real.pi_pos]) (ht.2.le.trans hαL.le) ht.1
  exact div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hct)

/-- The actual support wall is strictly lower at every angle after
the projection-controlled prefix. This does not assume smooth support. -/
theorem IsDownwardCap.secondWall_lt_of_late_angle {U : Set Plane}
    (hU : IsDownwardCap U) {x β t : ℝ}
    (hβ0 : 0 ≤ β) (hβt : β < t) (htL : t < Real.pi / 2)
    (hx : x - horizontalLeft U ≤ Real.sin β) :
    secondWall U t x < secondWall U β x := by
  obtain ⟨p, hp, hsupport⟩ :=
    exists_coordDot_eq_support hU.isCompact hU.nonempty (companionNormal t)
  have hproj : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
    rw [← horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact ⟨p, hp, rfl⟩
  have hct : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], htL⟩
  have hcβ : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hβt.trans htL⟩
  have hanti := companionPointWall_strictAntiOn hβ0 hβt.le htL
    (show x - p.1 ≤ Real.sin β by linarith [hproj.1])
  calc
    _ = companionPointWall p x t :=
      (companionPointWall_eq_secondWall_of_support hct.ne' hsupport).symm
    _ < companionPointWall p x β := hanti ⟨le_rfl, hβt.le⟩ ⟨hβt.le, le_rfl⟩ hβt
    _ ≤ _ := companionPointWall_le_secondWall hU hp hcβ

theorem IsDownwardCap.secondWall_zero_nonpos {U : Set Plane}
    (hU : IsDownwardCap U) (x : ℝ) : secondWall U 0 x ≤ 0 := by
  have hs : support U (companionNormal 0) ≤ 1 := by
    apply support_le_of_forall hU.nonempty
    intro p hp
    simpa only [coordDot, companionNormal, Real.sin_zero, Real.cos_zero,
      neg_zero, mul_zero, mul_one, zero_add] using (hU.inStrip hp).2
  simpa only [secondWall, Real.sin_zero, Real.cos_zero, mul_zero, add_zero, div_one]
    using sub_nonpos.mpr hs

theorem IsDownwardCap.exists_localized_secondWall_max {U : Set Plane}
    (hU : IsDownwardCap U) {α B x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hB0 : 0 ≤ B) (hBα : B < Real.sin α)
    (hx : x - horizontalLeft U ≤ B) :
    ∃ t ∈ Icc 0 (Real.arcsin B), IsMaxOn (fun r => secondWall U r x) (Icc 0 α) t := by
  have hB1 : B < 1 := hBα.trans_le (Real.sin_le_one α)
  have hβ0 : 0 ≤ Real.arcsin B := Real.arcsin_nonneg.mpr hB0
  have hβα : Real.arcsin B < α := by
    have h := Real.arcsin_lt_arcsin (by linarith : -1 ≤ B) hBα (Real.sin_le_one α)
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) hαL.le] at h
  have hc : ContinuousOn (fun r => secondWall U r x) (Icc 0 α) := by
    intro r hr
    apply (hU.secondWall_continuousAt_angle
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1, Real.pi_pos], hr.2.trans_lt hαL⟩).ne' x).continuousWithinAt
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hα0.le⟩ hc
  refine ⟨t, ⟨ht.1, ?_⟩, hmax⟩
  by_contra hlate
  have hβt : Real.arcsin B < t := lt_of_not_ge hlate
  have hstrict := hU.secondWall_lt_of_late_angle hβ0 hβt (ht.2.trans_lt hαL)
    (show x - horizontalLeft U ≤ Real.sin (Real.arcsin B) by
      rwa [Real.sin_arcsin (by linarith) hB1.le])
  exact (not_lt_of_ge (hmax ⟨hβ0, hβα.le⟩)) hstrict

/-- MP.13 for the literal actual support point. Stationarity is proved
for a fixed attaining point, so no differentiability of the cap support
is required, even at the localization endpoint. -/
theorem IsDownwardCap.exists_positive_localized_secondWall_max {U : Set Plane}
    (hU : IsDownwardCap U) {α B x : ℝ}
    (hα0 : 0 < α) (hαL : α < Real.pi / 2)
    (hB0 : 0 ≤ B) (hBα : B < Real.sin α)
    (hx : x - horizontalLeft U ≤ B)
    (hpositive : ∃ r ∈ Icc 0 α, 0 < secondWall U r x) :
    ∃ t ∈ Ioo 0 α, t ≤ Real.arcsin B ∧ 0 < secondWall U t x ∧
      IsMaxOn (fun r => secondWall U r x) (Icc 0 α) t ∧
      (MovingSofaOptimality.vplus U (t + Real.pi / 2)).1 + Real.sin t = x ∧
      secondWall U t x = (MovingSofaOptimality.vplus U (t + Real.pi / 2)).2 - Real.cos t := by
  obtain ⟨t, ht, hmax⟩ := hU.exists_localized_secondWall_max hα0 hαL hB0 hBα hx
  obtain ⟨r, hr, hpos⟩ := hpositive
  have htpos : 0 < secondWall U t x := hpos.trans_le (hmax hr)
  have ht0 : 0 < t := by
    by_contra hbad
    have htzero : t = 0 := le_antisymm (le_of_not_gt hbad) ht.1
    rw [htzero] at htpos
    exact (not_lt_of_ge (hU.secondWall_zero_nonpos x)) htpos
  have hβα : Real.arcsin B < α := by
    have h := Real.arcsin_lt_arcsin (by linarith : -1 ≤ B) hBα (Real.sin_le_one α)
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) hαL.le] at h
  have htα : t < α := ht.2.trans_lt hβα
  have hcos (r : ℝ) (hr : r ∈ Icc 0 α) : 0 < Real.cos r :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1, Real.pi_pos], hr.2.trans_lt hαL⟩
  let p := MovingSofaOptimality.vplus U (t + Real.pi / 2)
  have hp : p ∈ U := (MovingSofaOptimality.vplus_mem_edge hU.imported_isConvexBody _).1
  have hpSupport : coordDot p (companionNormal t) = support U (companionNormal t) := by
    rw [companionNormal_eq_unitNormal]
    exact MovingSofaOptimality.dot_vplus_uvec U (t + Real.pi / 2)
  have hpeq := companionPointWall_eq_secondWall_of_support (x := x)
    (hcos t ⟨ht0.le, htα.le⟩).ne' hpSupport
  have hpmax : IsMaxOn (companionPointWall p x) (Icc 0 α) t := by
    intro r hr
    exact ((companionPointWall_le_secondWall hU hp (hcos r hr)).trans (hmax hr)).trans_eq hpeq.symm
  have hstation := (hpmax.isLocalMax (Icc_mem_nhds ht0 htα)).hasDerivAt_eq_zero
    (hasDerivAt_companionPointWall (hcos t ⟨ht0.le, htα.le⟩).ne')
  have hnumerator := (div_eq_iff (pow_ne_zero 2 (hcos t ⟨ht0.le, htα.le⟩).ne')).mp hstation
  simp only [zero_mul] at hnumerator
  have hpx : p.1 + Real.sin t = x := by linarith
  have hpy : secondWall U t x = p.2 - Real.cos t := by
    rw [← hpeq, companionPointWall, show x - p.1 = Real.sin t by linarith]
    field_simp [(hcos t ⟨ht0.le, htα.le⟩).ne']
    nlinarith only [Real.sin_sq_add_cos_sq t]
  exact ⟨t, ⟨ht0, htα⟩, ht.2, htpos, hmax, hpx, hpy⟩

end AmbidextrousSofa
