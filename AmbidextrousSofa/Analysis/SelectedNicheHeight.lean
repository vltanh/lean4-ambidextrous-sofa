import AmbidextrousSofa.Analysis.FiniteNicheOscillation
import AmbidextrousSofa.Analysis.EndpointPositivity

/-!
# The central niche-height bound for every canonical full maximum

The finite erosion sum controls the total variation of the physical
polygon niche. Concavity controls the two exterior roof variations even
when a selected polygon's highest point moves between the wings. The
actual axis-height limits and the vanishing erosion moments pass this
pointwise estimate to any prescribed full maximizer. Endpoint stationarity
then gives the central bound by half the sum of the two axis heights.

This argument does not require an identification of weak occupation
measures, a smooth roof, a unique active wall, or a prescribed floor set.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace AmbidextrousSofa

theorem IsFullCapMaximizer.middle_roof_sum_eq_two_sub_abs_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) +
      capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) =
      2 - |capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)| := by
  obtain ⟨m, c, haffine⟩ := haffine
  by_cases hm : 0 ≤ m
  · have htop := hU.middle_right_eq_one_of_affine_nonneg hheight hm haffine
    rw [htop, abs_of_nonneg (sub_nonneg.mpr
      (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _))]
    ring
  · have htop := hU.middle_left_eq_one_of_affine_nonpos hheight (le_of_not_ge hm) haffine
    rw [htop, abs_of_nonpos (sub_nonpos.mpr
      (capRoof_le_one hU.isCap.isCompact hU.isCap.inStrip _))]
    ring

namespace AngularGrid

open FinitePolygon

theorem selected_niche_oscillation_le
    {target : Set Plane} {U : ℕ → Set Plane} {a b : ℝ}
    {level : ℕ → ℕ} {coefficient : ℕ → ℝ}
    (hTarget : IsFullCapMaximizer target) (hheight : capHeight target = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval
      (horizontalLeft target) (horizontalRight target), capRoof target x = m * x + c)
    (hTargetBox : target ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1)
    (hU : ∀ n, IsSelectedPolygon target a b (level n) (coefficient n) (U n))
    (hHausdorff : CapHausdorffTendsto U target) (hlevel : Tendsto level atTop atTop)
    (hc : ∀ n, 0 ≤ coefficient n) (hrate : Tendsto coefficient atTop (𝓝 0))
    (hleft : a < horizontalLeft target) (hright : horizontalRight target < b)
    {x : ℝ} (hx : x ∈ middleHalfInterval (horizontalLeft target) (horizontalRight target)) :
    2 * sweptNiche target (Real.pi / 2) x -
      sweptNiche target (Real.pi / 2)
        (horizontalLeft target + (horizontalRight target - horizontalLeft target) / 4) -
      sweptNiche target (Real.pi / 2)
        (horizontalRight target - (horizontalRight target - horizontalLeft target) / 4) ≤
      2 - |capRoof target (horizontalRight target -
          (horizontalRight target - horizontalLeft target) / 4) -
        capRoof target (horizontalLeft target +
          (horizontalRight target - horizontalLeft target) / 4)| -
        capRoof target (horizontalLeft target) - capRoof target (horizontalRight target) := by
  let l := horizontalLeft target
  let r := horizontalRight target
  let u := l + (r - l) / 4
  let v := r - (r - l) / 4
  let un : ℕ → ℝ := fun n => horizontalLeft (U n) +
    (horizontalRight (U n) - horizontalLeft (U n)) / 4
  let vn : ℕ → ℝ := fun n => horizontalRight (U n) -
    (horizontalRight (U n) - horizontalLeft (U n)) / 4
  have hcap : ∀ n, IsDownwardCap (U n) := fun n => (hU n).isCap
  have hwidth : 1 < capWidth target := one_lt_M.trans_le hTarget.width_bounds.1
  have hlr : l < r := by change 1 < r - l at hwidth; linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hx' : x ∈ Icc u v := hx
  let w : ℝ := (x - u) / (v - u)
  have hw0 : 0 ≤ w := div_nonneg (sub_nonneg.mpr hx'.1) (sub_pos.mpr huv).le
  have hw1 : w ≤ 1 := by
    dsimp [w]
    rw [div_le_iff₀ (sub_pos.mpr huv)]
    linarith [hx'.2]
  have hxid : u + w * (v - u) = x := by
    dsimp [w]
    field_simp [(sub_pos.mpr huv).ne']
    ring
  let t : ℕ → ℝ := fun n => un n + w * (vn n - un n)
  have huvN (n : ℕ) : un n ≤ vn n := by
    have h := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp [un, vn]
    linarith
  have htJ (n : ℕ) : t n ∈ middleHalfInterval (horizontalLeft (U n)) (horizontalRight (U n)) := by
    change un n ≤ t n ∧ t n ≤ vn n
    have hprod0 := mul_nonneg hw0 (sub_nonneg.mpr (huvN n))
    have hprod1 := mul_nonneg (sub_nonneg.mpr hw1) (sub_nonneg.mpr (huvN n))
    dsimp [t]
    constructor <;> nlinarith
  have hbox : ∀ n, U n ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := fun n => (hU n).inBox
  have hunB : ∀ n, un n ∈ Icc a b := by
    intro n
    apply (hcap n).projection_subset_Icc_of_box (hbox n)
    have h := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp [un]
    exact ⟨by linarith, by linarith⟩
  have hvnB : ∀ n, vn n ∈ Icc a b := by
    intro n
    apply (hcap n).projection_subset_Icc_of_box (hbox n)
    have h := horizontalLeft_le_horizontalRight (hcap n).nonempty (hcap n).isCompact
    dsimp [vn]
    exact ⟨by linarith, by linarith⟩
  have htB : ∀ n, t n ∈ Icc a b := by
    intro n
    have ht := htJ n
    change un n ≤ t n ∧ t n ≤ vn n at ht
    exact ⟨(hunB n).1.trans ht.1, ht.2.trans (hvnB n).2⟩
  have hln := hHausdorff.horizontalLeft_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hrn := hHausdorff.horizontalRight_tendsto (fun n => (hcap n).isCompact)
    (fun n => (hcap n).nonempty) hTarget.isCap.isCompact hTarget.isCap.nonempty
  have hun : Tendsto un atTop (𝓝 u) := hln.add ((hrn.sub hln).div_const 4)
  have hvn : Tendsto vn atTop (𝓝 v) := hrn.sub ((hrn.sub hln).div_const 4)
  have ht : Tendsto t atTop (𝓝 x) := by
    simpa only [hxid] using hun.add ((hvn.sub hun).const_mul w)
  have hN := finiteBarrier_dyadic_tendsto hHausdorff hcap hTarget.isCap hlevel hbox htB ht
  have hNu := finiteBarrier_dyadic_tendsto hHausdorff hcap hTarget.isCap hlevel hbox hunB hun
  have hNv := finiteBarrier_dyadic_tendsto hHausdorff hcap hTarget.isCap hlevel hbox hvnB hvn
  have hAu := hHausdorff.middleLeft_roof_tendsto hcap hTarget.isCap hlr
  have hAv := hHausdorff.middleRight_roof_tendsto hcap hTarget.isCap hlr
  have heL := selected_left_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hwidth hleft
  have heR := selected_right_height_tendsto_actual hTarget.isCap hTargetBox hU hHausdorff
    hlevel hc hrate hwidth hright
  have hD := erosionMoments_tendsto_zero_of_canonical_maximum hTarget hheight haffine
    hTargetBox hU hHausdorff hlevel hc hrate hleft hright
  have hW : ∀ᶠ n in atTop, 0 < capWidth (U n) :=
    (hHausdorff.capWidth_tendsto hcap hTarget.isCap).eventually
      (Ioi_mem_nhds (by linarith : 0 < capWidth target))
  have hfinite : ∀ᶠ n in atTop,
      2 * finiteBarrier (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none (t n) -
        finiteBarrier (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none (un n) -
        finiteBarrier (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none (vn n) ≤
        2 - |capRoof (U n) (vn n) - capRoof (U n) (un n)| -
          capRoof (U n) (horizontalLeft (U n)) - capRoof (U n) (horizontalRight (U n)) +
          finiteRightMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none +
          finiteLeftMoment (U n) (normal (dyadic (level n))) (pairList (dyadic (level n))) none := by
    filter_upwards [hW] with n hn
    exact finiteBarrier_peak_le_end_heights_and_moments (hcap n) (normal (dyadic (level n)))
      (normal_snd_pos (dyadic (level n))) (wallSlopes_injective (dyadic (level n)))
      (hU n).polygon_eq (pairList (dyadic (level n))) none hn (htJ n)
  have hbound := le_of_tendsto_of_tendsto (((hN.const_mul 2).sub hNu).sub hNv)
    (((((tendsto_const_nhds.sub (hAv.sub hAu).abs).sub heL).sub heR).add hD.1).add hD.2)
    hfinite
  simpa only [add_zero] using hbound

end AngularGrid

/-- The central height estimate is a consequence of actual maximality.
The selected approximations and their vanishing moments are constructed
inside the proof; none is an additional assumption of this theorem. -/
theorem IsFullCapMaximizer.sweptNiche_le_half_endpoint_height_sum_of_affine
    {U : Set Plane} (hU : IsFullCapMaximizer U) (hheight : capHeight U = 1)
    (haffine : ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      capRoof U x = m * x + c) :
    ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
      sweptNiche U (Real.pi / 2) x ≤
        (capRoof U (horizontalRight U) + capRoof U (horizontalLeft U)) / 2 := by
  let a := horizontalLeft U - 1
  let b := horizontalRight U + 1
  have hlr := horizontalLeft_le_horizontalRight hU.isCap.nonempty hU.isCap.isCompact
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hbox : U ⊆ Icc a b ×ˢ Icc (0 : ℝ) 1 := by
    intro p hp
    have hx : p.1 ∈ Icc (horizontalLeft U) (horizontalRight U) := by
      rw [← horizontalProjection_eq_Icc hU.isCap.nonempty hU.isCap.isCompact hU.isCap.convex]
      exact ⟨p, hp, rfl⟩
    refine ⟨⟨?_, ?_⟩, hU.isCap.inStrip hp⟩
    · dsimp [a]
      linarith [hx.1]
    · dsimp [b]
      linarith [hx.2]
  obtain ⟨level, coefficient, V, hlevel, hc, hrate, hV, _, hHausdorff⟩ :=
    AngularGrid.exists_selected_sequence hU hab hbox
  have hlevelTop : Tendsto level atTop atTop := tendsto_atTop_mono hlevel tendsto_id
  have hleft : a < horizontalLeft U := by dsimp [a]; linarith
  have hright : horizontalRight U < b := by dsimp [b]; linarith
  have hsum := hU.middle_roof_sum_eq_two_sub_abs_of_affine hheight haffine
  have hEP := hU.endpoint_height_sum_of_affine hheight haffine
  intro x hx
  have hosc := AngularGrid.selected_niche_oscillation_le hU hheight haffine hbox hV hHausdorff
    hlevelTop (fun n => (hc n).le) hrate hleft hright hx
  linarith

end AmbidextrousSofa
