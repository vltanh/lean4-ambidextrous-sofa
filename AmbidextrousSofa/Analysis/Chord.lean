module

public import AmbidextrousSofa.Analysis.Extrusion

@[expose] public section

/-!
# Canonicalizing the uncharged middle roof

Intersecting a cap with the hypograph of a continuous concave ceiling is
an actual convex cap cut whenever the ceiling is nonnegative on its
projection. The chord through the middle-window endpoints lies below the
old roof inside that window and above it outside. Cutting to this chord
therefore preserves every charged exterior roof value and decreases the
actual barrier. Height saturation restores height one without lowering
the scalar score or destroying affinity of the middle roof.
-/

noncomputable section

open Set MeasureTheory

namespace AmbidextrousSofa

/-- An actual intersection with a ceiling, retaining the old horizontal domain. -/
def capCut (U : Set Plane) (ceiling : ℝ → ℝ) : Set Plane :=
  U ∩ {p | p.2 ≤ ceiling p.1}

theorem capCut_subset (U : Set Plane) (ceiling : ℝ → ℝ) : capCut U ceiling ⊆ U :=
  inter_subset_left

theorem IsDownwardCap.isDownwardCap_capCut {U : Set Plane} (hU : IsDownwardCap U)
    {ceiling : ℝ → ℝ} (hcontinuous : Continuous ceiling)
    (hconcave : ConcaveOn ℝ (horizontalProjection U) ceiling)
    (hnonneg : ∀ x ∈ horizontalProjection U, 0 ≤ ceiling x) :
    IsDownwardCap (capCut U ceiling) := by
  obtain ⟨p, hp⟩ := hU.nonempty
  refine ⟨⟨(p.1, 0), hU.baseline_mem hp, hnonneg p.1 ⟨p, hp, rfl⟩⟩,
    hU.isCompact.inter_right (isClosed_le continuous_snd (hcontinuous.comp continuous_fst)),
    fun p hp q hq a b ha hb hab => ⟨hU.convex hp.1 hq.1 ha hb hab, ?_⟩,
    fun p hp => hU.inStrip hp.1,
    fun p hp y hy0 hyp => ⟨hU.downward p hp.1 y hy0 hyp, hyp.trans hp.2⟩⟩
  change a * p.2 + b * q.2 ≤ ceiling (a * p.1 + b * q.1)
  exact (add_le_add (mul_le_mul_of_nonneg_left hp.2 ha) (mul_le_mul_of_nonneg_left hq.2 hb)).trans
    (hconcave.2 ⟨p, hp.1, rfl⟩ ⟨q, hq.1, rfl⟩ ha hb hab)

theorem IsDownwardCap.horizontalProjection_capCut {U : Set Plane}
    (hU : IsDownwardCap U) {ceiling : ℝ → ℝ}
    (hnonneg : ∀ x ∈ horizontalProjection U, 0 ≤ ceiling x) :
    horizontalProjection (capCut U ceiling) = horizontalProjection U :=
  (image_mono (capCut_subset U ceiling)).antisymm fun _ ⟨p, hp, hpx⟩ =>
    ⟨(p.1, 0), ⟨hU.baseline_mem hp, hnonneg p.1 ⟨p, hp, rfl⟩⟩, hpx⟩

/-- The line through two roof values, defined on all real abscissae. -/
def roofChord (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  f a + ((f b - f a) / (b - a)) * (x - a)

theorem continuous_roofChord (f : ℝ → ℝ) (a b : ℝ) :
    Continuous (roofChord f a b) := by
  unfold roofChord
  fun_prop

theorem roofChord_left (f : ℝ → ℝ) (a b : ℝ) : roofChord f a b a = f a := by
  simp [roofChord]

theorem roofChord_right (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) :
    roofChord f a b b = f b := by
  rw [roofChord, div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
  ring

theorem roofChord_eq_interpolation (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (x : ℝ) :
    roofChord f a b x = (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := by
  rw [roofChord]
  field_simp [(sub_pos.mpr hab).ne']
  ring

theorem concaveOn_roofChord (f : ℝ → ℝ) (a b : ℝ) {s : Set ℝ} (hs : Convex ℝ s) :
    ConcaveOn ℝ s (roofChord f a b) :=
  ⟨hs, fun x _ y _ u v _ _ huv => le_of_eq <| by
    simp only [roofChord, smul_eq_mul]
    linear_combination (f a - (f b - f a) / (b - a) * a) * huv⟩

theorem ConcaveOn.roofChord_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (hx : x ∈ Icc a b) : roofChord f a b x ≤ f x := by
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hpoint : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp
    ring
  rw [roofChord_eq_interpolation f hab]
  simpa only [smul_eq_mul, hpoint] using hf.2 ha hb
    (div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hab).le)
    (div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le) (by field_simp; ring)

/-- Outside a chord interval, concavity puts the original graph below the
extended chord. These are exterior bounds, not the interior chord inequality. -/
theorem ConcaveOn.le_roofChord_of_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (hx : x ∈ s) (hb : b ∈ s)
    (hab : a < b) (hxa : x ≤ a) : f x ≤ roofChord f a b x := by
  rcases hxa.eq_or_lt with rfl | hxa
  · rw [roofChord_left]
  · have := (le_div_iff₀ (sub_pos.mpr hxa)).mp (hf.slope_anti_adjacent hx hb hxa hab)
    rw [roofChord]
    linarith

theorem ConcaveOn.le_roofChord_of_ge {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (ha : a ∈ s) (hx : x ∈ s)
    (hab : a < b) (hbx : b ≤ x) : f x ≤ roofChord f a b x := by
  rcases hbx.eq_or_lt with rfl | hbx
  · rw [roofChord_right f hab]
  · have := (div_le_iff₀ (sub_pos.mpr hbx)).mp (hf.slope_anti_adjacent ha hx hab hbx)
    have := div_mul_cancel₀ (f b - f a) (sub_pos.mpr hab).ne'
    rw [roofChord]
    linarith

theorem IsDownwardCap.roofChord_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) : ∀ x ∈ horizontalProjection U, 0 ≤ roofChord (capRoof U) a b x := by
  intro x hx
  have h0 := capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1)
  rcases le_total x a with hxa | hax
  · exact (h0 x).trans (ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof hx hb hab hxa)
  rcases le_total b x with hbx | hxb
  · exact (h0 x).trans (ConcaveOn.le_roofChord_of_ge hU.concaveOn_capRoof ha hx hab hbx)
  rw [roofChord_eq_interpolation _ hab]
  exact add_nonneg (mul_nonneg (div_nonneg (sub_nonneg.mpr hxb) (sub_pos.mpr hab).le) (h0 a))
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hax) (sub_pos.mpr hab).le) (h0 b))

/-- The actual cut to the line through two points on the cap roof. -/
def chordCap (U : Set Plane) (a b : ℝ) : Set Plane := capCut U (roofChord (capRoof U) a b)

theorem IsDownwardCap.capRoof_chordCap {U : Set Plane} (hU : IsDownwardCap U)
    {a b x : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hx : x ∈ horizontalProjection U) :
    capRoof (chordCap U a b) x = min (capRoof U x) (roofChord (capRoof U) a b x) := by
  have hnonneg := hU.roofChord_nonneg ha hb hab
  have hV := hU.isDownwardCap_capCut (continuous_roofChord _ _ _)
    (concaveOn_roofChord _ _ _ (convex_horizontalProjection hU.convex)) hnonneg
  have htop := capRoof_mem hV.isCompact ((hU.horizontalProjection_capCut hnonneg).symm ▸ hx)
  exact le_antisymm (le_min (le_capRoof hU.isCompact htop.1) htop.2) (le_capRoof hV.isCompact
    ⟨hU.downward _ (capRoof_mem hU.isCompact hx) _ (le_min (capRoof_nonneg hU.isCompact
      (fun p hp => (hU.inStrip hp).1) x) (hnonneg x hx)) (min_le_left _ _), min_le_right
      (capRoof U x) (roofChord (capRoof U) a b x)⟩)

theorem IsDownwardCap.capRoof_chordCap_inside {U : Set Plane} (hU : IsDownwardCap U)
    {a b x : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hx : x ∈ Icc a b) :
    capRoof (chordCap U a b) x = roofChord (capRoof U) a b x := by
  rw [hU.capRoof_chordCap ha hb hab
    ((convex_horizontalProjection hU.convex).ordConnected.out ha hb hx)]
  exact min_eq_right (ConcaveOn.roofChord_le hU.concaveOn_capRoof ha hb hab hx)

theorem IsDownwardCap.capRoof_chordCap_outside {U : Set Plane} (hU : IsDownwardCap U)
    {a b x : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hx : x ∈ horizontalProjection U) (hout : x ∉ Icc a b) :
    capRoof (chordCap U a b) x = capRoof U x := by
  rw [hU.capRoof_chordCap ha hb hab hx]
  refine min_eq_left ?_
  rcases lt_or_ge x a with hxa | hax
  · exact ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof hx hb hab hxa.le
  · exact ConcaveOn.le_roofChord_of_ge hU.concaveOn_capRoof ha hx hab
      (not_le.mp fun h => hout ⟨hax, h⟩).le

/-- The middle chord uses the endpoints of the moving middle-half window. -/
def middleChordCap (U : Set Plane) : Set Plane :=
  chordCap U (horizontalLeft U + capWidth U / 4) (horizontalRight U - capWidth U / 4)

theorem IsDownwardCap.middleChord_endpoints {U : Set Plane} (hU : IsDownwardCap U)
    (hwidth : 0 < capWidth U) :
    horizontalLeft U + capWidth U / 4 ∈ horizontalProjection U ∧
      horizontalRight U - capWidth U / 4 ∈ horizontalProjection U ∧
      horizontalLeft U + capWidth U / 4 < horizontalRight U - capWidth U / 4 := by
  rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
  unfold capWidth at *
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, by linarith⟩

theorem IsDownwardCap.isDownwardCap_middleChordCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) :
    IsDownwardCap (middleChordCap U) :=
  let ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  hU.isDownwardCap_capCut (continuous_roofChord _ _ _)
    (concaveOn_roofChord _ _ _ (convex_horizontalProjection hU.convex))
    (hU.roofChord_nonneg ha hb hab)

theorem IsDownwardCap.horizontalProjection_middleChordCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) :
    horizontalProjection (middleChordCap U) = horizontalProjection U :=
  let ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  hU.horizontalProjection_capCut (hU.roofChord_nonneg ha hb hab)

/-- The charged exterior roof is unchanged while the actual interior and
terminal barriers can only decrease. -/
theorem IsDownwardCap.capScore_le_middleChordCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) : capScore U α ≤ capScore (middleChordCap U) α := by
  have hprojection := hU.horizontalProjection_middleChordCap hwidth
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  refine capScore_le_of_subset_of_exterior_roof_eq (hU.isDownwardCap_middleChordCap hwidth) hU
    (capCut_subset _ _) hprojection (fun x hx => ?_) hα0 hα
  rw [horizontalLeft, horizontalRight, hprojection] at hx
  exact hU.capRoof_chordCap_outside ha hb hab
    ((horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex).symm ▸ hx.1) hx.2

/-- Every positive-width cap has a height-one cap with the same projection,
an affine middle roof, and at least its scalar score. This is a concrete
canonicalization, without any maximizer or sharpness hypothesis. -/
theorem IsDownwardCap.exists_heightOne_affine_middle {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) :
    ∃ V : Set Plane, IsDownwardCap V ∧ horizontalProjection V = horizontalProjection U ∧
      capHeight V = 1 ∧ capScore U α ≤ capScore V α ∧
      ∃ m c : ℝ, ∀ x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U),
        capRoof V x = m * x + c := by
  have hV := hU.isDownwardCap_middleChordCap hwidth
  have hproj := hU.horizontalProjection_middleChordCap hwidth
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  set a := horizontalLeft U + capWidth U / 4
  set b := horizontalRight U - capWidth U / 4
  set m := (capRoof U b - capRoof U a) / (b - a)
  refine ⟨_, hV.isDownwardCap_heightSaturation,
    hV.horizontalProjection_heightSaturation.trans hproj, hV.capHeight_heightSaturation,
    (hU.capScore_le_middleChordCap hwidth hα0 hα).trans (hV.capScore_le_heightSaturation hα0 hα),
    m, capRoof U a - m * a + (1 - capHeight (middleChordCap U)), fun x hx => ?_⟩
  have hxU : x ∈ horizontalProjection U :=
    (horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex).symm ▸
      middleHalfInterval_subset (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact) hx
  rw [heightSaturation, hV.capRoof_verticalExtrusion (sub_nonneg.mpr hV.capHeight_le_one)
    (hproj.symm ▸ hxU), show capRoof (middleChordCap U) x = _ from
      hU.capRoof_chordCap_inside ha hb hab hx, roofChord]
  ring

end AmbidextrousSofa
