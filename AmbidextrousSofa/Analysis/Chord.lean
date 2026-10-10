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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hU.nonempty
    exact ⟨(p.1, 0), hU.baseline_mem hp, hnonneg p.1 ⟨p, hp, rfl⟩⟩
  · exact hU.isCompact.inter_right (isClosed_le continuous_snd
      (hcontinuous.comp continuous_fst))
  · intro p hp q hq a b ha hb hab
    refine ⟨hU.convex hp.1 hq.1 ha hb hab, ?_⟩
    change a * p.2 + b * q.2 ≤ ceiling (a * p.1 + b * q.1)
    calc
      a * p.2 + b * q.2 ≤ a * ceiling p.1 + b * ceiling q.1 :=
        add_le_add (mul_le_mul_of_nonneg_left hp.2 ha)
          (mul_le_mul_of_nonneg_left hq.2 hb)
      _ ≤ ceiling (a * p.1 + b * q.1) := by
        simpa only [smul_eq_mul] using hconcave.2
          (show p.1 ∈ horizontalProjection U from ⟨p, hp.1, rfl⟩)
          (show q.1 ∈ horizontalProjection U from ⟨q, hq.1, rfl⟩) ha hb hab
  · exact fun p hp => hU.inStrip hp.1
  · intro p hp y hy0 hyp
    exact ⟨hU.downward p hp.1 y hy0 hyp, hyp.trans hp.2⟩

theorem IsDownwardCap.horizontalProjection_capCut {U : Set Plane}
    (hU : IsDownwardCap U) {ceiling : ℝ → ℝ}
    (hnonneg : ∀ x ∈ horizontalProjection U, 0 ≤ ceiling x) :
    horizontalProjection (capCut U ceiling) = horizontalProjection U := by
  apply Set.Subset.antisymm (Set.image_mono (capCut_subset U ceiling))
  rintro x ⟨p, hp, hpx⟩
  exact ⟨(p.1, 0), ⟨hU.baseline_mem hp, hnonneg p.1 ⟨p, hp, rfl⟩⟩, hpx⟩

theorem IsDownwardCap.capRoof_capCut {U : Set Plane} (hU : IsDownwardCap U)
    {ceiling : ℝ → ℝ} (hcontinuous : Continuous ceiling)
    (hconcave : ConcaveOn ℝ (horizontalProjection U) ceiling)
    (hnonneg : ∀ x ∈ horizontalProjection U, 0 ≤ ceiling x)
    {x : ℝ} (hx : x ∈ horizontalProjection U) :
    capRoof (capCut U ceiling) x = min (capRoof U x) (ceiling x) := by
  have hV := hU.isDownwardCap_capCut hcontinuous hconcave hnonneg
  have hxV : x ∈ horizontalProjection (capCut U ceiling) := by
    rw [hU.horizontalProjection_capCut hnonneg]
    exact hx
  apply le_antisymm
  · have htop := capRoof_mem hV.isCompact hxV
    exact le_min (le_capRoof hU.isCompact htop.1) htop.2
  · apply le_capRoof hV.isCompact
    refine ⟨hU.downward (x, capRoof U x) (capRoof_mem hU.isCompact hx)
      (min (capRoof U x) (ceiling x)) ?_ (min_le_left _ _), ?_⟩
    swap
    · change min (capRoof U x) (ceiling x) ≤ ceiling x
      exact min_le_right _ _
    exact le_min (capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1) x)
      (hnonneg x hx)

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
  have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  simp only [roofChord, div_mul_cancel₀ _ hba]
  ring

theorem roofChord_eq_interpolation (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (x : ℝ) :
    roofChord f a b x = (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := by
  unfold roofChord
  field_simp [ne_of_gt (sub_pos.mpr hab)] <;> ring

theorem concaveOn_roofChord (f : ℝ → ℝ) (a b : ℝ) :
    ConcaveOn ℝ univ (roofChord f a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ u v _ _ huv
  change u * roofChord f a b x + v * roofChord f a b y ≤
    roofChord f a b (u * x + v * y)
  apply le_of_eq
  unfold roofChord
  calc
    u * (f a + (f b - f a) / (b - a) * (x - a)) +
        v * (f a + (f b - f a) / (b - a) * (y - a)) =
      (u + v) * f a + (f b - f a) / (b - a) *
        (u * x + v * y - (u + v) * a) := by ring
    _ = f a + (f b - f a) / (b - a) * (u * x + v * y - a) := by rw [huv]; ring

theorem ConcaveOn.roofChord_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a < b) (hx : x ∈ Icc a b) : roofChord f a b x ≤ f x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [hba.ne'] <;> ring
  have hpoint : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp [hba.ne'] <;> ring
  have h := hf.2 ha hb (div_nonneg (sub_nonneg.mpr hx.2) hba.le)
    (div_nonneg (sub_nonneg.mpr hx.1) hba.le) hsum
  rw [roofChord_eq_interpolation f hab]
  simpa only [smul_eq_mul, hpoint] using h

/-- Outside a chord interval, concavity puts the original graph below the
extended chord. These are exterior bounds, not the interior chord inequality. -/
theorem ConcaveOn.le_roofChord_of_le {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (hx : x ∈ s) (hb : b ∈ s)
    (hab : a < b) (hxa : x ≤ a) : f x ≤ roofChord f a b x := by
  rcases eq_or_lt_of_le hxa with rfl | hxa
  · rw [roofChord_left]
  · have h := hf.slope_anti_adjacent hx hb hxa hab
    have hmul := (le_div_iff₀ (sub_pos.mpr hxa)).mp h
    unfold roofChord
    nlinarith

theorem ConcaveOn.le_roofChord_of_ge {s : Set ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ s f) {a b x : ℝ} (ha : a ∈ s) (hx : x ∈ s)
    (hab : a < b) (hbx : b ≤ x) : f x ≤ roofChord f a b x := by
  rcases eq_or_lt_of_le hbx with rfl | hbx
  · rw [roofChord_right f hab]
  · have h := hf.slope_anti_adjacent ha hx hab hbx
    have hmul := (div_le_iff₀ (sub_pos.mpr hbx)).mp h
    calc
      f x ≤ roofChord f a b b + (f b - f a) / (b - a) * (x - b) := by
        rw [roofChord_right f hab]
        linarith
      _ = roofChord f a b x := by
        unfold roofChord
        ring

theorem roofChord_nonneg_of_mem_Icc {f : ℝ → ℝ} {a b x : ℝ}
    (hab : a < b) (ha : 0 ≤ f a) (hb : 0 ≤ f b) (hx : x ∈ Icc a b) :
    0 ≤ roofChord f a b x := by
  rw [roofChord_eq_interpolation f hab]
  exact add_nonneg
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hx.2) (sub_pos.mpr hab).le) ha)
    (mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hab).le) hb)

theorem IsDownwardCap.roofChord_nonneg {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) : ∀ x ∈ horizontalProjection U, 0 ≤ roofChord (capRoof U) a b x := by
  intro x hx
  have hroof0 := capRoof_nonneg hU.isCompact (fun p hp => (hU.inStrip hp).1)
  rcases le_total x a with hxa | hax
  · exact (hroof0 x).trans (ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof hx hb hab hxa)
  · rcases le_total b x with hbx | hxb
    · exact (hroof0 x).trans (ConcaveOn.le_roofChord_of_ge hU.concaveOn_capRoof ha hx hab hbx)
    · exact roofChord_nonneg_of_mem_Icc hab (hroof0 a) (hroof0 b) ⟨hax, hxb⟩

/-- The actual cut to the line through two points on the cap roof. -/
def chordCap (U : Set Plane) (a b : ℝ) : Set Plane := capCut U (roofChord (capRoof U) a b)

theorem IsDownwardCap.isDownwardCap_chordCap {U : Set Plane} (hU : IsDownwardCap U)
    {a b : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) : IsDownwardCap (chordCap U a b) :=
  hU.isDownwardCap_capCut (continuous_roofChord _ _ _)
    ((concaveOn_roofChord _ _ _).subset (subset_univ _)
      (convex_horizontalProjection hU.convex)) (hU.roofChord_nonneg ha hb hab)

theorem IsDownwardCap.horizontalProjection_chordCap {U : Set Plane}
    (hU : IsDownwardCap U) {a b : ℝ} (ha : a ∈ horizontalProjection U)
    (hb : b ∈ horizontalProjection U) (hab : a < b) :
    horizontalProjection (chordCap U a b) = horizontalProjection U :=
  hU.horizontalProjection_capCut (hU.roofChord_nonneg ha hb hab)

theorem IsDownwardCap.capRoof_chordCap {U : Set Plane} (hU : IsDownwardCap U)
    {a b x : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hx : x ∈ horizontalProjection U) :
    capRoof (chordCap U a b) x = min (capRoof U x) (roofChord (capRoof U) a b x) :=
  hU.capRoof_capCut (continuous_roofChord _ _ _)
    ((concaveOn_roofChord _ _ _).subset (subset_univ _)
      (convex_horizontalProjection hU.convex)) (hU.roofChord_nonneg ha hb hab) hx

theorem IsDownwardCap.capRoof_chordCap_inside {U : Set Plane} (hU : IsDownwardCap U)
    {a b x : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hx : x ∈ Icc a b) :
    capRoof (chordCap U a b) x = roofChord (capRoof U) a b x := by
  have hxU : x ∈ horizontalProjection U :=
    (convex_horizontalProjection hU.convex).ordConnected.out ha hb hx
  rw [hU.capRoof_chordCap ha hb hab hxU]
  exact min_eq_right (ConcaveOn.roofChord_le hU.concaveOn_capRoof ha hb hab hx)

theorem IsDownwardCap.capRoof_chordCap_outside {U : Set Plane} (hU : IsDownwardCap U)
    {a b x : ℝ} (ha : a ∈ horizontalProjection U) (hb : b ∈ horizontalProjection U)
    (hab : a < b) (hx : x ∈ horizontalProjection U) (hout : x ∉ Icc a b) :
    capRoof (chordCap U a b) x = capRoof U x := by
  rw [hU.capRoof_chordCap ha hb hab hx]
  apply min_eq_left
  rcases lt_or_ge x a with hxa | hax
  · exact ConcaveOn.le_roofChord_of_le hU.concaveOn_capRoof hx hb hab hxa.le
  · have hbx : b < x := lt_of_not_ge (fun hxb => hout ⟨hax, hxb⟩)
    exact ConcaveOn.le_roofChord_of_ge hU.concaveOn_capRoof ha hx hab hbx.le

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
    IsDownwardCap (middleChordCap U) := by
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  exact hU.isDownwardCap_chordCap ha hb hab

theorem IsDownwardCap.horizontalProjection_middleChordCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) :
    horizontalProjection (middleChordCap U) = horizontalProjection U := by
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  exact hU.horizontalProjection_chordCap ha hb hab

/-- The charged exterior roof is unchanged while the actual interior and
terminal barriers can only decrease. -/
theorem IsDownwardCap.capScore_le_middleChordCap {U : Set Plane}
    (hU : IsDownwardCap U) (hwidth : 0 < capWidth U) {α : ℝ}
    (hα0 : 0 < α) (hα : α ≤ Real.pi / 2) : capScore U α ≤ capScore (middleChordCap U) α := by
  have hV := hU.isDownwardCap_middleChordCap hwidth
  have hprojection := hU.horizontalProjection_middleChordCap hwidth
  have hleft : horizontalLeft (middleChordCap U) = horizontalLeft U :=
    congrArg sInf hprojection
  have hright : horizontalRight (middleChordCap U) = horizontalRight U :=
    congrArg sSup hprojection
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  apply capScore_le_of_subset_of_exterior_roof_eq hV hU (capCut_subset _ _)
    hprojection ?_ hα0 hα
  intro x hx
  rw [hleft, hright] at hx
  apply hU.capRoof_chordCap_outside ha hb hab
  · rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact hx.1
  · exact hx.2

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
  let V := middleChordCap U
  let a := horizontalLeft U + capWidth U / 4
  let b := horizontalRight U - capWidth U / 4
  let m := (capRoof U b - capRoof U a) / (b - a)
  have hV : IsDownwardCap V := hU.isDownwardCap_middleChordCap hwidth
  have hproj : horizontalProjection V = horizontalProjection U :=
    hU.horizontalProjection_middleChordCap hwidth
  obtain ⟨ha, hb, hab⟩ := hU.middleChord_endpoints hwidth
  refine ⟨heightSaturation V, hV.isDownwardCap_heightSaturation,
    hV.horizontalProjection_heightSaturation.trans hproj,
    hV.capHeight_heightSaturation,
    (hU.capScore_le_middleChordCap hwidth hα0 hα).trans
      (hV.capScore_le_heightSaturation hα0 hα),
    m, capRoof U a - m * a + (1 - capHeight V), ?_⟩
  intro x hx
  have hxU : x ∈ horizontalProjection U := by
    rw [horizontalProjection_eq_Icc hU.nonempty hU.isCompact hU.convex]
    exact middleHalfInterval_subset
      (horizontalLeft_le_horizontalRight hU.nonempty hU.isCompact) hx
  have hxV : x ∈ horizontalProjection V := by rw [hproj]; exact hxU
  rw [heightSaturation,
    hV.capRoof_verticalExtrusion (sub_nonneg.mpr hV.capHeight_le_one) hxV]
  have hchord : capRoof V x = roofChord (capRoof U) a b x :=
    hU.capRoof_chordCap_inside ha hb hab hx
  rw [hchord]
  dsimp [roofChord, m]
  ring

end AmbidextrousSofa
