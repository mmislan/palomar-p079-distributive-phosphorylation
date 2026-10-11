module
public import proofs.PhosphorylationStableCapacity.ScalarCrossingRightmost

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

private def endpointCharge (y : ℝ) : ℤ := if 0 < y then 1 else 0
def crossingCharge (f : ℝ → ℝ) (r : ℝ) : ℤ :=
  if 0 < deriv f r then 1 else -1

private theorem same_endpoint_sign_of_no_root
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : f a ≠ 0) (hb : f b ≠ 0)
    (hno : ∀ r, a < r → r < b → f r ≠ 0) :
    (0 < f a) ↔ (0 < f b) := by
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · rcases lt_or_gt_of_ne hb with hbNeg | hbPos
    · exact ⟨fun h => (not_lt_of_ge haNeg.le h).elim,
        fun h => (not_lt_of_ge hbNeg.le h).elim⟩
    · obtain ⟨r, har, hrb, hroot⟩ :=
        scalar_root_between_neg_pos f a b hab.le hcont haNeg hbPos
      exact (hno r har hrb hroot).elim
  · rcases lt_or_gt_of_ne hb with hbNeg | hbPos
    · obtain ⟨r, har, hrb, hroot⟩ :=
        scalar_root_between_pos_neg f a b hab.le hcont haPos hbNeg
      exact (hno r har hrb hroot).elim
    · exact ⟨fun _ => hbPos, fun _ => haPos⟩

/-- A finite family of simple real zeros has signed crossing count
equal to the change in endpoint sign. This is the one-dimensional
degree calculation needed by the scalar capacity route. -/
theorem finite_simple_roots_signed_crossing_count
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : f a ≠ 0) (hb : f b ≠ 0)
    (hfinite : {r : ℝ | a < r ∧ r < b ∧ f r = 0}.Finite)
    (hsimple : ∀ r, a < r → r < b → f r = 0 →
      deriv f r ≠ 0) :
    ∑ r ∈ hfinite.toFinset, crossingCharge f r =
      endpointCharge (f b) - endpointCharge (f a) := by
  classical
  have main : ∀ m : ℕ, ∀ (a b : ℝ) (S : Finset ℝ),
      S.card = m → a < b → ContinuousOn f (Set.Icc a b) →
      f a ≠ 0 → f b ≠ 0 →
      (∀ r, r ∈ S ↔ a < r ∧ r < b ∧ f r = 0) →
      (∀ r ∈ S, deriv f r ≠ 0) →
      ∑ r ∈ S, crossingCharge f r =
        endpointCharge (f b) - endpointCharge (f a) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a b S hcard hab hcont ha hb hcover hsimple
      by_cases hSne : S.Nonempty
      · have hfinite' : {r : ℝ | a < r ∧ r < b ∧ f r = 0}.Finite := by
          have heq : {r : ℝ | a < r ∧ r < b ∧ f r = 0} =
              (S : Set ℝ) := by
            ext r
            exact (hcover r).symm
          rw [heq]
          exact S.finite_toSet
        obtain ⟨r₀, hr₀S⟩ := hSne
        obtain ⟨r, hra, hrb, hrf, hrmax, hsign⟩ :=
          rightmost_simple_root_orientation f a b hcont hb
            hfinite' ⟨r₀, (hcover r₀).mp hr₀S⟩
            (fun z hza hzb hfz =>
              hsimple z ((hcover z).mpr ⟨hza, hzb, hfz⟩))
        have hrS : r ∈ S := (hcover r).mpr ⟨hra, hrb, hrf⟩
        let T := S.erase r
        have hbound : ∃ q, a ≤ q ∧ q < r ∧
            ∀ z ∈ T, z ≤ q := by
          by_cases hTne : T.Nonempty
          · let q := T.max' hTne
            have hqT : q ∈ T := Finset.max'_mem T hTne
            have hqS : q ∈ S := (Finset.mem_erase.mp hqT).2
            have hqne : q ≠ r := (Finset.mem_erase.mp hqT).1
            have hqa : a < q := ((hcover q).mp hqS).1
            have hqle : q ≤ r := by
              obtain ⟨hqa, hqb, hqf⟩ := (hcover q).mp hqS
              exact hrmax q hqa hqb hqf
            refine ⟨q, hqa.le, lt_of_le_of_ne hqle hqne, ?_⟩
            intro z hz
            exact Finset.le_max' T z hz
          · refine ⟨a, le_rfl, hra, ?_⟩
            intro z hz
            exact (hTne ⟨z, hz⟩).elim
        obtain ⟨q, haq, hqr, hTbound⟩ := hbound
        obtain ⟨c, _d, hqc, hcr, _hrd, _hdb, hcase⟩ :=
          simple_root_local_crossing f q r b hqr hrb hrf
            (hsimple r hrS)
        have hac : a < c := lt_of_le_of_lt haq hqc
        have hcb : c < b := lt_trans hcr hrb
        have hTcover : ∀ z, z ∈ T ↔
            a < z ∧ z < c ∧ f z = 0 := by
          intro z
          constructor
          · intro hz
            have hzS : z ∈ S := (Finset.mem_erase.mp hz).2
            have hza := ((hcover z).mp hzS).1
            exact ⟨hza, lt_of_le_of_lt (hTbound z hz) hqc,
              ((hcover z).mp hzS).2.2⟩
          · rintro ⟨hza, hzc, hfz⟩
            apply Finset.mem_erase.mpr
            refine ⟨?_, (hcover z).mpr ⟨hza,
              lt_trans hzc hcb, hfz⟩⟩
            exact ne_of_lt (lt_trans hzc hcr)
        have hcont' : ContinuousOn f (Set.Icc a c) := by
          apply hcont.mono
          intro z hz
          exact ⟨hz.1, le_trans hz.2 hcb.le⟩
        have hTlt : T.card < m := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hrS
        have hsimpleT : ∀ z ∈ T, deriv f z ≠ 0 := by
          intro z hz
          exact hsimple z (Finset.mem_of_mem_erase hz)
        have hcharge : crossingCharge f r =
            endpointCharge (f b) - endpointCharge (f c) ∧
            f c ≠ 0 := by
          rcases lt_or_gt_of_ne hb with hbNeg | hbPos
          · have hdNeg : deriv f r < 0 := by
              rcases lt_or_gt_of_ne (hsimple r hrS) with hdNeg | hdPos
              · exact hdNeg
              · exact ((hsign.mp hdPos).not_gt hbNeg).elim
            simp [not_lt.mpr hdNeg.le] at hcase
            have hcPos : 0 < f c := hcase.1
            exact ⟨by simp [crossingCharge, endpointCharge,
              hbNeg.not_gt, hcPos, hdNeg.not_gt], ne_of_gt hcPos⟩
          · have hdPos : 0 < deriv f r := hsign.mpr hbPos
            simp [hdPos] at hcase
            have hcNeg : f c < 0 := hcase.1
            exact ⟨by simp [crossingCharge, endpointCharge,
              hbPos, hcNeg.not_gt, hdPos], ne_of_lt hcNeg⟩
        have hrec := ih T.card hTlt a c T rfl hac hcont'
          ha hcharge.2 hTcover hsimpleT
        have hsum : ∑ z ∈ S, crossingCharge f z =
            crossingCharge f r + ∑ z ∈ T, crossingCharge f z :=
          (Finset.add_sum_erase S (crossingCharge f) hrS).symm
        rw [hsum, hrec, hcharge.1]
        ring
      · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
        have hno : ∀ r, a < r → r < b → f r ≠ 0 := by
          intro r har hrb hroot
          have hrS : r ∈ S := (hcover r).mpr ⟨har, hrb, hroot⟩
          simp [hSempty] at hrS
        have hsame := same_endpoint_sign_of_no_root
          f a b hab hcont ha hb hno
        rw [hSempty]
        by_cases hapos : 0 < f a
        · have hbpos := hsame.mp hapos
          simp [endpointCharge, hapos, hbpos]
        · have hbnot : ¬0 < f b := fun h => hapos (hsame.mpr h)
          simp [endpointCharge, hapos, hbnot]
  let S : Finset ℝ := hfinite.toFinset
  have hcover : ∀ r, r ∈ S ↔ a < r ∧ r < b ∧ f r = 0 := by
    intro r
    exact hfinite.mem_toFinset
  exact main S.card a b S rfl hab hcont ha hb hcover
    (fun r hr =>
      let ⟨har, hrb, hfr⟩ := (hcover r).mp hr
      hsimple r har hrb hfr)

/-- When the residual is negative at the left boundary and positive
at the right boundary, its simple roots have total signed charge one. -/
theorem finite_simple_roots_signed_crossing_one
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b)
    (hfinite : {r : ℝ | a < r ∧ r < b ∧ f r = 0}.Finite)
    (hsimple : ∀ r, a < r → r < b → f r = 0 →
      deriv f r ≠ 0) :
    ∑ r ∈ hfinite.toFinset, crossingCharge f r = 1 := by
  have h := finite_simple_roots_signed_crossing_count f a b hab
    hcont (ne_of_lt ha) (ne_of_gt hb) hfinite hsimple
  simpa [endpointCharge, ha.not_gt, hb] using h

end
end PhosphorylationStableCapacity
