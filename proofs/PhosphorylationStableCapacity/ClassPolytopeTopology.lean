module
public import proofs.PhosphorylationStableCapacity.ClassPositiveCenter
public import proofs.PhosphorylationStableCapacity.Jacobian

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

private theorem setOf_forall_compat {α ι : Type*} (P : ι → α → Prop) :
    {x : α | ∀ i, P i x} = ⋂ i, {x : α | P i x} := by
  ext x
  simp

private theorem setOf_and_compat {α : Type*} (P Q : α → Prop) :
    {x : α | P x ∧ Q x} = {x : α | P x} ∩ {x : α | Q x} := by
  ext x
  rfl

/-- The literal nonnegative compatibility class in its `3n` free
coordinate chart, written as six families of linear inequalities. -/
def classPolytope (n : ℕ) (ET FT ST : ℝ) : Set (CoordinateSpace n) :=
  {u | (∀ i : Fin n, 0 ≤ u.1 i) ∧
    (∀ i : Fin n, 0 ≤ u.2.1 i) ∧
    (∀ i : Fin n, 0 ≤ u.2.2 i) ∧
    (∑ i, u.1 i) + (∑ i, u.2.1 i) + (∑ i, u.2.2 i) ≤ ST ∧
    (∑ i, u.2.1 i) ≤ ET ∧ (∑ i, u.2.2 i) ≤ FT}

/-- The coordinate inequalities are exactly nonnegativity of every
species after reconstructing the three conserved totals. -/
theorem mem_classPolytope_iff_nonnegative {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n) :
    u ∈ classPolytope n ET FT ST ↔
      NonnegativeState (unChart ET FT ST (ofCoordinateSpace u)) := by
  constructor
  · rintro ⟨hS, hC, hD, hST, hET, hFT⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero =>
          change 0 ≤ ST - (∑ i, u.1 i) -
            (∑ i, u.2.1 i) - (∑ i, u.2.2 i)
          linarith
      | succ i => exact hS i
    · change 0 ≤ ET - ∑ i, u.2.1 i
      linarith
    · change 0 ≤ FT - ∑ i, u.2.2 i
      linarith
    · exact hC
    · exact hD
  · intro h
    rcases h with ⟨hS, hE, hF, hC, hD⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      exact hS i.succ
    · exact hC
    · exact hD
    · have h0 := hS 0
      change 0 ≤ ST - (∑ i, u.1 i) -
        (∑ i, u.2.1 i) - (∑ i, u.2.2 i) at h0
      linarith
    · change 0 ≤ ET - ∑ i, u.2.1 i at hE
      linarith
    · change 0 ≤ FT - ∑ i, u.2.2 i at hF
      linarith

theorem classPolytope_isClosed (n : ℕ) (ET FT ST : ℝ) :
    IsClosed (classPolytope n ET FT ST) := by
  have hS : IsClosed {u : CoordinateSpace n | ∀ i : Fin n, 0 ≤ u.1 i} := by
    rw [setOf_forall_compat]
    apply isClosed_iInter
    intro i
    have hc : Continuous (fun u : CoordinateSpace n => u.1 i) := by fun_prop
    exact isClosed_le continuous_const hc
  have hC : IsClosed {u : CoordinateSpace n | ∀ i : Fin n, 0 ≤ u.2.1 i} := by
    rw [setOf_forall_compat]
    apply isClosed_iInter
    intro i
    have hc : Continuous (fun u : CoordinateSpace n => u.2.1 i) := by fun_prop
    exact isClosed_le continuous_const hc
  have hD : IsClosed {u : CoordinateSpace n | ∀ i : Fin n, 0 ≤ u.2.2 i} := by
    rw [setOf_forall_compat]
    apply isClosed_iInter
    intro i
    have hc : Continuous (fun u : CoordinateSpace n => u.2.2 i) := by fun_prop
    exact isClosed_le continuous_const hc
  have hST : IsClosed {u : CoordinateSpace n |
      (∑ i, u.1 i) + (∑ i, u.2.1 i) + (∑ i, u.2.2 i) ≤ ST} := by
    have hc : Continuous (fun u : CoordinateSpace n =>
      (∑ i, u.1 i) + (∑ i, u.2.1 i) + (∑ i, u.2.2 i)) := by fun_prop
    exact isClosed_le hc continuous_const
  have hET : IsClosed {u : CoordinateSpace n | (∑ i, u.2.1 i) ≤ ET} := by
    have hc : Continuous (fun u : CoordinateSpace n => ∑ i, u.2.1 i) := by fun_prop
    exact isClosed_le hc continuous_const
  have hFT : IsClosed {u : CoordinateSpace n | (∑ i, u.2.2 i) ≤ FT} := by
    have hc : Continuous (fun u : CoordinateSpace n => ∑ i, u.2.2 i) := by fun_prop
    exact isClosed_le hc continuous_const
  simpa only [classPolytope, setOf_and_compat] using
    hS.inter (hC.inter (hD.inter (hST.inter (hET.inter hFT))))

/-- The closed literal class lies in a compact product interval.
This is the compactness interface needed for the degree homotopy. -/
theorem classPolytope_isCompact (n : ℕ) (ET FT ST : ℝ) :
    IsCompact (classPolytope n ET FT ST) := by
  let upper : CoordinateSpace n :=
    (fun _ => ST, fun _ => min ET ST, fun _ => min FT ST)
  have hsubset : classPolytope n ET FT ST ⊆ Set.Icc 0 upper := by
    intro u hu
    have hx : NonnegativeState
        (unChart ET FT ST (ofCoordinateSpace u)) :=
      (mem_classPolytope_iff_nonnegative ET FT ST u).mp hu
    have hb := nonnegative_class_species_bounds ET FT ST
      (unChart ET FT ST (ofCoordinateSpace u)) hx
      (unChart_inClass ET FT ST (ofCoordinateSpace u))
    constructor
    · change (0 : CoordinateSpace n) ≤ u
      exact ⟨fun i => hx.1 i.succ,
        ⟨hx.2.2.2.1, hx.2.2.2.2⟩⟩
    · change u ≤ upper
      exact ⟨fun i => hb.1 i.succ,
        ⟨hb.2.2.2.1, hb.2.2.2.2⟩⟩
  exact IsCompact.of_isClosed_subset isCompact_Icc
    (classPolytope_isClosed n ET FT ST) hsubset

/-- Convexity of the literal compatibility polytope follows directly
from its six linear inequality families. -/
theorem classPolytope_convex (n : ℕ) (ET FT ST : ℝ) :
    Convex ℝ (classPolytope n ET FT ST) := by
  intro u hu v hv a b ha hb hab
  rcases hu with ⟨huS, huC, huD, huST, huET, huFT⟩
  rcases hv with ⟨hvS, hvC, hvD, hvST, hvET, hvFT⟩
  have hSsum : (∑ i : Fin n, (a • u + b • v).1 i) =
      a*(∑ i, u.1 i) + b*(∑ i, v.1 i) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hCsum : (∑ i : Fin n, (a • u + b • v).2.1 i) =
      a*(∑ i, u.2.1 i) + b*(∑ i, v.2.1 i) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  have hDsum : (∑ i : Fin n, (a • u + b • v).2.2 i) =
      a*(∑ i, u.2.2 i) + b*(∑ i, v.2.2 i) := by
    simp [Finset.sum_add_distrib, Finset.mul_sum]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change 0 ≤ a*u.1 i + b*v.1 i
    exact add_nonneg (mul_nonneg ha (huS i)) (mul_nonneg hb (hvS i))
  · intro i
    change 0 ≤ a*u.2.1 i + b*v.2.1 i
    exact add_nonneg (mul_nonneg ha (huC i)) (mul_nonneg hb (hvC i))
  · intro i
    change 0 ≤ a*u.2.2 i + b*v.2.2 i
    exact add_nonneg (mul_nonneg ha (huD i)) (mul_nonneg hb (hvD i))
  · rw [hSsum, hCsum, hDsum]
    nlinarith [mul_le_mul_of_nonneg_left huST ha,
      mul_le_mul_of_nonneg_left hvST hb,
      congrArg (· * ST) hab]
  · rw [hCsum]
    nlinarith [mul_le_mul_of_nonneg_left huET ha,
      mul_le_mul_of_nonneg_left hvET hb,
      congrArg (· * ET) hab]
  · rw [hDsum]
    nlinarith [mul_le_mul_of_nonneg_left huFT ha,
      mul_le_mul_of_nonneg_left hvFT hb,
      congrArg (· * FT) hab]

/-- Strict coordinate inequalities characterize the interior species
region and form an open subset of the nonnegative class. -/
def classPolytopeStrict (n : ℕ) (ET FT ST : ℝ) :
    Set (CoordinateSpace n) :=
  {u | (∀ i : Fin n, 0 < u.1 i) ∧
    (∀ i : Fin n, 0 < u.2.1 i) ∧
    (∀ i : Fin n, 0 < u.2.2 i) ∧
    (∑ i, u.1 i) + (∑ i, u.2.1 i) + (∑ i, u.2.2 i) < ST ∧
    (∑ i, u.2.1 i) < ET ∧ (∑ i, u.2.2 i) < FT}

theorem classPolytopeStrict_isOpen (n : ℕ) (ET FT ST : ℝ) :
    IsOpen (classPolytopeStrict n ET FT ST) := by
  have hS : IsOpen {u : CoordinateSpace n | ∀ i : Fin n, 0 < u.1 i} := by
    rw [setOf_forall_compat]
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun u : CoordinateSpace n => u.1 i) := by fun_prop
    exact isOpen_lt continuous_const hc
  have hC : IsOpen {u : CoordinateSpace n | ∀ i : Fin n, 0 < u.2.1 i} := by
    rw [setOf_forall_compat]
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun u : CoordinateSpace n => u.2.1 i) := by fun_prop
    exact isOpen_lt continuous_const hc
  have hD : IsOpen {u : CoordinateSpace n | ∀ i : Fin n, 0 < u.2.2 i} := by
    rw [setOf_forall_compat]
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun u : CoordinateSpace n => u.2.2 i) := by fun_prop
    exact isOpen_lt continuous_const hc
  have hST : IsOpen {u : CoordinateSpace n |
      (∑ i, u.1 i) + (∑ i, u.2.1 i) + (∑ i, u.2.2 i) < ST} := by
    have hc : Continuous (fun u : CoordinateSpace n =>
      (∑ i, u.1 i) + (∑ i, u.2.1 i) + (∑ i, u.2.2 i)) := by fun_prop
    exact isOpen_lt hc continuous_const
  have hET : IsOpen {u : CoordinateSpace n | (∑ i, u.2.1 i) < ET} := by
    have hc : Continuous (fun u : CoordinateSpace n => ∑ i, u.2.1 i) := by fun_prop
    exact isOpen_lt hc continuous_const
  have hFT : IsOpen {u : CoordinateSpace n | (∑ i, u.2.2 i) < FT} := by
    have hc : Continuous (fun u : CoordinateSpace n => ∑ i, u.2.2 i) := by fun_prop
    exact isOpen_lt hc continuous_const
  simpa only [classPolytopeStrict, setOf_and_compat] using
    hS.inter (hC.inter (hD.inter (hST.inter (hET.inter hFT))))

theorem classPolytopeStrict_subset (n : ℕ) (ET FT ST : ℝ) :
    classPolytopeStrict n ET FT ST ⊆ classPolytope n ET FT ST := by
  intro u hu
  rcases hu with ⟨hS, hC, hD, hST, hET, hFT⟩
  exact ⟨fun i => (hS i).le, fun i => (hC i).le,
    fun i => (hD i).le, hST.le, hET.le, hFT.le⟩

theorem positive_state_mem_classPolytopeStrict {n : ℕ}
    (ET FT ST : ℝ) (x : State n)
    (hx : x.Positive) (hclass : InClass ET FT ST x) :
    toCoordinateSpace (chart x) ∈ classPolytopeStrict n ET FT ST := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hx.1 i.succ
  · exact hx.2.2.2.1
  · exact hx.2.2.2.2
  · have htotal := hclass.2.2
    dsimp [totalS] at htotal
    rw [Fin.sum_univ_succ] at htotal
    dsimp [toCoordinateSpace, chart]
    linarith [hx.1 0]
  · have htotal := hclass.1
    dsimp [totalE] at htotal
    dsimp [toCoordinateSpace, chart]
    linarith [hx.2.1]
  · have htotal := hclass.2.1
    dsimp [totalF] at htotal
    dsimp [toCoordinateSpace, chart]
    linarith [hx.2.2.1]

/-- The class of any positive totals has nonempty interior in the
exact class-coordinate topology. -/
theorem classPolytope_interior_nonempty (n : ℕ)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (hST : 0 < ST) :
    (interior (classPolytope n ET FT ST)).Nonempty := by
  obtain ⟨x, hx, hclass⟩ :=
    positive_class_nonempty n ET FT ST hET hFT hST
  let u : CoordinateSpace n := toCoordinateSpace (chart x)
  have hu : u ∈ classPolytopeStrict n ET FT ST :=
    positive_state_mem_classPolytopeStrict ET FT ST x hx hclass
  exact ⟨u, (interior_maximal (classPolytopeStrict_subset n ET FT ST)
    (classPolytopeStrict_isOpen n ET FT ST)) hu⟩

/-- Every equilibrium in the nonnegative class is an interior zero of
the exact class-restricted field. -/
theorem class_equilibrium_interior {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hET : 0 < ET) (hFT : 0 < FT) (hST : 0 < ST)
    (hk : k.Positive)
    (hu : u ∈ classPolytope n ET FT ST)
    (heq : restrictedFieldEuclid ET FT ST k u = 0) :
    u ∈ interior (classPolytope n ET FT ST) := by
  let x := unChart ET FT ST (ofCoordinateSpace u)
  have hx : NonnegativeState x :=
    (mem_classPolytope_iff_nonnegative ET FT ST u).mp hu
  have hclass : InClass ET FT ST x :=
    unChart_inClass ET FT ST (ofCoordinateSpace u)
  have hzero : Equilibrium k x :=
    (restrictedFieldEuclid_eq_zero_iff ET FT ST k u).mp heq
  have hpositive := equilibrium_positive_of_nonnegative
    k x hk hx hzero ET FT ST hET hFT hST hclass
  have hstrict : u ∈ classPolytopeStrict n ET FT ST := by
    have h := positive_state_mem_classPolytopeStrict
      ET FT ST x hpositive hclass
    simpa only [x, chart_unChart, to_ofCoordinateSpace] using h
  exact (interior_maximal (classPolytopeStrict_subset n ET FT ST)
    (classPolytopeStrict_isOpen n ET FT ST)) hstrict

theorem restrictedField_nonzero_on_class_boundary {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hET : 0 < ET) (hFT : 0 < FT) (hST : 0 < ST)
    (hk : k.Positive)
    (hu : u ∈ classPolytope n ET FT ST)
    (hboundary : u ∉ interior (classPolytope n ET FT ST)) :
    restrictedFieldEuclid ET FT ST k u ≠ 0 := by
  intro hzero
  exact hboundary (class_equilibrium_interior ET FT ST k u
    hET hFT hST hk hu hzero)

end
end PhosphorylationStableCapacity
