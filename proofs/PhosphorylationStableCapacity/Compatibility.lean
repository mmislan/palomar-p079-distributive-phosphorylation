module
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Fin
public import proofs.PhosphorylationSharpness.Source

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

/-- The three conserved totals defining one literal mass-action compatibility class. -/
def InClass {n : ℕ} (ET FT ST : ℝ) (x : State n) : Prop :=
  totalE x = ET ∧ totalF x = FT ∧ totalS x = ST

/-- Coordinates within a class: free substrates after `S₀` and both complex lists. -/
structure ClassCoord (n : ℕ) where
  S : Fin n → ℝ
  C : Fin n → ℝ
  D : Fin n → ℝ

def chart {n : ℕ} (x : State n) : ClassCoord n where
  S i := x.S i.succ
  C := x.C
  D := x.D

/-- Recover all literal species from class coordinates and three totals. -/
def unChart {n : ℕ} (ET FT ST : ℝ) (u : ClassCoord n) : State n where
  S := Fin.cases (ST - (∑ i, u.S i) - (∑ i, u.C i) - (∑ i, u.D i)) u.S
  E := ET - ∑ i, u.C i
  F := FT - ∑ i, u.D i
  C := u.C
  D := u.D

theorem chart_unChart {n : ℕ} (ET FT ST : ℝ) (u : ClassCoord n) :
    chart (unChart ET FT ST u) = u := by
  rfl

theorem unChart_inClass {n : ℕ} (ET FT ST : ℝ) (u : ClassCoord n) :
    InClass ET FT ST (unChart ET FT ST u) := by
  unfold InClass
  constructor
  · simp [totalE, unChart]
  constructor
  · simp [totalF, unChart]
  · simp [totalS, unChart, Fin.sum_univ_succ]
    ring

theorem unChart_chart_of_inClass {n : ℕ} (ET FT ST : ℝ) (x : State n)
    (h : InClass ET FT ST x) : unChart ET FT ST (chart x) = x := by
  rcases x with ⟨S, E, F, C, D⟩
  rcases h with ⟨hE, hF, hS⟩
  dsimp [totalE] at hE
  dsimp [totalF] at hF
  dsimp [totalS] at hS
  rw [Fin.sum_univ_succ] at hS
  dsimp [unChart, chart]
  congr 1
  · funext i
    refine Fin.cases ?_ ?_ i
    · dsimp [unChart, chart]
      linarith
    · intro j
      rfl
  · linarith
  · linarith

/-- The kinase total has zero derivative under the literal full field. -/
theorem totalE_field_zero {n : ℕ} (k : Rates n) (x : State n) :
    totalE (field k x) = 0 := by
  simp only [totalE, field]
  rw [← Finset.sum_add_distrib]
  simp [add_assoc, add_comm]

/-- The phosphatase total has zero derivative under the literal full field. -/
theorem totalF_field_zero {n : ℕ} (k : Rates n) (x : State n) :
    totalF (field k x) = 0 := by
  simp only [totalF, field]
  rw [← Finset.sum_add_distrib]
  simp [add_assoc, add_comm]

/-- The total substrate count, including both types of complex, has zero derivative. -/
theorem totalS_field_zero {n : ℕ} (k : Rates n) (x : State n) :
    totalS (field k x) = 0 := by
  simp only [totalS, field]
  simp [Finset.sum_add_distrib, Finset.sum_comm, add_assoc, add_comm]

/-- The full field expressed in the `3n` free coordinates of one class. -/
def restrictedField {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : ClassCoord n) : ClassCoord n :=
  chart (field k (unChart ET FT ST u))

theorem equilibrium_iff_restricted {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : ClassCoord n) :
    Equilibrium k (unChart ET FT ST u) ↔
      (∀ i, (restrictedField ET FT ST k u).S i = 0) ∧
      (∀ i, (restrictedField ET FT ST k u).C i = 0) ∧
      (∀ i, (restrictedField ET FT ST k u).D i = 0) := by
  let x := unChart ET FT ST u
  constructor
  · intro h
    rcases h with ⟨hS, hE, hF, hC, hD⟩
    exact ⟨fun i => hS i.succ, hC, hD⟩
  · rintro ⟨hS, hC, hD⟩
    have hS' (i : Fin n) : (field k x).S i.succ = 0 := hS i
    have hC' (i : Fin n) : (field k x).C i = 0 := hC i
    have hD' (i : Fin n) : (field k x).D i = 0 := hD i
    have hE : (field k x).E = 0 := by
      have ht := totalE_field_zero k x
      simp [totalE, hC'] at ht
      exact ht
    have hF : (field k x).F = 0 := by
      have ht := totalF_field_zero k x
      simp [totalF, hD'] at ht
      exact ht
    have hS0 : (field k x).S 0 = 0 := by
      have ht := totalS_field_zero k x
      simp [totalS, Fin.sum_univ_succ, hS', hC', hD'] at ht
      exact ht
    refine ⟨?_, hE, hF, hC', hD'⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · exact hS0
    · exact hS'

/-- Every velocity lies in the zero-total tangent space. -/
theorem field_in_zero_class {n : ℕ} (k : Rates n) (x : State n) :
    InClass 0 0 0 (field k x) := by
  exact ⟨totalE_field_zero k x, totalF_field_zero k x,
    totalS_field_zero k x⟩

/-- The full velocity is the zero-total lift of the restricted class velocity. -/
theorem field_eq_unChart_restricted {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : ClassCoord n) :
    field k (unChart ET FT ST u) =
      unChart 0 0 0 (restrictedField ET FT ST k u) := by
  exact (unChart_chart_of_inClass 0 0 0
    (field k (unChart ET FT ST u))
    (field_in_zero_class k (unChart ET FT ST u))).symm

end
end PhosphorylationStableCapacity
