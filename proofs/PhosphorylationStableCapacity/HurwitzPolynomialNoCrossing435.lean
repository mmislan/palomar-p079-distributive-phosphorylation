module
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialCoefficientNeighborhood435
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialRightHalfPlaneBound435
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.ClusterPt
public import Mathlib.Order.Filter.Finite

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology BigOperators

/-- Fixed finite degree converts coefficient continuity into continuity of
every evaluation. No topology on an infinite coefficient sequence is needed. -/
theorem fixed_degree_polynomial_eval_continuous
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree ≤ d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (z : ℂ) : Continuous (fun t => (P t).eval z) := by
  classical
  have heq : (fun t => (P t).eval z) =
      (fun t => ∑ i ∈ Finset.range (d+1), (P t).coeff i*z^i) := by
    funext t
    exact (P t).eval_eq_sum_range' (Nat.lt_succ_iff.mpr (hdegree t)) z
  rw [heq]
  apply continuous_finsetSum
  intro i hi
  exact (hcoeff i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).mul continuous_const

/-- The strict-Hurwitz parameter set is open for any monic constant-degree
family with continuous coefficients. Repeated roots are allowed. -/
theorem monic_fixed_degree_hurwitz_parameter_set_open
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (P t).Monic)
    (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i)) :
    IsOpen {t | ∀ z : ℂ, (P t).eval z = 0 → z.re < 0} := by
  classical
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hroots : ∀ z ∈ (P a).roots, z.re < 0 := by
    intro z hz
    exact ha z (Polynomial.isRoot_of_mem_roots hz)
  obtain ⟨ε, hε, hneighborhood⟩ :=
    monic_hurwitz_coefficient_neighborhood (P a) (hmonic a) hroots
  have hnear : ∀ᶠ b in 𝓝 a,
      ∀ i ∈ Finset.range (d+1), ‖(P b).coeff i-(P a).coeff i‖ ≤ ε := by
    apply (eventually_all_finset (Finset.range (d+1))).mpr
    intro i hi
    have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hc : Continuous (fun b => ‖(P b).coeff i-(P a).coeff i‖) :=
      ((hcoeff i hid).sub continuous_const).norm
    have hsmall : ∀ᶠ b in 𝓝 a, ‖(P b).coeff i-(P a).coeff i‖ < ε :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    exact hsmall.mono (fun _ hb => hb.le)
  filter_upwards [hnear] with b hb
  apply hneighborhood (P b)
  · simpa only [hdegree b, hdegree a] using (le_rfl : d ≤ d)
  · intro i hi
    have hid : i ≤ d := by simpa only [hdegree a] using hi
    exact hb i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hid))

/-- If imaginary-axis roots are excluded throughout a monic fixed-degree
family, its strict-Hurwitz parameter set is also closed. The proof uses
evaluation limits and a nonvanishing bound, without choosing root labels. -/
theorem monic_fixed_degree_hurwitz_parameter_set_closed_of_no_axis
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (P t).Monic)
    (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (haxis : ∀ t, ∀ z : ℂ, z.re = 0 → (P t).eval z ≠ 0) :
    IsClosed {t | ∀ z : ℂ, (P t).eval z = 0 → z.re < 0} := by
  classical
  apply isClosed_iff_forall_filter.mpr
  intro a l hnebot hstable hlimit
  let : NeBot l := hnebot
  have hevent : ∀ᶠ b in l,
      ∀ z : ℂ, (P b).eval z = 0 → z.re < 0 :=
    le_principal_iff.mp hstable
  have hP : ∀ᶠ b in l, (P b).Monic ∧ (P b).natDegree = d ∧
      ∀ z ∈ (P b).roots, z.re ≤ 0 := by
    filter_upwards [hevent] with b hb
    refine ⟨hmonic b, hdegree b, ?_⟩
    intro z hz
    exact (hb z (Polynomial.isRoot_of_mem_roots hz)).le
  have heval : ∀ z : ℂ,
      Tendsto (fun b => (P b).eval z) l (𝓝 ((P a).eval z)) := by
    intro z
    exact ((fixed_degree_polynomial_eval_continuous P d
      (fun b => (hdegree b).le) hcoeff z).tendsto a).mono_left hlimit
  exact evaluation_limit_roots_re_neg_of_no_axis l P (P a) d hP heval (haxis a)

/-- A continuous monic constant-degree polynomial family on a preconnected
space cannot lose strict Hurwitz stability without an imaginary-axis root.
One stable parameter therefore makes every parameter stable. No simple-root
assumption and no Routh criterion enter this theorem. -/
theorem monic_fixed_degree_hurwitz_of_no_axis
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (P : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (P t).Monic)
    (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (haxis : ∀ t, ∀ z : ℂ, z.re = 0 → (P t).eval z ≠ 0)
    (t₀ : T) (h₀ : ∀ z : ℂ, (P t₀).eval z = 0 → z.re < 0) :
    ∀ t, ∀ z : ℂ, (P t).eval z = 0 → z.re < 0 := by
  let S : Set T := {t | ∀ z : ℂ, (P t).eval z = 0 → z.re < 0}
  have hopen : IsOpen S :=
    monic_fixed_degree_hurwitz_parameter_set_open P d hmonic hdegree hcoeff
  have hclosed : IsClosed S :=
    monic_fixed_degree_hurwitz_parameter_set_closed_of_no_axis
      P d hmonic hdegree hcoeff haxis
  have hall : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, h₀⟩
  intro t
  have ht : t ∈ S := by rw [hall]; exact Set.mem_univ t
  exact ht

end

end PhosphorylationStableCapacity
