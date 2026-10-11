module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial Filter
open scoped Topology

noncomputable section

private theorem complex_multiset_prod_norm_lower_bound
    (s : Multiset ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ w ∈ s, c ≤ ‖w‖) : c ^ s.card ≤ ‖s.prod‖ := by
  revert h
  induction s using Multiset.induction_on with
  | empty =>
      intro _
      simp
  | cons w s ih =>
      intro h
      have hw : c ≤ ‖w‖ := h w (by simp)
      have hs : ∀ u ∈ s, c ≤ ‖u‖ := by
        intro u hu
        exact h u (by simp [hu])
      calc
        c ^ (w ::ₘ s).card = c ^ s.card * c := by
          rw [Multiset.card_cons, pow_succ]
        _ ≤ ‖s.prod‖ * ‖w‖ := mul_le_mul (ih hs) hw hc (norm_nonneg _)
        _ = ‖(w ::ₘ s).prod‖ := by
          rw [Multiset.prod_cons, norm_mul, mul_comm]

/-- A monic polynomial with all roots in the closed left half-plane
has an explicit nonvanishing margin at each point in the open right
half-plane. Multiplicities and constant polynomials are included. -/
theorem monic_eval_norm_lower_bound_of_roots_left
    (p : ℂ[X]) (hp : p.Monic)
    (hroots : ∀ w ∈ p.roots, w.re ≤ 0)
    (z : ℂ) (hz : 0 ≤ z.re) :
    z.re ^ p.natDegree ≤ ‖p.eval z‖ := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hfactor : ∀ w ∈ p.roots.map (fun u => z-u), z.re ≤ ‖w‖ := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hw
    calc
      z.re ≤ (z-u).re := by
        rw [Complex.sub_re]
        linarith [hroots u hu]
      _ ≤ ‖z-u‖ := Complex.re_le_norm _
  have hbound := complex_multiset_prod_norm_lower_bound
    (p.roots.map (fun u => z-u)) z.re hz hfactor
  rw [hsplit.eval_eq_prod_roots_of_monic hp z]
  simpa only [Multiset.card_map, hsplit.natDegree_eq_card_roots] using hbound

/-- Evaluation limits of fixed-degree monic polynomials with roots on
the left cannot acquire a root in the open right half-plane. This avoids
choosing continuous root labels or assuming simple roots. -/
theorem evaluation_limit_roots_re_nonpos
    {ι : Type*} (l : Filter ι) [NeBot l]
    (P : ι → ℂ[X]) (q : ℂ[X]) (d : ℕ)
    (hP : ∀ᶠ i in l, (P i).Monic ∧ (P i).natDegree = d ∧
      ∀ w ∈ (P i).roots, w.re ≤ 0)
    (hlim : ∀ z : ℂ, Tendsto (fun i => (P i).eval z) l (𝓝 (q.eval z))) :
    ∀ z : ℂ, q.eval z = 0 → z.re ≤ 0 := by
  intro z hz
  by_contra hnonpos
  have hpos : 0 < z.re := lt_of_not_ge hnonpos
  have hbound : ∀ᶠ i in l, z.re ^ d ≤ ‖(P i).eval z‖ := by
    filter_upwards [hP] with i hi
    have h := monic_eval_norm_lower_bound_of_roots_left
      (P i) hi.1 hi.2.2 z hpos.le
    simpa only [hi.2.1] using h
  have hlimit : z.re ^ d ≤ ‖q.eval z‖ := ge_of_tendsto (hlim z).norm hbound
  rw [hz, norm_zero] at hlimit
  exact (not_le_of_gt (pow_pos hpos d)) hlimit

/-- Excluding imaginary-axis roots upgrades the closed-half-plane limit
to the strict Hurwitz condition. This is a limit transfer, not a proof
that an arbitrary Routh homotopy is stable before taking its limit. -/
theorem evaluation_limit_roots_re_neg_of_no_axis
    {ι : Type*} (l : Filter ι) [NeBot l]
    (P : ι → ℂ[X]) (q : ℂ[X]) (d : ℕ)
    (hP : ∀ᶠ i in l, (P i).Monic ∧ (P i).natDegree = d ∧
      ∀ w ∈ (P i).roots, w.re ≤ 0)
    (hlim : ∀ z : ℂ, Tendsto (fun i => (P i).eval z) l (𝓝 (q.eval z)))
    (haxis : ∀ z : ℂ, z.re = 0 → q.eval z ≠ 0) :
    ∀ z : ℂ, q.eval z = 0 → z.re < 0 := by
  intro z hz
  have hle := evaluation_limit_roots_re_nonpos l P q d hP hlim z hz
  exact lt_of_le_of_ne hle (fun heq => haxis z heq hz)

end
end PhosphorylationStableCapacity
