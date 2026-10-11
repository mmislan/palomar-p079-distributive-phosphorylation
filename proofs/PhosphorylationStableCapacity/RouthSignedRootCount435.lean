module
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialRightHalfPlaneBound435
public import Mathlib.Algebra.Polynomial.Derivative
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- The precise factorization needed for one positive simple real root
and a Hurwitz complement. This is a target predicate, not a consequence
of signed minors assumed without proof. The degree-one case has q = 1. -/
def PositiveRealRootHurwitzFactorization (d : ℕ) (p : ℂ[X]) : Prop :=
  1 ≤ d ∧ ∃ u : ℝ, 0 < u ∧ ∃ q : ℂ[X],
    q.Monic ∧ q.natDegree = d-1 ∧
      (∀ w ∈ q.roots, w.re < 0) ∧ p = (X-C (u : ℂ))*q

theorem positiveRealRootHurwitzFactorization_monic_and_degree
    (d : ℕ) (p : ℂ[X]) (hf : PositiveRealRootHurwitzFactorization d p) :
    p.Monic ∧ p.natDegree = d := by
  obtain ⟨hd, u, _hu, q, hq, hdegree, _hroots, hfactor⟩ := hf
  rw [hfactor]
  refine ⟨(monic_X_sub_C (u : ℂ)).mul hq, ?_⟩
  rw [(monic_X_sub_C (u : ℂ)).natDegree_mul hq, natDegree_X_sub_C, hdegree]
  omega

/-- Once the actual positive-root/Hurwitz-tail factorization is supplied,
its root is simple and every other complex root is strictly left. -/
theorem positiveRealRootHurwitzFactorization_root_classification
    (d : ℕ) (p : ℂ[X]) (hf : PositiveRealRootHurwitzFactorization d p) :
    ∃ u : ℝ, 0 < u ∧ p.eval (u : ℂ) = 0 ∧
      p.derivative.eval (u : ℂ) ≠ 0 ∧
      ∀ z : ℂ, p.eval z = 0 → z = (u : ℂ) ∨ z.re < 0 := by
  obtain ⟨_hd, u, hu, q, hq, _hdegree, hroots, hfactor⟩ := hf
  have hleft : ∀ z : ℂ, q.eval z = 0 → z.re < 0 := by
    intro z hz
    exact hroots z ((Polynomial.mem_roots hq.ne_zero).mpr hz)
  have hqu : q.eval (u : ℂ) ≠ 0 := by
    intro hz
    have hneg := hleft (u : ℂ) hz
    have huNeg : u < 0 := by simpa only [Complex.ofReal_re] using hneg
    exact (not_lt_of_ge hu.le) huNeg
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rw [hfactor]
    simp
  · simpa only [hfactor, derivative_mul, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_add, eval_mul, eval_sub, eval_X,
      eval_C, eval_one, sub_self, zero_mul, one_mul, add_zero] using hqu
  · intro z hz
    rw [hfactor, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero] at hz
    rcases hz with hz | hz
    · exact Or.inl (sub_eq_zero.mp hz)
    · exact Or.inr (hleft z hz)

/-- A real positive linear factor supplies an imaginary-part margin,
uniform in the location of that real root. The Hurwitz tail supplies
the remaining right-half-plane power. Multiplicities are unrestricted. -/
theorem positiveRealRootHurwitzFactorization_eval_margin
    (d : ℕ) (p : ℂ[X]) (hf : PositiveRealRootHurwitzFactorization d p)
    (z : ℂ) (hz : 0 ≤ z.re) :
    |z.im| *z.re^(d-1) ≤ ‖p.eval z‖ := by
  obtain ⟨_hd, u, _hu, q, hq, hdegree, hroots, hfactor⟩ := hf
  have him : |z.im| ≤ ‖z-(u : ℂ)‖ := by
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
      Complex.abs_im_le_norm (z-(u : ℂ))
  have htail : z.re^(d-1) ≤ ‖q.eval z‖ := by
    simpa only [hdegree] using
      monic_eval_norm_lower_bound_of_roots_left q hq
        (fun w hw => (hroots w hw).le) z hz
  have hproduct := mul_le_mul him htail (pow_nonneg hz _) (norm_nonneg _)
  simpa only [hfactor, eval_mul, eval_sub, eval_X, eval_C, norm_mul] using hproduct

/-- Limits of these one-positive-root families cannot acquire a nonreal
root in the open right half-plane. The positive root need not be given
continuously or even bounded; its real location drops out of the margin.
This is a closure lemma, not a signed Routh criterion. -/
theorem positiveRealRootHurwitzFactorization_limit_no_nonreal_right_root
    {ι : Type*} (l : Filter ι) [NeBot l]
    (P : ι → ℂ[X]) (q : ℂ[X]) (d : ℕ)
    (hP : ∀ᶠ i in l, PositiveRealRootHurwitzFactorization d (P i))
    (hlim : ∀ z : ℂ, Tendsto (fun i => (P i).eval z) l (𝓝 (q.eval z))) :
    ∀ z : ℂ, 0 < z.re → q.eval z = 0 → z.im = 0 := by
  intro z hz hroot
  by_contra him
  have hbound : ∀ᶠ i in l, |z.im| *z.re^(d-1) ≤ ‖(P i).eval z‖ := by
    filter_upwards [hP] with i hi
    exact positiveRealRootHurwitzFactorization_eval_margin d (P i) hi z hz.le
  have hlimit : |z.im| *z.re^(d-1) ≤ ‖q.eval z‖ :=
    ge_of_tendsto (hlim z).norm hbound
  rw [hroot, norm_zero] at hlimit
  exact (not_le_of_gt (mul_pos (abs_pos.mpr him) (pow_pos hz _))) hlimit

end

end PhosphorylationStableCapacity
