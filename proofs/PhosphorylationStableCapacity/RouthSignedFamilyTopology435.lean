module
public import proofs.PhosphorylationStableCapacity.RouthSignedRootCount435
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialNoCrossing435
public import Mathlib.Algebra.Polynomial.Div

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology BigOperators

/-- The positive real root is unique among positive real roots and is
algebraically simple. This property alone does not classify nonreal roots. -/
def UniqueSimplePositiveRealRoot (p : ℂ[X]) : Prop :=
  ∃ u : ℝ, 0 < u ∧ p.eval (u : ℂ) = 0 ∧
    p.derivative.eval (u : ℂ) ≠ 0 ∧
    ∀ v : ℝ, 0 < v → p.eval (v : ℂ) = 0 → v = u

/-- Finite synthetic division has continuous coefficients when both the
polynomial coefficients and its real dividing root vary continuously. -/
theorem fixed_degree_linear_deflation_coeff_continuous
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ)
    (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (u : T → ℝ) (hu : Continuous u) (n : ℕ) :
    Continuous (fun t => ((P t) /ₘ (X-C (u t : ℂ))).coeff n) := by
  classical
  have heq : (fun t => ((P t) /ₘ (X-C (u t : ℂ))).coeff n) =
      (fun t => ∑ i ∈ Finset.Icc (n+1) d,
        (u t : ℂ)^(i-(n+1))*(P t).coeff i) := by
    funext t
    rw [coeff_divByMonic_X_sub_C, hdegree t]
  rw [heq]
  apply continuous_finsetSum
  intro i hi
  exact ((Complex.continuous_ofReal.comp hu).pow _).mul
    (hcoeff i (Finset.mem_Icc.mp hi).2)

/-- Actual linear deflation of a monic polynomial at a root is monic
and has the exact one-less degree. -/
theorem monic_linear_deflation_factorization
    (p : ℂ[X]) (hp : p.Monic) (d : ℕ) (hdegree : p.natDegree = d)
    (u : ℝ) (hroot : p.eval (u : ℂ) = 0) :
    let q := p /ₘ (X-C (u : ℂ))
    q.Monic ∧ q.natDegree = d-1 ∧ p = (X-C (u : ℂ))*q := by
  dsimp
  have hf : (X-C (u : ℂ))*(p /ₘ (X-C (u : ℂ))) = p :=
    mul_divByMonic_eq_iff_isRoot.mpr hroot
  refine ⟨(monic_X_sub_C (u : ℂ)).of_mul_monic_left (hf.symm ▸ hp), ?_, hf.symm⟩
  rw [natDegree_divByMonic p (monic_X_sub_C (u : ℂ)), natDegree_X_sub_C, hdegree]

/-- Root simplicity makes the literal deflation nonzero at the root. -/
theorem linear_deflation_eval_ne_zero_of_simple_root
    (p : ℂ[X]) (u : ℝ) (hroot : p.eval (u : ℂ) = 0)
    (hsimple : p.derivative.eval (u : ℂ) ≠ 0) :
    (p /ₘ (X-C (u : ℂ))).eval (u : ℂ) ≠ 0 := by
  have hf : p = (X-C (u : ℂ))*(p /ₘ (X-C (u : ℂ))) :=
    (mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
  have heval : p.derivative.eval (u : ℂ) =
      (p /ₘ (X-C (u : ℂ))).eval (u : ℂ) := by
    conv_lhs => rw [hf]
    rw [derivative_mul]
    simp
  exact heval ▸ hsimple

/-- A simple unique positive root, axis exclusion, and exclusion of
nonreal open-right roots together prove the full signed factorization. -/
theorem positiveRealRootHurwitzFactorization_of_root_exclusions
    (p : ℂ[X]) (d : ℕ) (hd : 1 ≤ d) (hp : p.Monic)
    (hdegree : p.natDegree = d) (hpositive : UniqueSimplePositiveRealRoot p)
    (haxis : ∀ z : ℂ, z.re = 0 → p.eval z ≠ 0)
    (hnonreal : ∀ z : ℂ, 0 < z.re → p.eval z = 0 → z.im = 0) :
    PositiveRealRootHurwitzFactorization d p := by
  obtain ⟨u, hu, hroot, hsimple, hunique⟩ := hpositive
  let q := p /ₘ (X-C (u : ℂ))
  obtain ⟨hq, hqdegree, hfactor⟩ :=
    monic_linear_deflation_factorization p hp d hdegree u hroot
  have hqu : q.eval (u : ℂ) ≠ 0 :=
    linear_deflation_eval_ne_zero_of_simple_root p u hroot hsimple
  refine ⟨hd, u, hu, q, hq, hqdegree, ?_, hfactor⟩
  intro z hz
  have hqz : q.eval z = 0 := Polynomial.isRoot_of_mem_roots hz
  have hpz : p.eval z = 0 := by rw [hfactor, eval_mul, hqz, mul_zero]
  by_contra hneg
  have hright : 0 ≤ z.re := le_of_not_gt hneg
  have hstrict : 0 < z.re := lt_of_le_of_ne hright
    (fun heq => haxis z heq.symm hpz)
  have him := hnonreal z hstrict hpz
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hzu : z.re = u := hunique z.re hstrict (hzreal ▸ hpz)
  have hzeq : z = (u : ℂ) := hzreal.trans (congrArg Complex.ofReal hzu)
  exact hqu (hzeq ▸ hqz)

/-- The signed factorization set is closed for a fixed-degree continuous
family with unique simple positive roots and no imaginary-axis roots.
The margin proof avoids choosing continuous root labels for this step. -/
theorem signed_factorization_parameter_set_closed
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ t, (P t).Monic) (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (hpositive : ∀ t, UniqueSimplePositiveRealRoot (P t))
    (haxis : ∀ t, ∀ z : ℂ, z.re = 0 → (P t).eval z ≠ 0) :
    IsClosed {t | PositiveRealRootHurwitzFactorization d (P t)} := by
  apply isClosed_iff_forall_filter.mpr
  intro a l hnebot hstable hlimit
  let : NeBot l := hnebot
  have hP : ∀ᶠ b in l, PositiveRealRootHurwitzFactorization d (P b) :=
    le_principal_iff.mp hstable
  have heval : ∀ z : ℂ,
      Tendsto (fun b => (P b).eval z) l (𝓝 ((P a).eval z)) := by
    intro z
    exact ((fixed_degree_polynomial_eval_continuous P d
      (fun b => (hdegree b).le) hcoeff z).tendsto a).mono_left hlimit
  exact positiveRealRootHurwitzFactorization_of_root_exclusions
    (P a) d hd (hmonic a) (hdegree a) (hpositive a) (haxis a)
    (positiveRealRootHurwitzFactorization_limit_no_nonreal_right_root l P (P a) d hP heval)

/-- With the actual unique positive root selected continuously, the
signed factorization set is open. The tail is literal monic division,
and its coefficient continuity is established by a finite sum. -/
theorem signed_factorization_parameter_set_open
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ t, (P t).Monic) (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (u : T → ℝ) (hu : Continuous u) (hupos : ∀ t, 0 < u t)
    (huroot : ∀ t, (P t).eval (u t : ℂ) = 0)
    (husimple : ∀ t, (P t).derivative.eval (u t : ℂ) ≠ 0)
    (huunique : ∀ t, ∀ v : ℝ, 0 < v → (P t).eval (v : ℂ) = 0 → v = u t) :
    IsOpen {t | PositiveRealRootHurwitzFactorization d (P t)} := by
  let Q : T → ℂ[X] := fun t => (P t) /ₘ (X-C (u t : ℂ))
  have hQ (t : T) : (Q t).Monic ∧ (Q t).natDegree = d-1 ∧
      P t = (X-C (u t : ℂ))*(Q t) :=
    monic_linear_deflation_factorization (P t) (hmonic t) d (hdegree t) (u t) (huroot t)
  have heq : {t | PositiveRealRootHurwitzFactorization d (P t)} =
      {t | ∀ z : ℂ, (Q t).eval z = 0 → z.re < 0} := by
    ext t
    constructor
    · intro ht
      obtain ⟨v, hv, hvroot, _hvsimple, hclass⟩ :=
        positiveRealRootHurwitzFactorization_root_classification d (P t) ht
      have hvu : v = u t := huunique t v hv hvroot
      have hqu : (Q t).eval (u t : ℂ) ≠ 0 :=
        linear_deflation_eval_ne_zero_of_simple_root (P t) (u t) (huroot t) (husimple t)
      intro z hz
      have hpz : (P t).eval z = 0 := by rw [(hQ t).2.2, eval_mul, hz, mul_zero]
      rcases hclass z hpz with hequal | hleft
      · have hequal' : z = (u t : ℂ) := hequal.trans (congrArg Complex.ofReal hvu)
        exact False.elim (hqu (hequal' ▸ hz))
      · exact hleft
    · intro ht
      refine ⟨hd, u t, hupos t, Q t, (hQ t).1, (hQ t).2.1, ?_, (hQ t).2.2⟩
      intro z hz
      exact ht z (Polynomial.isRoot_of_mem_roots hz)
  rw [heq]
  apply monic_fixed_degree_hurwitz_parameter_set_open Q (d-1)
    (fun t => (hQ t).1) (fun t => (hQ t).2.1)
  intro i _hi
  exact fixed_degree_linear_deflation_coeff_continuous P d hdegree hcoeff u hu i

/-- A connected family preserves the full one-positive-root configuration
once its continuous positive root, simplicity, uniqueness, and exclusion
of axis roots are proved. These inputs are explicit; no signed Routh
criterion is assumed. -/
theorem signed_factorization_of_connected_family
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (P : T → ℂ[X]) (d : ℕ) (hd : 1 ≤ d)
    (hmonic : ∀ t, (P t).Monic) (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (u : T → ℝ) (hu : Continuous u) (hupos : ∀ t, 0 < u t)
    (huroot : ∀ t, (P t).eval (u t : ℂ) = 0)
    (husimple : ∀ t, (P t).derivative.eval (u t : ℂ) ≠ 0)
    (huunique : ∀ t, ∀ v : ℝ, 0 < v → (P t).eval (v : ℂ) = 0 → v = u t)
    (haxis : ∀ t, ∀ z : ℂ, z.re = 0 → (P t).eval z ≠ 0)
    (t₀ : T) (h₀ : PositiveRealRootHurwitzFactorization d (P t₀)) :
    ∀ t, PositiveRealRootHurwitzFactorization d (P t) := by
  let S : Set T := {t | PositiveRealRootHurwitzFactorization d (P t)}
  have hopen : IsOpen S := signed_factorization_parameter_set_open
    P d hd hmonic hdegree hcoeff u hu hupos huroot husimple huunique
  have hclosed : IsClosed S := signed_factorization_parameter_set_closed
    P d hd hmonic hdegree hcoeff
      (fun t => ⟨u t, hupos t, huroot t, husimple t, huunique t⟩) haxis
  have hall : S = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, h₀⟩
  intro t
  have ht : t ∈ S := by rw [hall]; exact Set.mem_univ t
  exact ht

/-- A stable literal tail at a boundary parameter stays stable nearby
under continuous coefficients and continuous linear deflation. The
selected dividing root may be zero at the boundary. This supplies the
stable-tail part of the negative-constant seed without an assumed signed
criterion or continuously labeled complementary roots. -/
theorem linear_deflation_hurwitz_near
    {T : Type*} [TopologicalSpace T] (P : T → ℂ[X]) (d : ℕ)
    (hmonic : ∀ t, (P t).Monic) (hdegree : ∀ t, (P t).natDegree = d)
    (hcoeff : ∀ i ≤ d, Continuous (fun t => (P t).coeff i))
    (u : T → ℝ) (hu : Continuous u)
    (huroot : ∀ t, (P t).eval (u t : ℂ) = 0)
    (a : T) (ha : ∀ z : ℂ,
      ((P a) /ₘ (X-C (u a : ℂ))).eval z = 0 → z.re < 0) :
    ∀ᶠ t in 𝓝 a, ∀ z : ℂ,
      ((P t) /ₘ (X-C (u t : ℂ))).eval z = 0 → z.re < 0 := by
  let Q : T → ℂ[X] := fun t => (P t) /ₘ (X-C (u t : ℂ))
  have hQ (t : T) : (Q t).Monic ∧ (Q t).natDegree = d-1 ∧
      P t = (X-C (u t : ℂ))*(Q t) :=
    monic_linear_deflation_factorization (P t) (hmonic t) d (hdegree t) (u t) (huroot t)
  have hopen : IsOpen {t | ∀ z : ℂ, (Q t).eval z = 0 → z.re < 0} :=
    monic_fixed_degree_hurwitz_parameter_set_open Q (d-1)
      (fun t => (hQ t).1) (fun t => (hQ t).2.1)
      (fun i _hi => fixed_degree_linear_deflation_coeff_continuous P d hdegree hcoeff u hu i)
  exact hopen.mem_nhds ha

/-- A one-sided boundary seed only requires a limit of the positive root,
not a continuous extension on a two-sided parameter neighborhood. Finite
synthetic division transfers the coefficient and root limits to the tail,
and the explicit Hurwitz neighborhood preserves that tail. -/
theorem linear_deflation_hurwitz_eventually_of_tendsto
    {ι : Type*} (l : Filter ι) (P : ι → ℂ[X]) (p₀ : ℂ[X]) (d : ℕ)
    (hdegree : ∀ i, (P i).natDegree = d) (hdegree₀ : p₀.natDegree = d)
    (hcoeff : ∀ n ≤ d, Tendsto (fun i => (P i).coeff n) l (𝓝 (p₀.coeff n)))
    (u : ι → ℝ) (u₀ : ℝ) (hu : Tendsto u l (𝓝 u₀))
    (hmonic₀ : p₀.Monic) (hroot₀ : p₀.eval (u₀ : ℂ) = 0)
    (htail₀ : ∀ z : ℂ, (p₀ /ₘ (X-C (u₀ : ℂ))).eval z = 0 → z.re < 0) :
    ∀ᶠ i in l, ∀ z : ℂ,
      ((P i) /ₘ (X-C (u i : ℂ))).eval z = 0 → z.re < 0 := by
  classical
  let Q : ι → ℂ[X] := fun i => (P i) /ₘ (X-C (u i : ℂ))
  let q₀ := p₀ /ₘ (X-C (u₀ : ℂ))
  obtain ⟨hq₀, hqdegree₀, _hfactor₀⟩ :=
    monic_linear_deflation_factorization p₀ hmonic₀ d hdegree₀ u₀ hroot₀
  have hqcoeff (n : ℕ) : Tendsto (fun i => (Q i).coeff n) l (𝓝 (q₀.coeff n)) := by
    have hc : Tendsto (fun i => (u i : ℂ)) l (𝓝 (u₀ : ℂ)) :=
      (Complex.continuous_ofReal.tendsto u₀).comp hu
    have hsum : Tendsto
        (fun j => ∑ k ∈ Finset.Icc (n+1) d,
          (u j : ℂ)^(k-(n+1))*(P j).coeff k) l
        (𝓝 (∑ k ∈ Finset.Icc (n+1) d,
          (u₀ : ℂ)^(k-(n+1))*p₀.coeff k)) := by
      apply tendsto_finsetSum
      intro k hk
      exact (hc.pow _).mul (hcoeff k (Finset.mem_Icc.mp hk).2)
    simpa only [Q, q₀, coeff_divByMonic_X_sub_C, hdegree, hdegree₀] using hsum
  have hroots₀ : ∀ z ∈ q₀.roots, z.re < 0 := by
    intro z hz
    exact htail₀ z (Polynomial.isRoot_of_mem_roots hz)
  obtain ⟨ε, hε, hneighborhood⟩ :=
    monic_hurwitz_coefficient_neighborhood q₀ hq₀ hroots₀
  have hnear : ∀ᶠ j in l, ∀ n ∈ Finset.range (q₀.natDegree+1),
      ‖(Q j).coeff n-q₀.coeff n‖ ≤ ε := by
    apply (eventually_all_finset (Finset.range (q₀.natDegree+1))).mpr
    intro n _hn
    have hlim : Tendsto (fun j => ‖(Q j).coeff n-q₀.coeff n‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using
        ((hqcoeff n).sub (tendsto_const_nhds :
          Tendsto (fun _ : ι => q₀.coeff n) l (𝓝 (q₀.coeff n)))).norm
    exact (hlim.eventually (Iio_mem_nhds hε)).mono (fun _ hj => hj.le)
  filter_upwards [hnear] with j hj
  apply hneighborhood (Q j)
  · have hqdegree : q₀.natDegree = d-1 := hqdegree₀
    rw [hqdegree]
    simpa only [Q, natDegree_divByMonic (P j) (monic_X_sub_C (u j : ℂ)),
      natDegree_X_sub_C, hdegree j] using (le_rfl : d-1 ≤ d-1)
  · intro n hn
    exact hj n (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))

end
end PhosphorylationStableCapacity
