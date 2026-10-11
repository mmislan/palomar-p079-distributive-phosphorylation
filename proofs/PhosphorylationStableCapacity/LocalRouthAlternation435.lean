module
public import proofs.PhosphorylationStableCapacity.SaddleSpectrumOpenness435
public import proofs.PhosphorylationStableCapacity.DyadicEventuallySelection
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

namespace PhosphorylationStableCapacity

open Matrix Polynomial Filter
open scoped Topology

/-- Descending polynomial coefficient, with both negative and excessive
indices zero. The explicit degree is shared by every member of a family. -/
def routhDescendingCoeff {R : Type*} [Semiring R]
    (d : ℕ) (p : R[X]) (s : ℤ) : R :=
  if 0 ≤ s ∧ s ≤ (d : ℤ) then p.coeff (d-s.toNat) else 0

/-- The transpose of the conventional Hurwitz matrix. Transposition
preserves its determinant and makes the index formula convenient. -/
def routhHurwitzMatrix {R : Type*} [Semiring R]
    (d k : ℕ) (p : R[X]) : Matrix (Fin k) (Fin k) R :=
  fun i j => routhDescendingCoeff d p (2*(i.val : ℤ)-(j.val : ℤ)+1)

def routhHurwitzMinor {R : Type*} [CommRing R]
    (d k : ℕ) (p : R[X]) : R := (routhHurwitzMatrix d k p).det

/-- Exact rational arithmetic sufficient data for the local Routh
pattern: every proper Hurwitz minor is positive, and the last-column
sign is the prescribed sign of the characteristic constant. The generic
Routh spectral counting theorem is a separate soundness obligation. -/
def rationalLocalRouthAccepts (d : ℕ) (p : ℚ[X]) (odd : Bool) : Bool :=
  decide ((∀ k : Fin (d-1), 0 < routhHurwitzMinor d (k.val+1) p) ∧
    (if odd then p.coeff 0 < 0 else 0 < p.coeff 0))

noncomputable section

/-- Multiplication by X preserves descending coefficients when the
explicit degree increases by one, including the zero constant term. -/
theorem routhDescendingCoeff_X_mul {R : Type*} [Semiring R]
    (d : ℕ) (q : R[X]) (s : ℤ) :
    routhDescendingCoeff (d+1) (Polynomial.X*q) s =
      routhDescendingCoeff d q s := by
  unfold routhDescendingCoeff
  by_cases hs : 0 ≤ s ∧ s ≤ (d : ℤ)
  · have hs' : 0 ≤ s ∧ s ≤ ((d+1 : ℕ) : ℤ) := by omega
    rw [ite_eq_left hs', ite_eq_left hs]
    have hnat : s.toNat ≤ d := by omega
    rw [show d+1-s.toNat = (d-s.toNat)+1 by omega]
    exact Polynomial.coeff_X_mul q (d-s.toNat)
  · rw [ite_eq_right hs]
    split_ifs with hs'
    · have heq : s.toNat = d+1 := by omega
      simp [heq]
    · rfl

/-- All proper minors at a neutral point X*q are literally the minors
of q. This exact identity explains why the odd checker can be completed
locally without a general signed-inertia construction. -/
theorem routhHurwitzMinor_X_mul {R : Type*} [CommRing R]
    (d k : ℕ) (q : R[X]) :
    routhHurwitzMinor (d+1) k (Polynomial.X*q) =
      routhHurwitzMinor d k q := by
  unfold routhHurwitzMinor
  congr 1
  ext i j
  exact routhDescendingCoeff_X_mul d q _

/-- The final Hurwitz determinant is the characteristic constant times
its preceding determinant. This identifies the last Routh pivot exactly. -/
theorem routhHurwitzMinor_last {R : Type*} [CommRing R]
    (d : ℕ) (p : R[X]) :
    routhHurwitzMinor (d+1) (d+1) p =
      p.coeff 0 * routhHurwitzMinor (d+1) d p := by
  let H := routhHurwitzMatrix (d+1) (d+1) p
  have hrow (j : Fin d) : H (Fin.last d) j.castSucc = 0 := by
    dsimp [H, routhHurwitzMatrix, routhDescendingCoeff]
    rw [ite_eq_right (by omega)]
  have hlast : H (Fin.last d) (Fin.last d) = p.coeff 0 := by
    dsimp [H, routhHurwitzMatrix, routhDescendingCoeff]
    rw [ite_eq_left (by omega)]
    congr 1
    omega
  have hsub : H.submatrix (Fin.last d).succAbove (Fin.last d).succAbove =
      routhHurwitzMatrix (d+1) d p := by
    simp only [Fin.succAbove_last]
    ext i j
    rfl
  have hpow : (-1 : R)^(d+d) = 1 := by
    rw [show d+d = 2*d by omega, pow_mul]
    simp
  change H.det = _
  rw [Matrix.det_succ_row H (Fin.last d), Fin.sum_univ_castSucc]
  have hsum : (∑ j : Fin d, (-1 : R)^((Fin.last d).val+j.castSucc.val) *
      H (Fin.last d) j.castSucc *
        (H.submatrix (Fin.last d).succAbove j.castSucc.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hrow]
    simp
  rw [hsum, zero_add, hlast, hsub]
  simp [routhHurwitzMinor, hpow]

/-- Hurwitz minors commute with the exact rational embedding. -/
theorem routhHurwitzMinor_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d k : ℕ) (p : R[X]) :
    routhHurwitzMinor d k (p.map f) = f (routhHurwitzMinor d k p) := by
  unfold routhHurwitzMinor
  rw [RingHom.map_det]
  congr 1
  ext i j
  change routhDescendingCoeff d (p.map f) (2*(i.val : ℤ)-(j.val : ℤ)+1) =
    f (routhDescendingCoeff d p (2*(i.val : ℤ)-(j.val : ℤ)+1))
  unfold routhDescendingCoeff
  split_ifs <;> simp

/-- The rational Boolean test is exactly the real determinant/sign
predicate, with no floating point root calculation or unchecked cast. -/
theorem rationalLocalRouthAccepts_iff (d : ℕ) (p : ℚ[X]) (odd : Bool) :
    rationalLocalRouthAccepts d p odd = true ↔
      (∀ k : Fin (d-1),
        0 < routhHurwitzMinor d (k.val+1) (p.map (algebraMap ℚ ℝ))) ∧
      (if odd then (p.map (algebraMap ℚ ℝ)).coeff 0 < 0
        else 0 < (p.map (algebraMap ℚ ℝ)).coeff 0) := by
  simp only [rationalLocalRouthAccepts, decide_eq_true_eq,
    routhHurwitzMinor_map, Polynomial.coeff_map]
  cases odd <;> simp

theorem continuousAt_routhHurwitzMinor
    (d k : ℕ) (P : ℝ → ℝ[X])
    (hcoeff : ∀ n, ContinuousAt (fun δ => (P δ).coeff n) 0) :
    ContinuousAt (fun δ => routhHurwitzMinor d k (P δ)) 0 := by
  have hH : ContinuousAt (fun δ => routhHurwitzMatrix d k (P δ)) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    dsimp [routhHurwitzMatrix, routhDescendingCoeff]
    split_ifs
    · exact hcoeff _
    · exact continuousAt_const
  exact continuous_id.matrix_det.continuousAt.comp hH

/-- Proper-minor positivity of the coalesced deflation propagates to
all sufficiently small distances, simultaneously over the finite family.
Together with the already-proved characteristic-constant alternation,
this supplies the local arithmetic part of every odd/even Routh test. -/
theorem properRouthMinors_eventually_positive
    {ι : Type*} [Fintype ι]
    (d : ℕ) (P : ι → ℝ → ℝ[X]) (q : ℝ[X])
    (hzero : ∀ j, P j 0 = Polynomial.X*q)
    (hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0)
    (hq : ∀ k : Fin d, 0 < routhHurwitzMinor d (k.val+1) q) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ j : ι, ∀ k : Fin d,
        0 < routhHurwitzMinor (d+1) (k.val+1) (P j δ) := by
  apply Filter.eventually_all.mpr
  intro j
  apply Filter.eventually_all.mpr
  intro k
  have hpositive : 0 < routhHurwitzMinor (d+1) (k.val+1) (P j 0) := by
    rw [hzero, routhHurwitzMinor_X_mul]
    exact hq k
  exact (continuousAt_routhHurwitzMinor (d+1) (k.val+1)
    (P j) (hcoeff j)).eventually (Ioi_mem_nhds hpositive)

/-- For the fixed-degree real characteristic polynomials, the local
minor test accepts the alternating sign pattern after finitely many
halvings. This theorem concerns exactly the scalar acceptance predicate;
it does not substitute an existential Euler search for a Routh loop. -/
theorem localRouthPattern_has_halving_index
    {ι : Type*} [Fintype ι]
    (d : ℕ) (P : ι → ℝ → ℝ[X]) (q : ℝ[X])
    (odd : ι → Bool)
    (hzero : ∀ j, P j 0 = Polynomial.X*q)
    (hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0)
    (hq : ∀ k : Fin d, 0 < routhHurwitzMinor d (k.val+1) q)
    (hsign : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, if odd j then (P j δ).coeff 0 < 0 else 0 < (P j δ).coeff 0) :
    ∃ b : ℕ, ∀ j : ι,
      (∀ k : Fin d,
        0 < routhHurwitzMinor (d+1) (k.val+1) (P j ((1/2 : ℝ)^b))) ∧
      (if odd j then (P j ((1/2 : ℝ)^b)).coeff 0 < 0
        else 0 < (P j ((1/2 : ℝ)^b)).coeff 0) := by
  have hproper : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j : ι, ∀ k : Fin d,
        0 < routhHurwitzMinor (d+1) (k.val+1) (P j δ) :=
    (properRouthMinors_eventually_positive d P q hzero hcoeff hq).filter_mono
      (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi (0 : ℝ)))
  obtain ⟨b, hminors, hsigns⟩ := eventually_right_has_halving_index _
    (hproper.and hsign)
  exact ⟨b, fun j => ⟨hminors j, hsigns j⟩⟩

/-- The local determinant argument yields an accepted finite rational
Routh test for every state, at one common halving index. The cast identity
pins those tests to the original real characteristic polynomials. -/
theorem rationalLocalRouthFamily_has_halving_index
    {ι : Type*} [Fintype ι]
    (d : ℕ) (P : ι → ℝ → ℝ[X]) (Q : ι → ℚ → ℚ[X])
    (q : ℝ[X]) (odd : ι → Bool)
    (hcast : ∀ j b,
      (Q j ((1/2 : ℚ)^b)).map (algebraMap ℚ ℝ) = P j ((1/2 : ℝ)^b))
    (hzero : ∀ j, P j 0 = Polynomial.X*q)
    (hcoeff : ∀ j n, ContinuousAt (fun δ => (P j δ).coeff n) 0)
    (hq : ∀ k : Fin d, 0 < routhHurwitzMinor d (k.val+1) q)
    (hsign : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, if odd j then (P j δ).coeff 0 < 0 else 0 < (P j δ).coeff 0) :
    ∃ b : ℕ, ∀ j : ι,
      rationalLocalRouthAccepts (d+1) (Q j ((1/2 : ℚ)^b)) (odd j) = true := by
  obtain ⟨b, hb⟩ := localRouthPattern_has_halving_index
    d P q odd hzero hcoeff hq hsign
  refine ⟨b, ?_⟩
  intro j
  rw [rationalLocalRouthAccepts_iff, hcast]
  simpa using hb j

end
end PhosphorylationStableCapacity
