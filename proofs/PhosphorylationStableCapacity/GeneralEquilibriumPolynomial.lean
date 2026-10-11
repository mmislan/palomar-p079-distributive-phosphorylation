module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumElimination

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- The three universal inventory polynomials; their coefficients are
defined by the literal positive-rate equilibrium recurrence. -/
def freeSubstratePoly {n : ℕ} (k : Rates n) : ℝ[X] :=
  ∑ j : Fin (n+1), C (equilibriumWeight k j.val) * X^j.val

def kinaseComplexPoly {n : ℕ} (k : Rates n) : ℝ[X] :=
  ∑ i : Fin n, C (kinaseBindingRatio k i * equilibriumWeight k i.val) *
    X^(i.val+1)

def phosphataseComplexPoly {n : ℕ} (k : Rates n) : ℝ[X] :=
  ∑ i : Fin n, C (phosphataseBindingRatio k i *
    equilibriumWeight k (i.val+1)) * X^(i.val+1)

theorem freeSubstratePoly_eval {n : ℕ} (k : Rates n) (u : ℝ) :
    (freeSubstratePoly k).eval u = freeSubstrateInventory k u := by
  simp only [freeSubstratePoly, freeSubstrateInventory, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X]

theorem kinaseComplexPoly_eval {n : ℕ} (k : Rates n) (u : ℝ) :
    (kinaseComplexPoly k).eval u = kinaseComplexInventory k u := by
  simp only [kinaseComplexPoly, kinaseComplexInventory, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X]

theorem phosphataseComplexPoly_eval {n : ℕ} (k : Rates n) (u : ℝ) :
    (phosphataseComplexPoly k).eval u =
      phosphataseComplexInventory k u := by
  simp only [phosphataseComplexPoly, phosphataseComplexInventory,
    eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem freeSubstratePoly_natDegree_le {n : ℕ} (k : Rates n) :
    (freeSubstratePoly k).natDegree ≤ n := by
  unfold freeSubstratePoly
  apply natDegree_sum_le_of_forall_le
  intro j _
  have h := natDegree_C_mul_X_pow_le
    (equilibriumWeight k j.val) j.val
  omega

theorem kinaseComplexPoly_natDegree_le {n : ℕ} (k : Rates n) :
    (kinaseComplexPoly k).natDegree ≤ n := by
  unfold kinaseComplexPoly
  apply natDegree_sum_le_of_forall_le
  intro i _
  have h := natDegree_C_mul_X_pow_le
    (kinaseBindingRatio k i * equilibriumWeight k i.val) (i.val+1)
  omega

theorem phosphataseComplexPoly_natDegree_le {n : ℕ} (k : Rates n) :
    (phosphataseComplexPoly k).natDegree ≤ n := by
  unfold phosphataseComplexPoly
  apply natDegree_sum_le_of_forall_le
  intro i _
  have h := natDegree_C_mul_X_pow_le
    (phosphataseBindingRatio k i *
      equilibriumWeight k (i.val+1)) (i.val+1)
  omega

/-- Exact polynomial form of the arbitrary-rate elimination residual. -/
def equilibriumEliminationPoly {n : ℕ}
    (k : Rates n) (ET FT ST : ℝ) : ℝ[X] :=
  let T := freeSubstratePoly k
  let B := kinaseComplexPoly k
  let D := phosphataseComplexPoly k
  let A := C ET-C FT*X
  let Q := C FT*B-C ET*D
  C ST*Q*(Q+A*D)-A*T*(Q+A*D)-C FT*A*(B+D)*Q

theorem equilibriumEliminationPoly_eval {n : ℕ}
    (k : Rates n) (ET FT ST u : ℝ) :
    (equilibriumEliminationPoly k ET FT ST).eval u =
      equilibriumEliminationResidual k ET FT ST u := by
  simp [equilibriumEliminationPoly, equilibriumEliminationResidual,
    freeSubstratePoly_eval, kinaseComplexPoly_eval,
    phosphataseComplexPoly_eval]

set_option maxHeartbeats 1000000
/-- Universal degree bound for the literal arbitrary-rate eliminant.
The common zero at `u=0` and an additional negative root will leave
at most `2n` positive roots. -/
theorem equilibriumEliminationPoly_natDegree_le {n : ℕ}
    (k : Rates n) (ET FT ST : ℝ) :
    (equilibriumEliminationPoly k ET FT ST).natDegree ≤ 2*n+2 := by
  let T := freeSubstratePoly k
  let B := kinaseComplexPoly k
  let D := phosphataseComplexPoly k
  let A : ℝ[X] := C ET-C FT*X
  let Q : ℝ[X] := C FT*B-C ET*D
  let R : ℝ[X] := Q+A*D
  have hT : T.natDegree ≤ n := freeSubstratePoly_natDegree_le k
  have hB : B.natDegree ≤ n := kinaseComplexPoly_natDegree_le k
  have hD : D.natDegree ≤ n := phosphataseComplexPoly_natDegree_le k
  have hA : A.natDegree ≤ 1 := by
    dsimp [A]
    apply (natDegree_sub_le (C ET) (C FT*X)).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le FT X).trans (by simp)
  have hQ : Q.natDegree ≤ n := by
    dsimp [Q]
    apply (natDegree_sub_le (C FT*B) (C ET*D)).trans
    exact max_le ((natDegree_C_mul_le FT B).trans hB)
      ((natDegree_C_mul_le ET D).trans hD)
  have hR : R.natDegree ≤ n+1 := by
    dsimp [R]
    apply (natDegree_add_le Q (A*D)).trans
    exact max_le (by omega)
      ((natDegree_mul_le_of_le hA hD).trans (by omega))
  have hBD : (B+D).natDegree ≤ n :=
    natDegree_add_le_of_degree_le hB hD
  have hterm1 : (C ST*Q*R).natDegree ≤ 2*n+2 := by
    calc
      _ ≤ (C ST*Q).natDegree+R.natDegree := natDegree_mul_le
      _ ≤ Q.natDegree+R.natDegree :=
        add_le_add (natDegree_C_mul_le ST Q) le_rfl
      _ ≤ n+(n+1) := add_le_add hQ hR
      _ ≤ 2*n+2 := by omega
  have hterm2 : (A*T*R).natDegree ≤ 2*n+2 := by
    calc
      _ ≤ (A*T).natDegree+R.natDegree := natDegree_mul_le
      _ ≤ (A.natDegree+T.natDegree)+R.natDegree :=
        add_le_add (natDegree_mul_le (p := A) (q := T)) le_rfl
      _ ≤ (1+n)+(n+1) := add_le_add (add_le_add hA hT) hR
      _ ≤ 2*n+2 := by omega
  have hterm3 : (C FT*A*(B+D)*Q).natDegree ≤ 2*n+2 := by
    calc
      _ ≤ (C FT*A*(B+D)).natDegree+Q.natDegree := natDegree_mul_le
      _ ≤ ((C FT*A).natDegree+(B+D).natDegree)+Q.natDegree :=
        add_le_add
          (natDegree_mul_le (p := C FT*A) (q := B+D)) le_rfl
      _ ≤ (A.natDegree+(B+D).natDegree)+Q.natDegree :=
        add_le_add
          (add_le_add (natDegree_C_mul_le FT A) le_rfl) le_rfl
      _ ≤ (1+n)+n := add_le_add (add_le_add hA hBD) hQ
      _ ≤ 2*n+2 := by omega
  change (C ST*Q*R-A*T*R-C FT*A*(B+D)*Q).natDegree ≤ 2*n+2
  exact (natDegree_sub_le_of_le
    (natDegree_sub_le_of_le hterm1 hterm2) hterm3).trans (by omega)

theorem positive_equilibrium_poly_root {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    (equilibriumEliminationPoly k
      (totalE x) (totalF x) (totalS x)).eval (x.E/x.F) = 0 := by
  rw [equilibriumEliminationPoly_eval]
  exact equilibrium_elimination_residual_zero k x hk hx heq

theorem kinaseComplexInventory_zero {n : ℕ} (k : Rates n) :
    kinaseComplexInventory k 0 = 0 := by
  simp [kinaseComplexInventory, pow_succ]

theorem phosphataseComplexInventory_zero {n : ℕ} (k : Rates n) :
    phosphataseComplexInventory k 0 = 0 := by
  simp [phosphataseComplexInventory, pow_succ]

/-- The raw eliminant always has the expected extraneous zero at
enzyme ratio zero. Positive equilibria have strictly positive ratio. -/
theorem equilibriumEliminationPoly_zero_root {n : ℕ}
    (k : Rates n) (ET FT ST : ℝ) :
    (equilibriumEliminationPoly k ET FT ST).eval 0 = 0 := by
  rw [equilibriumEliminationPoly_eval]
  simp [equilibriumEliminationResidual, kinaseComplexInventory_zero,
    phosphataseComplexInventory_zero]

end
end PhosphorylationStableCapacity
