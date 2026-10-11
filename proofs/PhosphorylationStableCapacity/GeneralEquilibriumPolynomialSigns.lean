module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumPolynomial

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- The highest substrate coefficient is the positive accumulated
adjacent-level rate factor. -/
theorem freeSubstratePoly_top_coeff {n : ℕ} (k : Rates n) :
    (freeSubstratePoly k).coeff n = equilibriumWeight k n := by
  unfold freeSubstratePoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  let j : Fin (n+1) := ⟨n, Nat.lt_succ_self n⟩
  rw [Finset.sum_eq_single j]
  · simp [j]
  · intro i _ hi
    have hne : n ≠ i.val := by
      intro hval
      apply hi
      exact Fin.ext hval.symm
    simp [hne]
  · simp [j]

/-- The highest phosphatase-complex coefficient is positive for every
nonempty chain with positive rates. -/
theorem phosphataseComplexPoly_top_coeff {n : ℕ}
    (k : Rates n) (hn : 0 < n) :
    (phosphataseComplexPoly k).coeff n =
      phosphataseBindingRatio k ⟨n-1, by omega⟩ *
        equilibriumWeight k n := by
  unfold phosphataseComplexPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  let i : Fin n := ⟨n-1, by omega⟩
  rw [Finset.sum_eq_single i]
  · simp [i, Nat.sub_add_cancel hn]
  · intro j _ hji
    have hne : n ≠ j.val+1 := by
      intro hval
      apply hji
      apply Fin.ext
      dsimp [i]
      omega
    simp [hne]
  · simp [i]

theorem freeSubstratePoly_top_coeff_pos {n : ℕ}
    (k : Rates n) (hk : k.Positive) :
    0 < (freeSubstratePoly k).coeff n := by
  rw [freeSubstratePoly_top_coeff]
  exact equilibriumWeight_pos k hk n

theorem phosphataseComplexPoly_top_coeff_pos {n : ℕ}
    (k : Rates n) (hn : 0 < n) (hk : k.Positive) :
    0 < (phosphataseComplexPoly k).coeff n := by
  rw [phosphataseComplexPoly_top_coeff k hn]
  exact mul_pos (phosphataseBindingRatio_pos k hk _)
    (equilibriumWeight_pos k hk n)

set_option maxHeartbeats 1000000

/-- The highest eliminant coefficient is strictly negative. This is
the uniform algebraic sign at negative infinity, independent of all
lower coefficients and of the substrate total. -/
theorem equilibriumEliminationPoly_top_coeff {n : ℕ}
    (k : Rates n) (ET FT ST : ℝ) :
    (equilibriumEliminationPoly k ET FT ST).coeff (2*n+2) =
      -(FT*FT*(freeSubstratePoly k).coeff n*
        (phosphataseComplexPoly k).coeff n) := by
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
    exact max_le (by simp) ((natDegree_C_mul_le FT X).trans (by simp))
  have hAcoeff : A.coeff 1 = -FT := by
    dsimp [A]
    simp
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
  have hRcoeff : R.coeff (n+1) = -FT*D.coeff n := by
    have hQzero : Q.coeff (n+1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    have hAD := coeff_mul_add_eq_of_natDegree_le hA hD
    dsimp [R]
    rw [coeff_add, hQzero]
    rw [show n+1 = 1+n by omega, hAD, hAcoeff]
    ring
  have hAT : (A*T).natDegree ≤ n+1 :=
    (natDegree_mul_le_of_le hA hT).trans (by omega)
  have hATcoeff : (A*T).coeff (n+1) =
      -FT*T.coeff n := by
    have h := coeff_mul_add_eq_of_natDegree_le hA hT
    rw [show n+1 = 1+n by omega, h, hAcoeff]
  have hterm1 : (C ST*Q*R).natDegree ≤ 2*n+1 := by
    calc
      _ ≤ (C ST*Q).natDegree+R.natDegree := natDegree_mul_le
      _ ≤ Q.natDegree+R.natDegree :=
        add_le_add (natDegree_C_mul_le ST Q) le_rfl
      _ ≤ n+(n+1) := add_le_add hQ hR
      _ ≤ 2*n+1 := by omega
  have hBD : (B+D).natDegree ≤ n :=
    natDegree_add_le_of_degree_le hB hD
  have hterm3 : (C FT*A*(B+D)*Q).natDegree ≤ 2*n+1 := by
    calc
      _ ≤ (C FT*A*(B+D)).natDegree+Q.natDegree := natDegree_mul_le
      _ ≤ ((C FT*A).natDegree+(B+D).natDegree)+Q.natDegree :=
        add_le_add
          (natDegree_mul_le (p := C FT*A) (q := B+D)) le_rfl
      _ ≤ (A.natDegree+(B+D).natDegree)+Q.natDegree :=
        add_le_add
          (add_le_add (natDegree_C_mul_le FT A) le_rfl) le_rfl
      _ ≤ (1+n)+n := add_le_add (add_le_add hA hBD) hQ
      _ ≤ 2*n+1 := by omega
  have hterm1zero : (C ST*Q*R).coeff (2*n+2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hterm3zero : (C FT*A*(B+D)*Q).coeff (2*n+2) = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hterm2coeff : (A*T*R).coeff (2*n+2) =
      FT*FT*T.coeff n*D.coeff n := by
    have h := coeff_mul_add_eq_of_natDegree_le hAT hR
    rw [show 2*n+2 = (n+1)+(n+1) by omega,
      h, hATcoeff, hRcoeff]
    ring
  change (C ST*Q*R-A*T*R-C FT*A*(B+D)*Q).coeff (2*n+2) =
    -(FT*FT*T.coeff n*D.coeff n)
  rw [coeff_sub, coeff_sub, hterm1zero, hterm2coeff,
    hterm3zero]
  ring

theorem equilibriumEliminationPoly_top_coeff_neg {n : ℕ}
    (k : Rates n) (hn : 0 < n) (hk : k.Positive)
    (ET FT ST : ℝ) (hFT : 0 < FT) :
    (equilibriumEliminationPoly k ET FT ST).coeff (2*n+2) < 0 := by
  rw [equilibriumEliminationPoly_top_coeff]
  exact neg_lt_zero.mpr
    (mul_pos (mul_pos (mul_pos hFT hFT)
      (freeSubstratePoly_top_coeff_pos k hk))
      (phosphataseComplexPoly_top_coeff_pos k hn hk))

/-- The lowest nonzero kinase-complex coefficient is positive. -/
theorem kinaseComplexPoly_coeff_one {n : ℕ}
    (k : Rates n) (hn : 0 < n) :
    (kinaseComplexPoly k).coeff 1 =
      kinaseBindingRatio k ⟨0, hn⟩ := by
  unfold kinaseComplexPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  let i : Fin n := ⟨0, hn⟩
  rw [Finset.sum_eq_single i]
  · simp [i, equilibriumWeight]
  · intro j _ hji
    have hjval : j.val ≠ 0 := by
      intro hval
      apply hji
      apply Fin.ext
      dsimp [i]
      exact hval
    simp [hjval]
  · simp [i]

theorem kinaseComplexPoly_coeff_zero {n : ℕ} (k : Rates n) :
    (kinaseComplexPoly k).coeff 0 = 0 := by
  unfold kinaseComplexPoly
  simp [finsetSum_coeff]

theorem phosphataseComplexPoly_coeff_zero {n : ℕ} (k : Rates n) :
    (phosphataseComplexPoly k).coeff 0 = 0 := by
  unfold phosphataseComplexPoly
  simp [finsetSum_coeff]

theorem freeSubstratePoly_coeff_zero {n : ℕ} (k : Rates n) :
    (freeSubstratePoly k).coeff 0 = 1 := by
  unfold freeSubstratePoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  let j : Fin (n+1) := ⟨0, Nat.succ_pos n⟩
  rw [Finset.sum_eq_single j]
  · simp [j, equilibriumWeight]
  · intro i _ hji
    have hne : 0 ≠ i.val := by
      intro hval
      apply hji
      exact Fin.ext hval.symm
    simp [hne]
  · simp [j]

end
end PhosphorylationStableCapacity
