module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPair
public import proofs.PhosphorylationStableCapacity.SplitConversionResidual

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

def arbitrarySplitRawD (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  rawD (arbitrarySplitPair m ξ δ).1 (arbitrarySplitPair m ξ δ).2 r

def arbitrarySplitRawB (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  rawB (arbitrarySplitPair m ξ δ).1 (arbitrarySplitPair m ξ δ).2 r

def arbitrarySplitConversionResidual (m : ℕ) (ξ : ℕ → ℝ)
    (r δ x : ℝ) : ℝ :=
  (x-1)*((arbitrarySplitRawB m ξ r δ).eval (ratio x)-
    r*(arbitrarySplitRawD m ξ r δ).eval (ratio x)) -
    2*(r-ratio x)*(arbitrarySplitRawD m ξ r δ).eval (ratio x)

/-- Every root uses the same positive limiting conversion multiplier. -/
theorem arbitrarySplitConversionPrefactor_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    4*r*(arbitrarySplitPair m ξ 0).1.eval r+
      (offsetSplitRoot ξ 0 j-1)*(arbitrarySplitPair m ξ 0).2.eval r =
    4*r*(coalescedPair m).1.eval r+
      2*(coalescedPair m).2.eval r := by
  norm_num [arbitrarySplitPair_zero_eq_coalesced, offsetSplitRoot]

theorem arbitrarySplitConversionPrefactor_zero_pos
    (m : ℕ) (r : ℝ) (hr : 0 < r) :
    0 < 4*r*(coalescedPair m).1.eval r+
      2*(coalescedPair m).2.eval r := by
  have hp := (coalescedPair_dense m).1.eval_pos hr
  have hq := (coalescedPair_dense m).2.eval_pos hr
  positivity

/-- The converted source residual retains the full arbitrary-root
product, with an explicit coefficient-dependent multiplier. -/
theorem arbitrarySplitConversionResidual_factor
    (m : ℕ) (ξ : ℕ → ℝ) (r δ x : ℝ) :
    arbitrarySplitConversionResidual m ξ r δ x =
      (4*r*(arbitrarySplitPair m ξ δ).1.eval r+
        (x-1)*(arbitrarySplitPair m ξ δ).2.eval r) *
          arbitrarySplitScalarProduct m ξ δ x := by
  unfold arbitrarySplitConversionResidual arbitrarySplitRawB arbitrarySplitRawD
  rw [conversion_residual_factor, arbitrarySplitPair_scalar_identity]

/-- At each prescribed root, the exact scalar slope has the paper's
`δ^(2n-2)` root-gap factor. The remaining multiplier still has to be
transported through the literal class-Jacobian determinant. -/
theorem arbitrarySplitConversionResidual_deriv_at_root
    (m j : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (hj : j < 2*m+1) :
    deriv (fun x => arbitrarySplitConversionResidual m ξ r δ x)
      (offsetSplitRoot ξ δ j) =
    (4*r*(arbitrarySplitPair m ξ δ).1.eval r+
      (offsetSplitRoot ξ δ j-1)*(arbitrarySplitPair m ξ δ).2.eval r) *
        (δ^(2*m) *
          ∏ i ∈ (Finset.range (2*m+1)).erase j, (ξ j-ξ i)) := by
  let f : ℝ → ℝ := fun x =>
    4*r*(arbitrarySplitPair m ξ δ).1.eval r+
      (x-1)*(arbitrarySplitPair m ξ δ).2.eval r
  let g : ℝ → ℝ := fun x => arbitrarySplitScalarProduct m ξ δ x
  have heq : (fun x => arbitrarySplitConversionResidual m ξ r δ x) =
      f * g := by
    funext x
    exact arbitrarySplitConversionResidual_factor m ξ r δ x
  have hz : g (offsetSplitRoot ξ δ j) = 0 := by
    dsimp [g]
    rw [arbitrarySplitScalarProduct_eq_prod_range]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
    simp
  have hdf : DifferentiableAt ℝ f (offsetSplitRoot ξ δ j) := by
    dsimp [f]
    fun_prop
  have hdg : DifferentiableAt ℝ g (offsetSplitRoot ξ δ j) := by
    have hprod : g = fun x =>
        ∏ i ∈ Finset.range (2*m+1),
          (x-offsetSplitRoot ξ δ i) := by
      funext x
      exact arbitrarySplitScalarProduct_eq_prod_range m ξ δ x
    rw [hprod]
    fun_prop
  rw [heq, deriv_mul hdf hdg, hz,
    arbitrarySplitScalarProduct_deriv_at_root m j ξ δ hj]
  simp [f]

end
end PhosphorylationStableCapacity
