module
public import proofs.PhosphorylationStableCapacity.RateSelectedPositiveNeighborhood

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Matrix

noncomputable section

/-- The explicit inverse response is linear in the requested class
velocity at every fixed literal state. -/
def selectedRateRightInverseLinear {n : ℕ} (x : State n) :
    CoordinateSpace n →ₗ[ℝ] CoordinateSpace n where
  toFun := selectedRateRightInverse x
  map_add' y z := by
    apply Prod.ext
    · funext i
      simp only [selectedRateRightInverse, Prod.fst_add,
        Prod.snd_add, Pi.add_apply, Matrix.mulVec_add]
      ring
    · apply Prod.ext
      · funext i
        simp only [selectedRateRightInverse, Prod.fst_add,
          Prod.snd_add, Pi.add_apply, Matrix.mulVec_add]
        ring
      · funext i
        simp only [selectedRateRightInverse, Prod.fst_add,
          Prod.snd_add, Pi.add_apply]
        ring
  map_smul' t y := by
    apply Prod.ext
    · funext i
      simp only [selectedRateRightInverse, Prod.smul_fst,
        Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        Matrix.mulVec_smul, RingHom.id_apply]
      ring_nf
    · apply Prod.ext
      · funext i
        simp only [selectedRateRightInverse, Prod.smul_fst,
          Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          Matrix.mulVec_smul, RingHom.id_apply]
        ring_nf
      · funext i
        simp only [selectedRateRightInverse, Prod.smul_fst,
          Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring_nf

theorem selectedRateRightInverseLinear_bijective {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    Function.Bijective
      (selectedRateRightInverseLinear (stateFromLoaded ET FT ST u)) := by
  let B := selectedRateRightInverseLinear (stateFromLoaded ET FT ST u)
  let A : CoordinateSpace n → CoordinateSpace n :=
    fun v => loadedRestrictedField ET FT ST (selectedRates v) u
  have hright (y : CoordinateSpace n) : A (B y) = y := by
    exact selectedRates_response_right_inverse ET FT ST u y hx
  have hinjA : Function.Injective A :=
    selectedRates_response_injective ET FT ST u hx
  constructor
  · intro y z h
    calc
      y = A (B y) := (hright y).symm
      _ = A (B z) := congrArg A h
      _ = z := hright z
  · intro v
    refine ⟨A v, ?_⟩
    apply hinjA
    exact hright (A v)

/-- The selected-rate response is a linear equivalence at a positive
state, with an explicit inverse used by the cancellation graph. -/
def selectedRateRightInverseEquiv {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    CoordinateSpace n ≃ₗ[ℝ] CoordinateSpace n :=
  LinearEquiv.ofBijective
    (selectedRateRightInverseLinear (stateFromLoaded ET FT ST u))
    (selectedRateRightInverseLinear_bijective ET FT ST u hx)

theorem selectedRateRightInverse_response {n : ℕ}
    (ET FT ST : ℝ) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    selectedRateRightInverse (stateFromLoaded ET FT ST u)
      (loadedRestrictedField ET FT ST (selectedRates v) u) = v := by
  apply selectedRates_response_injective ET FT ST u hx
  exact selectedRates_response_right_inverse ET FT ST u
    (loadedRestrictedField ET FT ST (selectedRates v) u) hx

end
end PhosphorylationStableCapacity
