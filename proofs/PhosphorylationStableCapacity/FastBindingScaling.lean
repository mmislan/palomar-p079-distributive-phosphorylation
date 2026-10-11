module
public import proofs.PhosphorylationStableCapacity.FastBindingFieldAffinity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem fastEmbed_smul {n : ℕ} (t : ℝ) (v : FastSpace n) :
    fastEmbed (t • v) = t • fastEmbed v := by
  apply Prod.ext
  · simp [fastEmbed]
  · rfl

theorem fastDeltaS_smul {n : ℕ} (t : ℝ) (v : FastSpace n)
    (j : Fin (n + 1)) :
    fastDeltaS (t • v) j = t * fastDeltaS v j := by
  simp [fastDeltaS, boundComplexAt_smul, smul_eq_mul]

theorem fastDeltaE_smul {n : ℕ} (t : ℝ) (v : FastSpace n) :
    fastDeltaE (t • v) = t * fastDeltaE v := by
  simp [fastDeltaE, smul_eq_mul, ← Finset.mul_sum]

theorem fastDeltaF_smul {n : ℕ} (t : ℝ) (v : FastSpace n) :
    fastDeltaF (t • v) = t * fastDeltaF v := by
  simp [fastDeltaF, smul_eq_mul, ← Finset.mul_sum]

theorem fastAffinityC_smul {n : ℕ} (x : State n) (t : ℝ)
    (v : FastSpace n) (i : Fin n) :
    fastAffinityC x (t • v) i = t * fastAffinityC x v i := by
  rw [fastAffinityC_eq_delta, fastAffinityC_eq_delta,
    fastDeltaS_smul, fastDeltaE_smul]
  simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
  ring

theorem fastAffinityD_smul {n : ℕ} (x : State n) (t : ℝ)
    (v : FastSpace n) (i : Fin n) :
    fastAffinityD x (t • v) i = t * fastAffinityD x v i := by
  rw [fastAffinityD_eq_delta, fastAffinityD_eq_delta,
    fastDeltaS_smul, fastDeltaF_smul]
  simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  ring

end
end PhosphorylationStableCapacity
