module
public import proofs.PhosphorylationStableCapacity.FastBindingDissipation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Binding affinities depend linearly on the complex perturbation at a fixed
positive state. -/
def fastAffinityLinear (n : ℕ) (x : State n) :
    FastSpace n →ₗ[ℝ] FastSpace n where
  toFun v := (fastAffinityC x v, fastAffinityD x v)
  map_add' := by
    intro v w
    apply Prod.ext
    · funext i
      simp [fastAffinityC, boundComplexAt_add, Finset.sum_add_distrib]
      ring
    · funext i
      simp [fastAffinityD, boundComplexAt_add, Finset.sum_add_distrib]
      ring
  map_smul' := by
    intro a v
    apply Prod.ext
    · funext i
      simp [fastAffinityC, boundComplexAt_smul, smul_eq_mul,
        ← Finset.mul_sum]
      ring
    · funext i
      simp [fastAffinityD, boundComplexAt_smul, smul_eq_mul,
        ← Finset.mul_sum]
      ring

/-- The abstract fast binding operator as a linear endomorphism. -/
def fastBindingEnd (n : ℕ) (x : State n) (ρ σ : Fin n → ℝ) :
    FastSpace n →ₗ[ℝ] FastSpace n where
  toFun := fastBindingLinear x ρ σ
  map_add' := by
    intro v w
    apply Prod.ext
    · funext i
      have h := congrArg (fun y : FastSpace n => y.1 i)
        ((fastAffinityLinear n x).map_add v w)
      simp only [fastAffinityLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Prod.fst_add, Pi.add_apply] at h
      simp [fastBindingLinear, h]
      ring
    · funext i
      have h := congrArg (fun y : FastSpace n => y.2 i)
        ((fastAffinityLinear n x).map_add v w)
      simp only [fastAffinityLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Prod.snd_add, Pi.add_apply] at h
      simp [fastBindingLinear, h]
      ring
  map_smul' := by
    intro a v
    apply Prod.ext
    · funext i
      have h := congrArg (fun y : FastSpace n => y.1 i)
        ((fastAffinityLinear n x).map_smul a v)
      simp only [fastAffinityLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Prod.smul_fst, Pi.smul_apply, smul_eq_mul] at h
      simp [fastBindingLinear, h, smul_eq_mul]
      ring

    · funext i
      have h := congrArg (fun y : FastSpace n => y.2 i)
        ((fastAffinityLinear n x).map_smul a v)
      simp only [fastAffinityLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Prod.smul_snd, Pi.smul_apply, smul_eq_mul] at h
      simp [fastBindingLinear, h, smul_eq_mul]
      ring

theorem fastBindingEnd_injective {n : ℕ} (x : State n)
    (hx : x.Positive) (ρ σ : Fin n → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hσ : ∀ i, 0 < σ i) :
    Function.Injective (fastBindingEnd n x ρ σ) := by
  intro v w h
  have hzero : fastBindingEnd n x ρ σ (v - w) = 0 := by
    rw [map_sub, h, sub_self]
  have hfast : fastBindingLinear x ρ σ (v - w) = 0 := hzero
  exact sub_eq_zero.mp
    (fastBindingLinear_kernel_zero x hx ρ σ hρ hσ (v - w) hfast)

end
end PhosphorylationStableCapacity
