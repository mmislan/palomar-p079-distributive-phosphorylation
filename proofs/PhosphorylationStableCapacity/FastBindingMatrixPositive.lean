module
public import proofs.PhosphorylationStableCapacity.FastBindingSelfAdjoint
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Matrix

theorem fastBasis_repr_inl {n : ℕ} (v : FastSpace n) (i : Fin n) :
    (fastBasis n).repr v (Sum.inl i) = v.1 i := by
  simp [fastBasis]

theorem fastBasis_repr_inr {n : ℕ} (v : FastSpace n) (i : Fin n) :
    (fastBasis n).repr v (Sum.inr i) = v.2 i := by
  simp [fastBasis]

/-- The matrix quadratic pairing is the literal affinity pairing. -/
theorem fastAffinityMatrix_pairing {n : ℕ} (x : State n)
    (v w : FastSpace n) :
    (fastBasis n).repr v ⬝ᵥ
        (fastAffinityMatrix n x *ᵥ (fastBasis n).repr w) =
      (∑ i, v.1 i * fastAffinityC x w i) +
        (∑ i, v.2 i * fastAffinityD x w i) := by
  rw [fastAffinityMatrix, LinearMap.toMatrix_mulVec_repr]
  simp only [dotProduct, Fintype.sum_sum_type]
  simp [fastBasis_repr_inl, fastBasis_repr_inr, fastAffinityLinear]

theorem fastAffinityMatrix_pairing_symmetric {n : ℕ} (x : State n)
    (u v : Fin n ⊕ Fin n → ℝ) :
    u ⬝ᵥ (fastAffinityMatrix n x *ᵥ v) =
      v ⬝ᵥ (fastAffinityMatrix n x *ᵥ u) := by
  let a := (fastBasis n).equivFun.symm u
  let b := (fastBasis n).equivFun.symm v
  have ha : (fastBasis n).repr a = u := by
    simpa only [← Module.Basis.equivFun_apply] using
      (fastBasis n).equivFun.apply_symm_apply u
  have hb : (fastBasis n).repr b = v := by
    simpa only [← Module.Basis.equivFun_apply] using
      (fastBasis n).equivFun.apply_symm_apply v
  calc
    u ⬝ᵥ (fastAffinityMatrix n x *ᵥ v) =
        (∑ i, a.1 i * fastAffinityC x b i) +
          (∑ i, a.2 i * fastAffinityD x b i) := by
            simpa only [ha, hb] using fastAffinityMatrix_pairing x a b
    _ = (∑ i, b.1 i * fastAffinityC x a i) +
          (∑ i, b.2 i * fastAffinityD x a i) :=
      fastAffinity_pairing_symmetric x a b
    _ = v ⬝ᵥ (fastAffinityMatrix n x *ᵥ u) := by
      simpa only [ha, hb] using (fastAffinityMatrix_pairing x b a).symm

theorem fastAffinityMatrix_isHermitian {n : ℕ} (x : State n) :
    (fastAffinityMatrix n x).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  have h := fastAffinityMatrix_pairing_symmetric x
    (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ))
  simp only [single_one_dotProduct, Matrix.mulVec_single_one] at h
  simpa using h.symm

theorem fastAffinityMatrix_posDef {n : ℕ} (x : State n)
    (hx : x.Positive) : (fastAffinityMatrix n x).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (fastAffinityMatrix_isHermitian x)
  intro u hu
  let v := (fastBasis n).equivFun.symm u
  have hvrepr : (fastBasis n).repr v = u := by
    simpa only [← Module.Basis.equivFun_apply] using
      (fastBasis n).equivFun.apply_symm_apply u
  have hv : v ≠ 0 := by
    intro hz
    apply hu
    rw [← hvrepr, hz]
    simp
  have hpos := fastBindingEnergy_pos x hx v hv
  rw [fastBindingEnergy_eq_affinity_pairing] at hpos
  rw [← fastAffinityMatrix_pairing x v v] at hpos
  simpa only [hvrepr, star_trivial] using hpos

end
end PhosphorylationStableCapacity
