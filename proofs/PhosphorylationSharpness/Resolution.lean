module
public import proofs.PhosphorylationSharpness.Assembly

@[expose] public section

namespace PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

/-- Positive literal rates and a common positive compatibility class containing
an injective family of the indicated number of positive mass-action equilibria. -/
def Attains (n count : ℕ) : Prop :=
  ∃ (k : Rates n) (ET FT ST : ℝ) (z : Fin count → State n),
    k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective z ∧
      ∀ j, (z j).Positive ∧ Equilibrium k (z j) ∧
        totalE (z j)=ET ∧ totalF (z j)=FT ∧ totalS (z j)=ST

theorem attainment_succ (m : ℕ) : Attains (m+1) (2*m+1) := by
  obtain ⟨hp,hq⟩ := pair_dense m
  obtain ⟨r,⟨hD,hB⟩,hr⟩ :=
    ((conversion_eventually_positive hp hq).and (eventually_gt_atTop (0:ℝ))).exists
  let B := rawB (pair m).1 (pair m).2 r
  let D := rawD (pair m).1 (pair m).2 r
  let A : ℝ[X] := (1+X)*D
  let t : Fin (m+2) → ℝ := fun i => A.coeff i
  let b : Fin (m+1) → ℝ := fun i => B.coeff i
  let d : Fin (m+1) → ℝ := fun i => D.coeff i
  let xx : Fin (2*m+1) → ℝ := fun j => (j.val:ℝ)+2
  let z : Fin (2*m+1) → State (m+1) := fun j =>
    reconstruct t b d (ratio (xx j)) (rootS (xx j) (D.eval (ratio (xx j)))) (rootF (xx j))
  have hx (j : Fin (2*m+1)) : 1 < xx j := by
    dsimp [xx]
    nlinarith [Nat.cast_nonneg (α := ℝ) j.val]
  have hrel (j : Fin (2*m+1)) :
      (xx j-1)*(B.eval (ratio (xx j))-r*D.eval (ratio (xx j)))=
        2*(r-ratio (xx j))*D.eval (ratio (xx j)) :=
    conversion_root _ _ r (xx j) (pair_roots m j.val (by omega))
  have hA : DensePositive A (m+1) := dense_inventory_product hD
  have ht : ∀ i, 0 < t i := fun i => hA.1 i (by omega)
  have hb : ∀ i, 0 < b i := fun i => hB.1 i (by omega)
  have hd : ∀ i, 0 < d i := fun i => hD.1 i (by omega)
  refine ⟨realize t b d, 2*r, 2, 2*(r+1), z,
    realize_positive t b d ht hb hd, by positivity, by norm_num, by positivity, ?_, ?_⟩
  · intro i j hij
    have hrat := congrArg (fun w : State (m+1) => w.E/w.F) hij
    have hf (k : Fin (2*m+1)) : rootF (xx k) ≠ 0 :=
      ne_of_gt (div_pos (by norm_num) (by have := hx k; linarith))
    change (reconstruct t b d _ _ _).E/(reconstruct t b d _ _ _).F =
      (reconstruct t b d _ _ _).E/(reconstruct t b d _ _ _).F at hrat
    rw [reconstruct_ratio _ _ _ _ _ _ (hf i), reconstruct_ratio _ _ _ _ _ _ (hf j)] at hrat
    have he := ratio_injective (hx i) (hx j) hrat
    have hv : (i.val:ℝ)=(j.val:ℝ) := by dsimp [xx] at he; linarith
    apply Fin.ext
    exact_mod_cast hv
  · intro j
    exact source_from_coefficients B D hB hD r (xx j) (hx j) (hrel j)

/-- Uniform sharp lower bound for the standard sequential distributive source.
Equality with the maximum additionally uses the published Wang--Sontag upper bound;
that external upper bound is not an axiom or dependency of this theorem. -/
theorem sharp_lower_bound (n : ℕ) (hn : 1 ≤ n) : Attains n (2*n-1) := by
  cases n with
  | zero => omega
  | succ m =>
    have h : 2*(m+1)-1=2*m+1 := by omega
    simpa only [Nat.succ_eq_add_one, h] using attainment_succ m

end
end PhosphorylationSharpness
