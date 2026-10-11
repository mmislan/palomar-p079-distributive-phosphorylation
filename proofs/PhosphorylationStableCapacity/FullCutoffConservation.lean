module
public import proofs.PhosphorylationStableCapacity.FullCutoffPositivity

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

-- The conversion leaves equality subgoals only on the newer mathlib pin.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The species cutoff does not alter the three stoichiometric
conservation laws: the vector field is evaluated at a clamped state,
but every such field vector still has zero totals. -/
theorem full_cutoff_curve_conserves_totals {n : ℕ}
    (k : Rates n) (B : ℝ) (γ : ℝ → FullSpace n)
    (hγ : ∀ t : ℝ,
      HasDerivAt γ
        (fullFieldEuclid k (clampFullSpace B (γ t))) t) :
    ∀ t : ℝ,
      totalE (ofFullSpace (γ t)) =
        totalE (ofFullSpace (γ 0)) ∧
      totalF (ofFullSpace (γ t)) =
        totalF (ofFullSpace (γ 0)) ∧
      totalS (ofFullSpace (γ t)) =
        totalS (ofFullSpace (γ 0)) := by
  let v : ℝ → FullSpace n :=
    fun t => fullFieldEuclid k (clampFullSpace B (γ t))
  have hE (t : ℝ) :
      HasDerivAt (fun s => (γ s).2.1.1) (v t).2.1.1 t := by
    simpa [v] using (hγ t).hasFDerivAt.snd.fst.fst.hasDerivAt
  have hF (t : ℝ) :
      HasDerivAt (fun s => (γ s).2.1.2) (v t).2.1.2 t := by
    simpa [v] using (hγ t).hasFDerivAt.snd.fst.snd.hasDerivAt
  have hS (t : ℝ) (i : Fin (n+1)) :
      HasDerivAt (fun s => (γ s).1 i) ((v t).1 i) t := by
    simpa [v] using
      (hasDerivAt_pi.mp ((hγ t).hasFDerivAt.fst.hasDerivAt)) i
  have hC (t : ℝ) (i : Fin n) :
      HasDerivAt (fun s => (γ s).2.2.1 i)
        ((v t).2.2.1 i) t := by
    simpa [v] using
      (hasDerivAt_pi.mp
        ((hγ t).hasFDerivAt.snd.snd.fst.hasDerivAt)) i
  have hD (t : ℝ) (i : Fin n) :
      HasDerivAt (fun s => (γ s).2.2.2 i)
        ((v t).2.2.2 i) t := by
    simpa [v] using
      (hasDerivAt_pi.mp
        ((hγ t).hasFDerivAt.snd.snd.snd.hasDerivAt)) i
  have htotalE (t : ℝ) :
      HasDerivAt
        (fun s => totalE (ofFullSpace (γ s)))
        (totalE (ofFullSpace (v t))) t := by
    convert
      (hE t).add
        (HasDerivAt.fun_sum (u := Finset.univ)
          (fun i _ => hC t i)) using 1
    all_goals
      first
      | funext s; simp [totalE, ofFullSpace, Pi.add_apply]
      | simp [totalE, ofFullSpace]
  have htotalF (t : ℝ) :
      HasDerivAt
        (fun s => totalF (ofFullSpace (γ s)))
        (totalF (ofFullSpace (v t))) t := by
    convert
      (hF t).add
        (HasDerivAt.fun_sum (u := Finset.univ)
          (fun i _ => hD t i)) using 1
    all_goals
      first
      | funext s; simp [totalF, ofFullSpace, Pi.add_apply]
      | simp [totalF, ofFullSpace]
  have htotalS (t : ℝ) :
      HasDerivAt
        (fun s => totalS (ofFullSpace (γ s)))
        (totalS (ofFullSpace (v t))) t := by
    convert
      ((HasDerivAt.fun_sum (u := Finset.univ)
          (fun i _ => hS t i)).add
        (HasDerivAt.fun_sum (u := Finset.univ)
          (fun i _ => hC t i))).add
        (HasDerivAt.fun_sum (u := Finset.univ)
          (fun i _ => hD t i)) using 1
    all_goals
      first
      | funext s; simp [totalS, ofFullSpace, add_assoc, Pi.add_apply]
      | simp [totalS, ofFullSpace, add_assoc]
  have hEzero (t : ℝ) :
      HasDerivAt
        (fun s => totalE (ofFullSpace (γ s))) 0 t := by
    simpa [v, fullFieldEuclid, of_toFullSpace,
      totalE_field_zero] using htotalE t
  have hFzero (t : ℝ) :
      HasDerivAt
        (fun s => totalF (ofFullSpace (γ s))) 0 t := by
    simpa [v, fullFieldEuclid, of_toFullSpace,
      totalF_field_zero] using htotalF t
  have hSzero (t : ℝ) :
      HasDerivAt
        (fun s => totalS (ofFullSpace (γ s))) 0 t := by
    simpa [v, fullFieldEuclid, of_toFullSpace,
      totalS_field_zero] using htotalS t
  intro t
  exact ⟨
    is_const_of_deriv_eq_zero
      (fun s => (hEzero s).differentiableAt)
      (fun s => (hEzero s).deriv) t 0,
    is_const_of_deriv_eq_zero
      (fun s => (hFzero s).differentiableAt)
      (fun s => (hFzero s).deriv) t 0,
    is_const_of_deriv_eq_zero
      (fun s => (hSzero s).differentiableAt)
      (fun s => (hSzero s).deriv) t 0⟩

end
end PhosphorylationStableCapacity
