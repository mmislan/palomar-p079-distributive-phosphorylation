module
public import proofs.PhosphorylationStableCapacity.RateVariationTranslated

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- In the explicit three-list perturbation family, positivity of a base
literal rate list holds on an open neighborhood of the zero parameter. -/
theorem rateVariation_positive_neighborhood {n : ℕ}
    (k : Rates n) (hk : k.Positive) (x : State n) :
    ∃ U : Set (CoordinateSpace n),
      IsOpen U ∧ (0 : CoordinateSpace n) ∈ U ∧
      ∀ v ∈ U,
        (ratesAdd k (rateVariation x v.2.1 v.2.2 v.1)).Positive := by
  let perturb (v : CoordinateSpace n) : Rates n :=
    ratesAdd k (rateVariation x v.2.1 v.2.2 v.1)
  let U : Set (CoordinateSpace n) := {v | (perturb v).Positive}
  refine ⟨U, ?_, ?_, ?_⟩
  · have hcoord (i : Fin n) :
        IsOpen {v : CoordinateSpace n |
          0 < (perturb v).a i ∧ 0 < (perturb v).b i ∧
          0 < (perturb v).c i ∧ 0 < (perturb v).alpha i ∧
          0 < (perturb v).beta i ∧ 0 < (perturb v).gamma i} := by
      have ha : Continuous (fun v : CoordinateSpace n => (perturb v).a i) := by
        unfold perturb ratesAdd rateVariation
        dsimp
        fun_prop
      have hb : Continuous (fun v : CoordinateSpace n => (perturb v).b i) := by
        unfold perturb ratesAdd rateVariation
        dsimp
        fun_prop
      have hc : Continuous (fun v : CoordinateSpace n => (perturb v).c i) := by
        unfold perturb ratesAdd rateVariation
        dsimp
        fun_prop
      have halpha : Continuous
          (fun v : CoordinateSpace n => (perturb v).alpha i) := by
        unfold perturb ratesAdd rateVariation
        dsimp
        fun_prop
      have hbeta : Continuous
          (fun v : CoordinateSpace n => (perturb v).beta i) := by
        unfold perturb ratesAdd rateVariation
        dsimp
        fun_prop
      have hgamma : Continuous
          (fun v : CoordinateSpace n => (perturb v).gamma i) := by
        unfold perturb ratesAdd rateVariation
        dsimp
        fun_prop
      have hopen {f : CoordinateSpace n → ℝ} (hf : Continuous f) :
          IsOpen {v | 0 < f v} := by
        have heq : {v | 0 < f v} = f ⁻¹' Set.Ioi (0 : ℝ) := by
          ext v
          simp
        rw [heq]
        exact (isOpen_Ioi (a := (0 : ℝ))).preimage hf
      have heq :
          {v : CoordinateSpace n |
            0 < (perturb v).a i ∧ 0 < (perturb v).b i ∧
            0 < (perturb v).c i ∧ 0 < (perturb v).alpha i ∧
            0 < (perturb v).beta i ∧ 0 < (perturb v).gamma i} =
          {v | 0 < (perturb v).a i} ∩
            ({v | 0 < (perturb v).b i} ∩
              ({v | 0 < (perturb v).c i} ∩
                ({v | 0 < (perturb v).alpha i} ∩
                  ({v | 0 < (perturb v).beta i} ∩
                    {v | 0 < (perturb v).gamma i})))) := by
        ext v
        simp
      rw [heq]
      exact (hopen ha).inter ((hopen hb).inter ((hopen hc).inter
        ((hopen halpha).inter ((hopen hbeta).inter (hopen hgamma)))))
    have hU : IsOpen (⋂ i : Fin n,
        {v : CoordinateSpace n |
          0 < (perturb v).a i ∧ 0 < (perturb v).b i ∧
          0 < (perturb v).c i ∧ 0 < (perturb v).alpha i ∧
          0 < (perturb v).beta i ∧ 0 < (perturb v).gamma i}) :=
      isOpen_iInter_of_finite hcoord
    convert hU using 1
    ext v
    simp [U, Rates.Positive]
  · simpa [U, perturb, ratesAdd, rateVariation, Rates.Positive] using hk
  · intro v hv
    exact hv

end
end PhosphorylationStableCapacity
