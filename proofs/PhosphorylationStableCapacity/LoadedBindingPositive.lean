module
public import proofs.PhosphorylationStableCapacity.LoadedBindingAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Weighted finite Cauchy-Schwarz without square roots. -/
theorem weighted_binding_cauchy {ι : Type*} [Fintype ι]
    (C σ : ι → ℝ) (hC : ∀ i, 0 ≤ C i) :
    (∑ i, C i * σ i) ^ 2 ≤
      (∑ i, C i) * (∑ i, C i * σ i ^ 2) := by
  classical
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => C i * σ i)
    (f := C) (g := fun i => C i * σ i ^ 2)
    (fun i _ => hC i)
    (fun i _ => mul_nonneg (hC i) (sq_nonneg _))
    (fun i _ => by ring_nf; exact le_refl _)

/-- The bound-complex part of the mass quadratic form is nonnegative when
the enzyme total is the free enzyme plus all bound complexes. -/
theorem binding_complex_quadratic_nonneg {ι : Type*} [Fintype ι]
    (C σ : ι → ℝ) (ET : ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hET : ET = 1 + ∑ i, C i) :
    0 ≤ (∑ i, C i * σ i ^ 2) - (∑ i, C i * σ i) ^ 2 / ET := by
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC i)
  have hETpos : 0 < ET := by rw [hET]; linarith
  have hsq : 0 ≤ ∑ i, C i * σ i ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hC i) (sq_nonneg _))
  have hcs := weighted_binding_cauchy C σ hC
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hETpos).mpr
  rw [hET]
  nlinarith

/-- Exact quadratic form of the loaded mass matrix. -/
theorem loadedBindingMass_quadratic {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT : ℝ) :
    (∑ i, σ i * (loadedBindingMass S C Y ET FT).mulVec σ i) =
      (∑ i, S i * σ i ^ 2) +
      ((∑ i, C i * σ i ^ 2) - (∑ i, C i * σ i) ^ 2 / ET) +
      ((∑ i, Y i * σ i ^ 2) - (∑ i, Y i * σ i) ^ 2 / FT) := by
  have hterm (i : ι) :
      σ i * (S i * σ i +
        C i * (σ i - (∑ j, C j * σ j) / ET) +
        Y i * (σ i - (∑ j, Y j * σ j) / FT)) =
      S i * σ i ^ 2 + C i * σ i ^ 2 + Y i * σ i ^ 2 -
        C i * σ i * (∑ j, C j * σ j) / ET -
        Y i * σ i * (∑ j, Y j * σ j) / FT := by
    ring
  have hCterm :
      (∑ i, C i * σ i * (∑ j, C j * σ j) / ET) =
        (∑ i, C i * σ i) ^ 2 / ET := by
    calc
      _ = ∑ i, (C i * σ i) * ((∑ j, C j * σ j) / ET) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, C i * σ i) * ((∑ j, C j * σ j) / ET) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  have hYterm :
      (∑ i, Y i * σ i * (∑ j, Y j * σ j) / FT) =
        (∑ i, Y i * σ i) ^ 2 / FT := by
    calc
      _ = ∑ i, (Y i * σ i) * ((∑ j, Y j * σ j) / FT) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, Y i * σ i) * ((∑ j, Y j * σ j) / FT) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  simp_rw [loadedBindingMass_action, hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hCterm, hYterm]
  ring

/-- Positive free substrates and exact enzyme totals make the finite loaded
mass matrix strictly positive on every nonzero real direction. -/
theorem loadedBindingMass_quadratic_pos {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT : ℝ)
    (hS : ∀ i, 0 < S i)
    (hC : ∀ i, 0 ≤ C i)
    (hY : ∀ i, 0 ≤ Y i)
    (hET : ET = 1 + ∑ i, C i)
    (hFT : FT = 1 + ∑ i, Y i)
    (hσ : σ ≠ 0) :
    0 < ∑ i, σ i * (loadedBindingMass S C Y ET FT).mulVec σ i := by
  have hex : ∃ i, σ i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hSsum : 0 < ∑ j, S j * σ j ^ 2 :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hS j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hS i) (sq_pos_of_ne_zero hi)⟩
  have hCnon := binding_complex_quadratic_nonneg C σ ET hC hET
  have hYnon := binding_complex_quadratic_nonneg Y σ FT hY hFT
  rw [loadedBindingMass_quadratic]
  linarith

/-- The exact positive binding mass matrix is invertible at every state with
positive free substrates and valid enzyme totals. -/
theorem loadedBindingMass_det_ne_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT : ℝ)
    (hS : ∀ i, 0 < S i)
    (hC : ∀ i, 0 ≤ C i)
    (hY : ∀ i, 0 ≤ Y i)
    (hET : ET = 1 + ∑ i, C i)
    (hFT : FT = 1 + ∑ i, Y i) :
    (loadedBindingMass S C Y ET FT).det ≠ 0 := by
  have hinj : Function.Injective (loadedBindingMass S C Y ET FT).mulVec := by
    intro σ τ heq
    have hzero : (loadedBindingMass S C Y ET FT).mulVec (σ - τ) = 0 := by
      simp [Matrix.mulVec_sub, heq]
    have hdiff : σ - τ = 0 := by
      by_contra hne
      have hpos := loadedBindingMass_quadratic_pos S C Y (σ - τ) ET FT
        hS hC hY hET hFT hne
      rw [hzero] at hpos
      simp at hpos
    exact sub_eq_zero.mp hdiff
  have hunit : IsUnit (loadedBindingMass S C Y ET FT) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end
end PhosphorylationStableCapacity
