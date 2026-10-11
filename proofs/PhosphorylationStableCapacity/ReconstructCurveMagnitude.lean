module
public import proofs.PhosphorylationStableCapacity.ReconstructCurveOrientation
public import proofs.PhosphorylationStableCapacity.ExactJacobianScalarMagnitude

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- The two exact affine equations behind the existing split-curve
orientation argument, retained as reusable magnitude data. -/
theorem reconstructed_curve_affine_moment_data {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b z H : ℝ)
    (hx : (reconstruct t B D (u y) (s y) (f y)).Positive)
    (hu : HasDerivAt u (u y*b) y)
    (hs : HasDerivAt s (s y*a) y)
    (hf : HasDerivAt f (f y*z) y)
    (hET : HasDerivAt (fun v =>
      totalE (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hFT : HasDerivAt (fun v =>
      totalF (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hST : HasDerivAt (fun v =>
      totalS (reconstruct t B D (u v) (s v) (f v))) H y) :
    let x := reconstruct t B D (u y) (s y) (f y)
    a * sourcePathZerothMoment (sourceOccupancyDifference x) +
      b * (sourcePathFirstMoment (sourceOccupancyDifference x)-1) = 0 ∧
    H = a * sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      b * sourcePathFirstMoment (sourceAugmentedTotalRow x) := by
  dsimp only
  let x : State n := reconstruct t B D (u y) (s y) (f y)
  let σ : Fin (n+1) → ℝ := sourceAffineLogTangent a b
  let curve : ℝ → State n := fun v =>
    reconstruct t B D (u v) (s v) (f v)
  have hCsum : HasDerivAt (fun v => ∑ i : Fin n, (curve v).C i)
      (∑ i : Fin n, x.C i * (σ i.succ+z)) y := by
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_reconstruct_kinase_complex t B D u s f y a b z
      hu hs hf i
  have hDsum : HasDerivAt (fun v => ∑ i : Fin n, (curve v).D i)
      (∑ i : Fin n, x.D i * (σ i.succ+z)) y := by
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_reconstruct_phosphatase_complex t B D u s f y a b z
      hu hs hf i
  have hSsum : HasDerivAt (fun v => ∑ j : Fin (n+1), (curve v).S j)
      (∑ j : Fin (n+1), x.S j * σ j) y := by
    apply HasDerivAt.fun_sum
    intro j _
    exact hasDerivAt_reconstruct_substrate t B D u s f y a b hu hs j
  have hEn : HasDerivAt (fun v => totalE (curve v))
      (x.E*(b+z) + ∑ i : Fin n, x.C i*(σ i.succ+z)) y := by
    have hfun :
        (fun v => (reconstruct t B D (u v) (s v) (f v)).E) +
          (fun v => ∑ i : Fin n, (curve v).C i) =
        (fun v => totalE (curve v)) := by
      funext v
      simp [totalE, curve, Pi.add_apply]
    have h :=
      (hasDerivAt_reconstruct_kinase_enzyme t B D u s f y b z
        hu hf).add hCsum
    rw [hfun] at h
    exact h
  have hFn : HasDerivAt (fun v => totalF (curve v))
      (x.F*z + ∑ i : Fin n, x.D i*(σ i.succ+z)) y := by
    have hfun :
        (fun v => (reconstruct t B D (u v) (s v) (f v)).F) +
          (fun v => ∑ i : Fin n, (curve v).D i) =
        (fun v => totalF (curve v)) := by
      funext v
      simp [totalF, curve, Pi.add_apply]
    have h :=
      (hasDerivAt_reconstruct_phosphatase_enzyme t B D u s f y z
        hf).add hDsum
    rw [hfun] at h
    exact h
  have hSn : HasDerivAt (fun v => totalS (curve v))
      ((∑ j : Fin (n+1), x.S j*σ j) +
        (∑ i : Fin n, x.C i*(σ i.succ+z)) +
        (∑ i : Fin n, x.D i*(σ i.succ+z))) y := by
    have hfun :
        ((fun v => ∑ j : Fin (n+1), (curve v).S j) +
          (fun v => ∑ i : Fin n, (curve v).C i)) +
          (fun v => ∑ i : Fin n, (curve v).D i) =
        (fun v => totalS (curve v)) := by
      funext v
      simp [totalS, Pi.add_apply]
    have h := (hSsum.add hCsum).add hDsum
    rw [hfun] at h
    exact h
  have hEzero : x.E*(b+z) +
      ∑ i : Fin n, x.C i*(σ i.succ+z) = 0 :=
    hEn.unique hET
  have hFzero : x.F*z +
      ∑ i : Fin n, x.D i*(σ i.succ+z) = 0 :=
    hFn.unique hFT
  have hshift (i : Fin n) : σ i.succ = σ i.castSucc + b := by
    simp [σ, sourceAffineLogTangent]
    ring
  have hEbal : totalE x*(b+z) +
      ∑ i : Fin n, x.C i*σ i.castSucc = 0 := by
    simp_rw [hshift] at hEzero
    simp only [← add_assoc, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul] at hEzero
    dsimp [totalE]
    linear_combination hEzero
  have hFbal : totalF x*z +
      ∑ i : Fin n, x.D i*σ i.succ = 0 := by
    simp only [mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul] at hFzero
    dsimp [totalF]
    linear_combination hFzero
  have hcurrent := source_affine_current_kernel_of_enzyme_balances
    x hx a b z hEbal hFbal
  have hspecies := source_affine_species_total_eq_loaded_action
    x hx a b z hEbal hFbal
  have htotal : H = sourceAugmentedTotalRow x ⬝ᵥ σ := by
    have hderiv := hSn.unique hST
    rw [hspecies] at hderiv
    exact hderiv.symm
  constructor
  · simpa only [sourcePathZerothMoment,
      sourceOccupancyFirstMoment_eq_path] using hcurrent
  · rw [sourceAugmentedTotalRow_affine_action] at htotal
    exact htotal

/-- The exact augmented determinant moment is proportional to the
substrate-total derivative along a fixed-enzyme reconstructed curve. -/
theorem reconstructed_curve_moment_magnitude {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b z H : ℝ)
    (hx : (reconstruct t B D (u y) (s y) (f y)).Positive)
    (hu : HasDerivAt u (u y*b) y)
    (hs : HasDerivAt s (s y*a) y)
    (hf : HasDerivAt f (f y*z) y)
    (hET : HasDerivAt (fun v =>
      totalE (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hFT : HasDerivAt (fun v =>
      totalF (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hST : HasDerivAt (fun v =>
      totalS (reconstruct t B D (u v) (s v) (f v))) H y) :
    let x := reconstruct t B D (u y) (s y) (f y)
    b * ((1-sourcePathFirstMoment (sourceOccupancyDifference x)) *
        sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        sourcePathFirstMoment (sourceAugmentedTotalRow x)) =
      sourcePathZerothMoment (sourceOccupancyDifference x) * H := by
  obtain ⟨hcurrent, htotal⟩ :=
    reconstructed_curve_affine_moment_data t B D u s f y a b z H
      hx hu hs hf hET hFT hST
  exact affine_current_moment_magnitude _ _ _ _ a b H hcurrent htotal

end
end PhosphorylationStableCapacity
