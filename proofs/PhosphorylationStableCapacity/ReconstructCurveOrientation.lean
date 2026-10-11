module
public import proofs.PhosphorylationStableCapacity.ReconstructAffineTangent

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- A differentiable reconstructed source curve with fixed enzyme
totals and decreasing substrate total has the physical augmented
current orientation, provided its ratio increases and the occupancy
factor is negative. -/
theorem reconstructed_curve_augmented_orientation {n : ℕ}
    (k : Rates n) (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b z H : ℝ)
    (hk : k.Positive)
    (hx : (reconstruct t B D (u y) (s y) (f y)).Positive)
    (hu : HasDerivAt u (u y*b) y)
    (hs : HasDerivAt s (s y*a) y)
    (hf : HasDerivAt f (f y*z) y)
    (hb : 0 < b)
    (hq : sourcePathZerothMoment
      (sourceOccupancyDifference
        (reconstruct t B D (u y) (s y) (f y))) < 0)
    (hET : HasDerivAt (fun v =>
      totalE (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hFT : HasDerivAt (fun v =>
      totalF (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hST : HasDerivAt (fun v =>
      totalS (reconstruct t B D (u v) (s v) (f v))) H y)
    (hH : H < 0) :
    0 < (-1 : ℝ)^n *
      (sourceAugmentedCurrentMatrix k
        (reconstruct t B D (u y) (s y) (f y))).det := by
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
  have htotal : sourceAugmentedTotalRow x ⬝ᵥ σ < 0 := by
    have hderiv := hSn.unique hST
    rw [hspecies] at hderiv
    rw [hderiv]
    exact hH
  exact sourceAugmentedCurrentMatrix_parity_det_pos_of_affine_tangent
    k x hk hx a b hb hq hcurrent htotal

end
end PhosphorylationStableCapacity
