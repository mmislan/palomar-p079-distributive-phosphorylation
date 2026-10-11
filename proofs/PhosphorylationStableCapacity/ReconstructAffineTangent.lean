module
public import proofs.PhosphorylationStableCapacity.SourceAffineLoadedTotalBalance

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- A monomial source coordinate has the expected affine logarithmic
tangent when its scale and ratio have logarithmic velocities `a,b`. -/
theorem hasDerivAt_sourceMonomial
    (u s : ℝ → ℝ) (y a b : ℝ)
    (hu : HasDerivAt u (u y * b) y)
    (hs : HasDerivAt s (s y * a) y) (j : ℕ) :
    HasDerivAt (fun v => (u v)^j * s v)
      ((u y)^j * s y * (a + (j : ℝ)*b)) y := by
  have h := (hu.pow j).mul hs
  convert h using 1
  cases j with
  | zero => simp
  | succ j =>
      simp [pow_succ]
      ring

/-- The three-factor complex monomial carries one extra ratio and
free-enzyme logarithmic velocity. -/
theorem hasDerivAt_sourceComplexMonomial
    (u s f : ℝ → ℝ) (y a b z : ℝ)
    (hu : HasDerivAt u (u y * b) y)
    (hs : HasDerivAt s (s y * a) y)
    (hf : HasDerivAt f (f y * z) y) (j : ℕ) :
    HasDerivAt (fun v => (u v)^j * s v * f v)
      ((u y)^j * s y * f y * (a + (j : ℝ)*b + z)) y := by
  have hm := hasDerivAt_sourceMonomial u s y a b hu hs j
  have h := hm.mul hf
  convert h using 1
  ring

theorem hasDerivAt_reconstruct_substrate {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b : ℝ)
    (hu : HasDerivAt u (u y * b) y)
    (hs : HasDerivAt s (s y * a) y)
    (j : Fin (n+1)) :
    HasDerivAt (fun v => (reconstruct t B D (u v) (s v) (f v)).S j)
      ((reconstruct t B D (u y) (s y) (f y)).S j *
        sourceAffineLogTangent a b j) y := by
  have h := (hasDerivAt_sourceMonomial u s y a b hu hs j.val).const_mul (t j)
  convert h using 1
  · ext v
    simp [reconstruct]
    ring
  · simp [reconstruct, sourceAffineLogTangent]
    ring

theorem hasDerivAt_reconstruct_kinase_complex {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b z : ℝ)
    (hu : HasDerivAt u (u y * b) y)
    (hs : HasDerivAt s (s y * a) y)
    (hf : HasDerivAt f (f y * z) y)
    (i : Fin n) :
    HasDerivAt (fun v => (reconstruct t B D (u v) (s v) (f v)).C i)
      ((reconstruct t B D (u y) (s y) (f y)).C i *
        (sourceAffineLogTangent a b i.succ + z)) y := by
  have h := (hasDerivAt_sourceComplexMonomial u s f y a b z
    hu hs hf (i.val+1)).const_mul (B i)
  convert h using 1
  · ext v
    simp [reconstruct]
    ring
  · simp [reconstruct, sourceAffineLogTangent]
    ring

theorem hasDerivAt_reconstruct_phosphatase_complex {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b z : ℝ)
    (hu : HasDerivAt u (u y * b) y)
    (hs : HasDerivAt s (s y * a) y)
    (hf : HasDerivAt f (f y * z) y)
    (i : Fin n) :
    HasDerivAt (fun v => (reconstruct t B D (u v) (s v) (f v)).D i)
      ((reconstruct t B D (u y) (s y) (f y)).D i *
        (sourceAffineLogTangent a b i.succ + z)) y := by
  have h := (hasDerivAt_sourceComplexMonomial u s f y a b z
    hu hs hf (i.val+1)).const_mul (D i)
  convert h using 1
  · ext v
    simp [reconstruct]
    ring
  · simp [reconstruct, sourceAffineLogTangent]
    ring

theorem hasDerivAt_reconstruct_kinase_enzyme {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y b z : ℝ)
    (hu : HasDerivAt u (u y * b) y)
    (hf : HasDerivAt f (f y * z) y) :
    HasDerivAt (fun v => (reconstruct t B D (u v) (s v) (f v)).E)
      ((reconstruct t B D (u y) (s y) (f y)).E * (b+z)) y := by
  have hfun :
      (fun v => (reconstruct t B D (u v) (s v) (f v)).E) = u * f := by
    funext v
    simp [reconstruct, Pi.mul_apply]
  have hscalar :
      (reconstruct t B D (u y) (s y) (f y)).E * (b+z) =
        u y * b * f y + u y * (f y * z) := by
    simp only [reconstruct]
    ring
  rw [hfun, hscalar]
  exact hu.mul hf

theorem hasDerivAt_reconstruct_phosphatase_enzyme {n : ℕ}
    (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y z : ℝ)
    (hf : HasDerivAt f (f y * z) y) :
    HasDerivAt (fun v => (reconstruct t B D (u v) (s v) (f v)).F)
      ((reconstruct t B D (u y) (s y) (f y)).F * z) y := by
  simpa only [reconstruct] using hf

end
end PhosphorylationStableCapacity
