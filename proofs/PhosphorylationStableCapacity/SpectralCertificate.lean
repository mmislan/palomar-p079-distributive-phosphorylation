module
public import proofs.PhosphorylationStableCapacity.Assembly
public import proofs.PhosphorylationStableCapacity.MetzlerWeighted
public import proofs.PhosphorylationStableCapacity.PathLaplacian
public import proofs.PhosphorylationStableCapacity.PathMatrixBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The assembled large-parameter negative-vector certificate yields a Hurwitz
limiting block once its explicit loaded-matrix premises are available. -/
theorem large_r_block_hurwitz_of_premises (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1)
    (H : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)
    (f z : Fin (n-1) → ℝ)
    (hz : ∀ i, 0 < z i)
    (hH : ∀ i, ∑ j, H i j * z j = 1)
    (hgain : (∑ j, f j * z j) =
      (10*((4:ℝ)/3-v*((n:ℝ)-(4*(n:ℝ)-3)/9))+(2+v)/3)/(14-8*v))
    (hoff : ∀ i j, i ≠ j → 0 ≤ -H i j + f j) :
    IsHurwitz (fun i j => -H i j + f j) := by
  exact hurwitz_of_metzler_positive_vector _ z hz hoff
    (large_r_block_certificate n hn v hv hv1 H f z hH hgain)

/-- For the path matrix, positivity of the feedback entries supplies the
off-diagonal sign hypothesis of the limiting-block certificate. -/
theorem path_block_hurwitz_of_premises (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1)
    (d : Fin ((n-1)+1) → ℝ) (hd : ∀ i, 0 < d i)
    (f z : Fin (n-1) → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hz : ∀ i, 0 < z i)
    (hH : ∀ i, ∑ j, pathH d i j * z j = 1)
    (hgain : (∑ j, f j * z j) =
      (10*((4:ℝ)/3-v*((n:ℝ)-(4*(n:ℝ)-3)/9))+(2+v)/3)/(14-8*v)) :
    IsHurwitz (fun i j => -pathH d i j + f j) := by
  apply large_r_block_hurwitz_of_premises n hn v hv hv1 (pathH d) f z hz hH hgain
  intro i j hij
  have hpath := pathH_offdiag_nonpos d hd i j hij
  linarith [hf j]

/-- The same conditional Hurwitz certificate in the paper's incidence-matrix
form `R₀ diag(1/d) R₀ᵀ`, now identified exactly with the path block. -/
theorem incidence_block_hurwitz_of_premises (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1)
    (d : Fin ((n-1)+1) → ℝ) (hd : ∀ i, 0 < d i)
    (f z : Fin (n-1) → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hz : ∀ i, 0 < z i)
    (hH : ∀ i, ∑ j,
      (pathIncidence (n-1) * Matrix.diagonal (fun k => (d k)⁻¹) *
        (pathIncidence (n-1)).transpose) i j * z j = 1)
    (hgain : (∑ j, f j * z j) =
      (10*((4:ℝ)/3-v*((n:ℝ)-(4*(n:ℝ)-3)/9))+(2+v)/3)/(14-8*v)) :
    IsHurwitz (fun i j =>
      -(pathIncidence (n-1) * Matrix.diagonal (fun k => (d k)⁻¹) *
        (pathIncidence (n-1)).transpose) i j + f j) := by
  have hH' : ∀ i, ∑ j, pathH d i j * z j = 1 := by
    intro i
    simpa only [pathH_eq_incidence] using hH i
  simpa only [pathH_eq_incidence] using
    path_block_hurwitz_of_premises n hn v hv hv1 d hd f z hf hz hH' hgain

end
end PhosphorylationStableCapacity
