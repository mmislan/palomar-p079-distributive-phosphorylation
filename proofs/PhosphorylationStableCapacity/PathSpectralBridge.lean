module
public import proofs.PhosphorylationStableCapacity.PathVector
public import proofs.PhosphorylationStableCapacity.SpectralCertificate

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Extend the finite path weights by zero to make the exact prefix formula
available with natural-number sum bounds. -/
def pathWeightsNat {m : ℕ} (d : Fin (m + 1) → ℝ) : ℕ → ℝ :=
  fun k => if h : k < m + 1 then d ⟨k, h⟩ else 0

/-- The explicit positive vector used by the path spectral certificate. -/
def pathVectorFin {m : ℕ} (d : Fin (m + 1) → ℝ) : Fin m → ℝ :=
  pathVectorNat (pathWeightsNat d)

theorem pathVectorFin_pos {m : ℕ} (d : Fin (m + 1) → ℝ)
    (hd : ∀ k, 0 < d k) (i : Fin m) : 0 < pathVectorFin d i := by
  apply pathVectorNat_pos
  intro k hk
  have hlt : k < m + 1 := by omega
  change 0 < (if h : k < m + 1 then d ⟨k, h⟩ else 0)
  simpa only [hlt, dite_true] using hd ⟨k, hlt⟩

theorem pathVectorFin_action {m : ℕ} (hm : 0 < m)
    (d : Fin (m + 1) → ℝ) (hd : ∀ k, 0 < d k) :
    ∀ i, (pathH d).mulVec (pathVectorFin d) i = 1 := by
  let dn := pathWeightsNat d
  have hdn : ∀ k ≤ m, 0 < dn k := by
    intro k hk
    have hlt : k < m + 1 := by omega
    change 0 < (if h : k < m + 1 then d ⟨k, h⟩ else 0)
    simpa only [hlt, dite_true] using hd ⟨k, hlt⟩
  have hflux := pathVectorNat_affine_flux hm dn hdn
  apply pathH_mulVec_eq_one_of_affine_flux d
    (fun k => ne_of_gt (hd k)) (pathVectorFin d) (pathMean m dn)
  intro k
  have hk := hflux k
  have hrestrict : dn k.val = d k := by
    change (if h : k.val < m + 1 then d ⟨k.val, h⟩ else 0) = d k
    simp only [k.isLt, dite_true]
  simpa only [pathVectorFin, dn, hrestrict] using hk

/-- The positive path vector and its Poisson action are discharged; the
source-specific feedback signs and scalar gain remain explicit premises. -/
theorem path_block_hurwitz_of_explicit_gain (n : ℕ) (hn : 2 ≤ n) (v : ℝ)
    (hv : 0 < v) (hv1 : v < 1)
    (d : Fin ((n - 1) + 1) → ℝ) (hd : ∀ i, 0 < d i)
    (f : Fin (n - 1) → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hgain : (∑ j, f j * pathVectorFin d j) =
      (10*((4:ℝ)/3-v*((n:ℝ)-(4*(n:ℝ)-3)/9))+(2+v)/3)/(14-8*v)) :
    IsHurwitz (fun i j => -pathH d i j + f j) := by
  have hm : 0 < n - 1 := by omega
  apply path_block_hurwitz_of_premises n hn v hv hv1 d hd f (pathVectorFin d) hf
    (pathVectorFin_pos d hd)
  · intro i
    simpa only [Matrix.mulVec, dotProduct] using pathVectorFin_action hm d hd i
  · exact hgain

end
end PhosphorylationStableCapacity
