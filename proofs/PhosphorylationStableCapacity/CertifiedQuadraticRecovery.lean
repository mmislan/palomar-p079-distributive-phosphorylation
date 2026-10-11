module
public import proofs.PhosphorylationStableCapacity.FiniteEuclideanLength
public import proofs.PhosphorylationStableCapacity.QuantitativeMatrixDissipation
public import proofs.PhosphorylationStableCapacity.QuantitativeLyapunovTrajectory
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix Set
open scoped BigOperators

/-- Every actual solution of a quadratic field obeys the operational
recovery envelope from fixed matrix certificates on the parameter box.
The midpoint hypothesis is an exact field identity, not an approximate
linearization or an assumption of a solution remaining in the box. -/
theorem certified_quadratic_recovery
    {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → (ι → ℝ)) (J : (ι → ℝ) → Matrix ι ι ℝ)
    (P : Matrix ι ι ℝ) (hP : P.IsSymm)
    (centre equilibrium : ι → ℝ) (ρ ρin p c M : ℝ)
    (hρ : 0 < ρ) (hp : 0 < p) (hc : 0 < c) (hM : 0 < M)
    (hshift : ‖equilibrium-centre‖ ≤ ρ/4) (heq : f equilibrium = 0)
    (hlower : ∀ v : ι → ℝ, p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v))
    (hupper : ∀ v : ι → ℝ, v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2))
    (hmidpoint : ∀ x w, f (x+w)-f x = (J (x+(1/2 : ℝ) • w)) *ᵥ w)
    (hdiss : ∀ x, ‖x-centre‖ ≤ ρ → ∀ v : ι → ℝ,
      2*(v ⬝ᵥ (P *ᵥ ((J x) *ᵥ v))) ≤ -c*(∑ i, v i^2))
    (hmargin : M*ρin^2 < p*(ρ/2)^2)
    (γ : ℝ → (ι → ℝ))
    (hγ : ∀ t : ℝ, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun s => γ s i) (f (γ t) i) (Ici (0 : ℝ)) t)
    (hinit : (∑ i, (γ 0 i-equilibrium i)^2) ≤ ρin^2) :
    (∀ t : ℝ, 0 ≤ t → ‖γ t-centre‖ < ρ) ∧
    (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
      (ρ/2)*Real.exp (-(c/(2*M))*t)) ∧
    (∀ t : ℝ, 6*M/c ≤ t → finiteEuclideanLength (γ t-equilibrium) < ρ/20) := by
  let v : ℝ → ι → ℝ := fun t => γ t-equilibrium
  let g : ℝ → ℝ := fun t => v t ⬝ᵥ (P *ᵥ v t)
  let g' : ℝ → ℝ := fun t => 2*(v t ⬝ᵥ (P *ᵥ f (γ t)))
  let d : ℝ → ℝ := fun t => finiteEuclideanLength (v t)
  have hderiv (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt g (g' t) (Ici (0 : ℝ)) t := by
    exact symmetric_matrix_energy_hasDerivWithinAt P hP v (f (γ t)) _ t
      (fun i => (hγ t ht i).sub_const (equilibrium i))
  have hlow (t : ℝ) (_ht : 0 ≤ t) : p*(d t)^2 ≤ g t := by
    dsimp only [d, g]
    rw [finiteEuclideanLength_sq]
    exact hlower (v t)
  have hslope (t : ℝ) (_ht : 0 ≤ t) (hgt : g t < p*(ρ/2)^2) :
      g' t ≤ -(c/M)*g t := by
    have hvsq : (∑ i, v t i^2) < (ρ/2)^2 := by
      exact lt_of_mul_lt_mul_left ((hlower (v t)).trans_lt hgt) hp.le
    have hdlt : d t < ρ/2 := by
      exact (Real.sqrt_lt' (half_pos hρ)).mpr hvsq
    have hvnorm : ‖v t‖ < ρ/2 := (sup_norm_le_finiteEuclideanLength (v t)).trans_lt hdlt
    let mid := equilibrium+(1/2 : ℝ) • v t
    have hmid : ‖mid-centre‖ ≤ ρ := by
      have he : mid-centre = (equilibrium-centre)+(1/2 : ℝ) • v t := by
        dsimp only [mid]
        abel
      rw [he]
      have htri := norm_add_le (equilibrium-centre) ((1/2 : ℝ) • v t)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))] at htri
      linarith only [htri, hshift, hvnorm, hρ]
    have hfield : f (γ t) = (J mid) *ᵥ v t := by
      have h := hmidpoint equilibrium (v t)
      have he : equilibrium+v t = γ t := by dsimp only [v]; abel
      rw [he, heq, sub_zero] at h
      exact h
    have hs := hdiss mid hmid (v t)
    have hr := lyapunov_directional_energy_ratio (J mid) P (v t) c M hc.le hM hs (hupper (v t))
    dsimp only [g', g]
    rw [hfield]
    exact hr
  have hstart : g 0 < p*(ρ/2)^2 := by
    have hu := hupper (v 0)
    have hi : (∑ i, v 0 i^2) ≤ ρin^2 := hinit
    exact (hu.trans (mul_le_mul_of_nonneg_left hi hM.le)).trans_lt hmargin
  obtain ⟨hstay, henv, htime⟩ := quantitative_lyapunov_trajectory g g' d p c M ρ
    hp hc hM hρ hderiv hlow (fun _t _ht => Real.sqrt_nonneg _) hslope hstart
  refine ⟨?_, henv, htime⟩
  intro t ht
  have hn := (sup_norm_le_finiteEuclideanLength (v t)).trans_lt (hstay t ht).2
  have he : γ t-centre = v t+(equilibrium-centre) := by dsimp only [v]; abel
  rw [he]
  have htri := norm_add_le (v t) (equilibrium-centre)
  linarith only [htri, hn, hshift, hρ]
end
end PhosphorylationStableCapacity
