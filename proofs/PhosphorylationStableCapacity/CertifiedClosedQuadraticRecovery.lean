module
public import proofs.PhosphorylationStableCapacity.CertifiedQuadraticRecovery
public import proofs.PhosphorylationStableCapacity.ClosedLyapunovTrajectory

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix Set
open scoped BigOperators

/-- The closed Lyapunov ellipsoid in the manuscript is invariant, including
its boundary, for every actual forward solution of the quadratic field. -/
theorem certified_closed_quadratic_recovery
    {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → (ι → ℝ)) (J : (ι → ℝ) → Matrix ι ι ℝ)
    (P : Matrix ι ι ℝ) (hP : P.IsSymm)
    (centre equilibrium : ι → ℝ) (ρ p c M : ℝ)
    (hρ : 0 < ρ) (hp : 0 < p) (hc : 0 < c) (hM : 0 < M)
    (hshift : ‖equilibrium-centre‖ ≤ ρ/4) (heq : f equilibrium = 0)
    (hlower : ∀ v : ι → ℝ, p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v))
    (hupper : ∀ v : ι → ℝ, v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2))
    (hmidpoint : ∀ x w, f (x+w)-f x = (J (x+(1/2 : ℝ) • w)) *ᵥ w)
    (hdiss : ∀ x, ‖x-centre‖ ≤ ρ → ∀ v : ι → ℝ,
      2*(v ⬝ᵥ (P *ᵥ ((J x) *ᵥ v))) ≤ -c*(∑ i, v i^2))
    (γ : ℝ → (ι → ℝ))
    (hγ : ∀ t : ℝ, 0 ≤ t → ∀ i,
      HasDerivWithinAt (fun s => γ s i) (f (γ t) i) (Ici (0 : ℝ)) t)
    (hinit : (γ 0-equilibrium) ⬝ᵥ (P *ᵥ (γ 0-equilibrium)) ≤ p*(ρ/2)^2) :
    (∀ t : ℝ, 0 ≤ t →
      (γ t-equilibrium) ⬝ᵥ (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧
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
  have hslope (t : ℝ) (_ht : 0 ≤ t) (hgt : g t < p*(3*ρ/4)^2) :
      g' t ≤ -(c/M)*g t := by
    have hvsq : (∑ i, v t i^2) < (3*ρ/4)^2 := by
      exact lt_of_mul_lt_mul_left ((hlower (v t)).trans_lt hgt) hp.le
    have hdlt : d t < 3*ρ/4 := by
      exact (Real.sqrt_lt' (by linarith : 0 < 3*ρ/4)).mpr hvsq
    have hvnorm : ‖v t‖ < 3*ρ/4 :=
      (sup_norm_le_finiteEuclideanLength (v t)).trans_lt hdlt
    let mid := equilibrium+(1/2 : ℝ) • v t
    have hmid : ‖mid-centre‖ ≤ ρ := by
      have he : mid-centre = (equilibrium-centre)+(1/2 : ℝ) • v t := by
        dsimp only [mid]
        abel
      rw [he]
      have htri := norm_add_le (equilibrium-centre) ((1/2 : ℝ) • v t)
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : 0 ≤ (1/2 : ℝ))] at htri
      linarith only [htri, hshift, hvnorm, hρ]
    have hfield : f (γ t) = (J mid) *ᵥ v t := by
      have h := hmidpoint equilibrium (v t)
      have he : equilibrium+v t = γ t := by dsimp only [v]; abel
      rw [he, heq, sub_zero] at h
      exact h
    have hr := lyapunov_directional_energy_ratio (J mid) P (v t) c M hc.le hM
      (hdiss mid hmid (v t)) (hupper (v t))
    dsimp only [g', g]
    rw [hfield]
    exact hr
  have hL : p*(ρ/2)^2 < p*(3*ρ/4)^2 := by
    apply mul_lt_mul_of_pos_left _ hp
    nlinarith [sq_pos_of_pos hρ]
  obtain ⟨hstay, henv, htime⟩ := closed_lyapunov_trajectory g g' d p c M ρ
    (p*(3*ρ/4)^2) hp hc hM hρ hL hderiv hlow
    (fun _t _ht => Real.sqrt_nonneg _) hslope hinit
  refine ⟨hstay, ?_, henv, htime⟩
  intro t ht
  have he : Real.exp (-(c/(2*M))*t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_pos hc (by linarith : 0 < 2*M)).le) ht
  have hdle : d t ≤ ρ/2 := (henv t ht).trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (half_pos hρ).le)
  have hn := (sup_norm_le_finiteEuclideanLength (v t)).trans hdle
  have hsum : γ t-centre = v t+(equilibrium-centre) := by dsimp only [v]; abel
  rw [hsum]
  have htri := norm_add_le (v t) (equilibrium-centre)
  linarith only [htri, hn, hshift, hρ]

end
end PhosphorylationStableCapacity
