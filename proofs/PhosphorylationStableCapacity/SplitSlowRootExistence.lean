module
public import proofs.PhosphorylationStableCapacity.SplitSlowRoot

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter PhosphorylationSharpness
open scoped Topology

/-- Opposite signs at two fixed real test points persist under a continuous
polynomial perturbation, forcing a real zero between them. -/
theorem polynomial_family_root_between_eventually
    (P : ℝ → ℝ[X]) (a b : ℝ) (hab : a ≤ b)
    (ha : ContinuousAt (fun δ => (P δ).eval a) 0)
    (hb : ContinuousAt (fun δ => (P δ).eval b) 0)
    (hneg : (P 0).eval a < 0) (hpos : 0 < (P 0).eval b) :
    ∀ᶠ δ : ℝ in nhds 0,
      ∃ x ∈ Set.Icc a b, (P δ).IsRoot x := by
  have hneg' : ∀ᶠ δ : ℝ in nhds 0, (P δ).eval a < 0 :=
    ha.eventually (eventually_lt_nhds hneg)
  have hpos' : ∀ᶠ δ : ℝ in nhds 0, 0 < (P δ).eval b :=
    hb.eventually (eventually_gt_nhds hpos)
  filter_upwards [hneg', hpos'] with δ hδa hδb
  have hzero : (0 : ℝ) ∈ Set.Icc ((P δ).eval a) ((P δ).eval b) :=
    ⟨le_of_lt hδa, le_of_lt hδb⟩
  obtain ⟨x, hx, hroot⟩ := (Set.mem_image _ _ _).mp
    (intermediate_value_Icc hab (P δ).continuous.continuousOn hzero)
  exact ⟨x, hx, hroot⟩

/-- A real polynomial with a simple zero at the origin takes opposite signs
at arbitrarily close symmetric real points. -/
theorem polynomial_simple_zero_opposite_near
    (P : ℝ[X]) (hzero : P.coeff 0 = 0)
    (hsimple : P.coeff 1 ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < η ∧ P.eval (-t) * P.eval t < 0 := by
  let q := P.divX
  have hq0 : q.eval 0 ≠ 0 := by
    simpa [q, ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_divX] using hsimple
  have hsource : P = X * q := by
    simpa [q, hzero] using (Polynomial.X_mul_divX_add P).symm
  have hprod0 : 0 < q.eval 0 * q.eval 0 := mul_self_pos.mpr hq0
  have hcont : ContinuousAt (fun t : ℝ => q.eval (-t) * q.eval t) 0 := by
    fun_prop
  have hevent : ∀ᶠ t : ℝ in nhds 0,
      0 < q.eval (-t) * q.eval t :=
    hcont.eventually (eventually_gt_nhds (by simpa using hprod0))
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let t := min (η / 2) (ρ / 2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htη : t < η := lt_of_le_of_lt (min_le_left ..) (by linarith)
  have htρ : t < ρ := lt_of_le_of_lt (min_le_right ..) (by linarith)
  have hqprod : 0 < q.eval (-t) * q.eval t :=
    hball (by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using htρ)
  have hfactor : P.eval (-t) * P.eval t =
      -(t * t) * (q.eval (-t) * q.eval t) := by
    rw [hsource]
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring
  refine ⟨t, ht, htη, ?_⟩
  rw [hfactor]
  simpa only [neg_mul] using
    (neg_lt_zero.mpr (mul_pos (mul_pos ht ht) hqprod))

/-- A simple real zero cannot disappear under a perturbation whose
polynomial evaluations are continuous at each fixed real argument. -/
theorem polynomial_simple_zero_real_root_eventually
    (P : ℝ → ℝ[X])
    (hzero : (P 0).coeff 0 = 0)
    (hsimple : (P 0).coeff 1 ≠ 0)
    (hcont : ∀ x : ℝ, ContinuousAt (fun δ => (P δ).eval x) 0)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in nhds 0,
      ∃ x : ℝ, |x| < η ∧ (P δ).IsRoot x := by
  obtain ⟨t, ht, htη, hprod⟩ :=
    polynomial_simple_zero_opposite_near (P 0) hzero hsimple η hη
  have hbounds : -t ≤ t := by linarith
  have hroot : ∀ᶠ δ : ℝ in nhds 0,
      ∃ x ∈ Set.Icc (-t) t, (P δ).IsRoot x := by
    rcases mul_neg_iff.mp hprod with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hneg : (-(P 0)).eval (-t) < 0 := by
        simpa only [Polynomial.eval_neg] using (neg_lt_zero.mpr ha)
      have hpos : 0 < (-(P 0)).eval t := by
        simpa only [Polynomial.eval_neg] using (neg_pos.mpr hb)
      have hnegative := polynomial_family_root_between_eventually
        (fun δ => -(P δ)) (-t) t hbounds
        (by
          convert (hcont (-t)).neg using 1
          ext δ
          simp [Polynomial.eval_neg])
        (by
          convert (hcont t).neg using 1
          ext δ
          simp [Polynomial.eval_neg])
        hneg hpos
      filter_upwards [hnegative] with δ hδ
      obtain ⟨x, hx, hroot⟩ := hδ
      exact ⟨x, hx, by simpa [Polynomial.IsRoot] using hroot⟩
    · exact polynomial_family_root_between_eventually
        P (-t) t hbounds (hcont (-t)) (hcont t) ha hb
  filter_upwards [hroot] with δ hδ
  obtain ⟨x, hx, hroot⟩ := hδ
  exact ⟨x, abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩, hroot⟩

theorem matrix_real_charpoly_eval_continuousAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ℝ → Matrix ι ι ℝ) (hJ : ContinuousAt J 0) (x : ℝ) :
    ContinuousAt (fun δ => (J δ).charpoly.eval x) 0 := by
  simp_rw [Matrix.eval_charpoly]
  fun_prop

/-- At every member of the split equilibrium family, sufficiently small
splitting retains a real characteristic root arbitrarily close to zero. -/
theorem split_real_slow_root_eventually
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in nhds 0,
      ∃ x : ℝ, |x| < η ∧
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (splitRetunedRates m r τ δ ε)
          (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (splitRetunedRates m r τ δ ε)
      (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))
  have hJ : ContinuousAt J 0 :=
    split_restrictedJacobianMatrix_continuousAt m r τ ε hr hD₀ hB₀ j
  have hzero : J 0 =
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r))) :=
    split_restrictedJacobianMatrix_zero_eq_coalesced m r τ ε j
  have hcoeff0 : (J 0).charpoly.coeff 0 = 0 := by
    rw [hzero]
    exact simpleNeutral_real_charpoly_coeff_zero _ hspec
  have hcoeff1 : (J 0).charpoly.coeff 1 ≠ 0 := by
    rw [hzero]
    exact simpleNeutral_real_charpoly_coeff_one_ne_zero _ hspec
  exact polynomial_simple_zero_real_root_eventually
    (fun δ => (J δ).charpoly) hcoeff0 hcoeff1
    (matrix_real_charpoly_eval_continuousAt J hJ) η hη

/-- One sufficiently small split retains a nearby real characteristic root
at every state in the finite family. -/
theorem split_real_slow_roots_uniform_eventually
    (m : ℕ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (coalescedFinalScaledRates m r τ) ε)
        (fromLoadedCoord (loadedCoordOfState (coalescedFiniteState (m+1) r)))))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ δ : ℝ in nhds 0,
      ∀ j : Fin (2*(m+1)+1),
        ∃ x : ℝ, |x| < η ∧
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (splitRetunedRates m r τ δ ε)
            (toCoordinateSpace (chart (splitFiniteState (m+1) r δ j)))).charpoly.IsRoot x := by
  apply Filter.eventually_all.mpr
  intro j
  exact split_real_slow_root_eventually
    m r τ ε hr hD₀ hB₀ hspec j η hη

end
end PhosphorylationStableCapacity
