module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingContinuity435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSchur435
public import proofs.PhosphorylationStableCapacity.CompactLoadedFullJacobian435
public import proofs.PhosphorylationStableCapacity.CompactAllCurrentFiniteSlow435
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurPremises435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial
open scoped Topology Matrix.Norms.L2Operator

/-- One binding threshold lifts the manuscript's literal
`bᵢ=βᵢ=1` kinetics for every member of a compact independent-current
family. The slow Schur polynomial is the exact finite current matrix,
while the positive fast rows are allowed to vary with the currents. -/
theorem coalescedPaperFixedBinding_compact_spectrum_eventually
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (K : Set (PositivePrefixCurrents m)), IsCompact K →
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
            0 < ε → ∀ ω ∈ K,
              SimpleNeutralHurwitzComplement
                (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                  (relaxRates (paperFixedBindingRates
                    (coalescedAllScaledRates m r
                      (Fin.lastCases τ ω.val))) ε)
                  (fromLoadedCoord (loadedCoordOfState
                    (coalescedFiniteState (m+1) r)))) := by
  filter_upwards [coalescedAllCurrentFiniteSlowSpectrum_compact_eventually m,
    paperFixedBindingSchur_charpoly_eventually m,
    coalescedAllSchurPremises_eventually m,
    coalescedAllScaledRates_eventually_source m,
    coalescedFiniteState_eventually_equilibrium (m+1)]
    with r hfinite hschur hprem hsource hfiniteSource
  intro K hK
  filter_upwards [hfinite K hK, self_mem_nhdsWithin]
    with τ hτ hτpos
  let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
  let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
  let k₀ : K → Rates (m+2) := fun a =>
    coalescedAllScaledRates m r (Fin.lastCases (motive := fun _ => ℝ) τ a.val.val)
  let k : K → Rates (m+2) := fun a => paperFixedBindingRates (k₀ a)
  let q : K → ℝ[X] := fun a => Classical.choose (hτ a.val a.property)
  have hKsub : IsCompact (Set.univ : Set K) :=
    isCompact_iff_isCompact_univ.mp hK
  have hw (a : K) : ∀ i : Fin (m+2),
      (0 : ℝ) < Fin.lastCases (motive := fun _ => ℝ) τ a.val.val i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa using hτpos
    | cast i => simpa using a.val.property i
  let w₁ : Fin (m+2) → ℝ := Fin.lastCases τ (fun _ => 1)
  have hw₁ : ∀ i : Fin (m+2), 0 < w₁ i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w₁] using hτpos
    | cast i => simp [w₁]
  have hbase : (coalescedFiniteRates (m+1) r).Positive := hfiniteSource.1
  have hk : Continuous (fun a : K => rateVector (k a)) :=
    (continuous_coalescedPaperFixedBinding_rateVector m r τ hτpos hbase).comp
      continuous_subtype_val
  have hpos : x.Positive := (hprem w₁ hw₁).1
  have heq : ∀ a ∈ (Set.univ : Set K), Equilibrium (k a) x := by
    intro a ha
    have hb := hprem (Fin.lastCases (motive := fun _ => ℝ) τ a.val.val) (hw a)
    have hk₀ := (hsource (Fin.lastCases (motive := fun _ => ℝ) τ a.val.val) (hw a)).1
    exact paperFixedBindingRates_preserves_equilibrium (k₀ a) x hk₀ hb.2.1
  have hρ : ∀ a ∈ (Set.univ : Set K), ∀ j : Fin (m+2),
      0 < (k a).a j*x.S j.castSucc*x.E := by
    intro a ha j
    have hk₀ := (hsource (Fin.lastCases (motive := fun _ => ℝ) τ a.val.val) (hw a)).1
    have hka := paperFixedBindingRates_positive (k₀ a) hk₀
    exact mul_pos (mul_pos (hka j).1 (hpos.1 j.castSucc)) hpos.2.1
  have hσ : ∀ a ∈ (Set.univ : Set K), ∀ j : Fin (m+2),
      0 < (k a).alpha j*x.S j.succ*x.F := by
    intro a ha j
    have hk₀ := (hsource (Fin.lastCases (motive := fun _ => ℝ) τ a.val.val) (hw a)).1
    have hka := paperFixedBindingRates_positive (k₀ a) hk₀
    exact mul_pos (mul_pos (hka j).2.2.2.1 (hpos.1 j.succ)) hpos.2.2.1
  have hSchur : ∀ a ∈ (Set.univ : Set K),
      let A := LinearMap.toMatrix (Pi.basisFun ℝ (Fin (m+2)))
        (Pi.basisFun ℝ (Fin (m+2)))
        (loadedBlockA (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
      let B := LinearMap.toMatrix (fastBasis (m+2))
        (Pi.basisFun ℝ (Fin (m+2)))
        (loadedBlockB (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
      let C := LinearMap.toMatrix (Pi.basisFun ℝ (Fin (m+2)))
        (fastBasis (m+2))
        (loadedBlockC (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
      let D := LinearMap.toMatrix (fastBasis (m+2))
        (fastBasis (m+2))
        (loadedBlockD (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
      (A - B * D⁻¹ * C).charpoly = q a * Polynomial.X := by
    intro a ha
    dsimp only
    let w : Fin (m+2) → ℝ := Fin.lastCases (motive := fun _ => ℝ) τ a.val.val
    obtain ⟨hfactor, _, _⟩ :=
      Classical.choose_spec (hτ a.val a.property)
    have hfactor' :
        (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly =
          q a * Polynomial.X := by
      rw [coalescedAllCurrentMatrix_eq_prefix_then_final m r τ a.val.val]
      exact hfactor
    have hDmatrix := loadedBlockD_toMatrix_eq_fastBinding
      (2*r) 2 (2*(r+1)) (k a) u hpos (heq a (by simp))
    rw [hDmatrix]
    calc
      _ = (schurLinear
          (loadedBlockA (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
          (loadedBlockB (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
          (loadedBlockC (2*r) 2 (2*(r+1)) (k a) u).toLinearMap
          (fastBindingEquiv x hpos
            (fun j => (k a).a j*x.S j.castSucc*x.E)
            (fun j => (k a).alpha j*x.S j.succ*x.F)
            (hρ a (by simp)) (hσ a (by simp)))).charpoly := by
              exact (loadedSchur_charpoly_eq_matrix
                (2*r) 2 (2*(r+1)) (k a) u hpos
                (heq a (by simp)) (hρ a (by simp))
                (hσ a (by simp))).symm
      _ = (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly :=
        hschur w (hw a) hpos (heq a (by simp))
          (hρ a (by simp)) (hσ a (by simp))
      _ = q a * Polynomial.X := hfactor'
  have hq : ∀ a ∈ (Set.univ : Set K), (q a).eval 0 ≠ 0 := by
    intro a ha
    exact (Classical.choose_spec (hτ a.val a.property)).2.1
  have hqleft : ∀ a ∈ (Set.univ : Set K), ∀ z : ℂ,
      ((q a).map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
    intro a ha
    exact (Classical.choose_spec (hτ a.val a.property)).2.2
  have hε := compact_loadedRestrictedJacobian_eventually_simple_zero_hurwitz_complement
    (Set.univ : Set K) hKsub (2*r) 2 (2*(r+1)) u k hk
      hpos heq hρ hσ q hSchur hq hqleft
  filter_upwards [hε] with ε hε hεpos ω hω
  exact hε ⟨ω, hω⟩ (by simp) hεpos

end

end PhosphorylationStableCapacity
