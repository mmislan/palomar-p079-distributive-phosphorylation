module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingActualCurrentAllSize
public import proofs.PhosphorylationStableCapacity.FiniteOffsetGapBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- The finite ordered tuple appears literally in the observable and
quantitative denominator, while `PaperFixedBindingCompletePoint` keeps
all the equilibrium, analytic-root, sign, and transverse statements
about the same rates and states. -/
def PaperFixedBindingFinitePoint
    (m : ℕ) (xoffset : Fin (2*(m+1)+1) → ℝ)
    (ξ : ℕ → ℝ) (r τ ε α K δ : ℝ)
    (θ : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  PaperFixedBindingCompletePoint m ξ r τ ε α K δ θ lam ∧
    ∀ j : Fin (2*(m+1)+1),
      let s := arbitrarySplitFiniteState (m+1) ξ r δ j
      Real.sqrt (1+8*s.E/s.F) = 3+δ*xoffset j ∧
      |lam j δ / (-paperFixedBindingPrintedCoefficient m r τ ε θ *
        δ^(2*(m+1)) * finiteOffsetGap xoffset j) - 1| ≤ K*|δ| ∧
      ∃ err : ℝ, |err| ≤ 2*K*|δ| ∧
        1/|lam j δ| = (1+err)/
          (paperFixedBindingPrintedCoefficient m r τ ε θ *
            |finiteOffsetGap xoffset j| * δ^(2*(m+1)))

theorem paperFixedBindingCompletePoint_to_finiteTuple
    (m : ℕ) (xoffset : Fin (2*(m+1)+1) → ℝ)
    (ξ : ℕ → ℝ)
    (hagree : ∀ j : Fin (2*(m+1)+1), ξ j.val = xoffset j)
    (r τ ε α K δ : ℝ) (θ : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ)
    (h : PaperFixedBindingCompletePoint
      m ξ r τ ε α K δ θ lam) :
    PaperFixedBindingFinitePoint
      m xoffset ξ r τ ε α K δ θ lam := by
  refine ⟨h, ?_⟩
  dsimp only [PaperFixedBindingCompletePoint] at h
  obtain ⟨_, _, _, _, hfamily⟩ := h
  intro j
  obtain ⟨_, _, _, _, _, hobs, _, _, _, hbound,
    ⟨err, herr, hreciprocal⟩, _, _⟩ := hfamily j
  refine ⟨?_, ?_, err, herr, ?_⟩
  · simpa only [← hagree j] using hobs
  · simpa only [finiteOffsetGap_eq_sequence_gap
      xoffset ξ hagree j] using hbound
  · simpa only [finiteOffsetGap_eq_sequence_gap
      xoffset ξ hagree j] using hreciprocal

/-- The manuscript's arbitrary finite offsets and actual unit prefix
currents, with one printed Equation (aconst) coefficient and analytic
branches shared by all sufficiently small positive split distances. -/
theorem paperFixedBinding_finite_tuple_actual_current_analytic_law
    (m : ℕ) (xoffset : Fin (2*(m+1)+1) → ℝ)
    (hordered : StrictMono xoffset) :
    ∃ ξ : ℕ → ℝ, StrictMono ξ ∧
      (∀ j : Fin (2*(m+1)+1), ξ j.val = xoffset j) ∧
      ∃ a b c : ℕ,
        let r : ℝ := (2 : ℝ)^a
        let t : ℝ := (1/2 : ℝ)^b
        let ε : ℝ := (1/2 : ℝ)^c
        let x₀ := coalescedFiniteState (m+1) r
        let τ : ℝ := t / x₀.D (Fin.last (m+1))
        let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
        let k₀ := relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
        (3*(m+2 : ℝ))/2 ≤ r ∧ 0 < t ∧
          (∀ i : Fin (m+1),
            k₀.gamma i.castSucc * x₀.D i.castSucc = 1) ∧
          k₀.gamma (Fin.last (m+1)) *
            x₀.D (Fin.last (m+1)) = t ∧
          ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
            (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
            0 < paperFixedBindingPrintedCoefficient m r τ ε θ ∧
            (paperFixedBindingPrintedCoefficient m r τ ε θ =
              (let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
                (fromLoadedCoord (loadedCoordOfState x₀))
               let Θ₀ : ℂ :=
                 ((J.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
               let C := 2*r*(coalescedPair (m+1)).1.eval r+
                 (coalescedPair (m+1)).2.eval r
               let M := ((coalescedRawB (m+1) r).eval 1-
                 (coalescedRawD (m+1) r).eval 1) /
                 (coalescedRawD (m+1) r).coeff 0
               (4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1*‖Θ₀‖)) *
                 (∏ i : Fin (m+2),
                   (k₀.b i+k₀.c i)*k₀.alpha i*k₀.gamma i))) ∧
            ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
              ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
                PaperFixedBindingFinitePoint
                  m xoffset ξ r τ ε α K δ θ lam := by
  obtain ⟨ξ, hξ, hagree, a, b, c, hrAdequate, ht, hprefix,
    hfinal, lam, hlam, ha, haconst, α, K, hα, hK, hpoint⟩ :=
    paperFixedBinding_actual_current_all_size_analytic_law
      m xoffset hordered
  refine ⟨ξ, hξ, hagree, a, b, c, hrAdequate, ht, hprefix,
    hfinal, lam, hlam, ha, haconst, α, K, hα, hK, ?_⟩
  filter_upwards [hpoint] with δ hδ
  exact paperFixedBindingCompletePoint_to_finiteTuple
    m xoffset ξ hagree _ _ _ _ _ _ _ _ hδ

end
end PhosphorylationStableCapacity
