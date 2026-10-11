module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingActualCurrentDesign
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompleteLaw
public import proofs.PhosphorylationStableCapacity.FiniteOrderedOffsetExtension

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- All sizes, all finite strictly ordered offset tuples, and the paper's
actual coalesced catalytic current choice `(1,…,1,t)`. The frozen
binding constants are literally one before relaxation. Analytic slow
branches are chosen once, before the common small-δ neighborhood. -/
theorem paperFixedBinding_actual_current_all_size_analytic_law
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
                PaperFixedBindingCompletePoint
                  m ξ r τ ε α K δ θ lam := by
  obtain ⟨ξ, hξ, hagree⟩ :=
    finite_ordered_offsets_extend
      (by omega : 0 < 2*(m+1)+1) xoffset hordered
  obtain ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1, hD, hB,
    hθ, hbase, hk, hx, heq, hET, hFT, hspec,
    hprefix, hfinal⟩ :=
    paperFixedBinding_actual_unit_current_design m
  let r : ℝ := (2 : ℝ)^a
  let t : ℝ := (1/2 : ℝ)^b
  let ε : ℝ := (1/2 : ℝ)^c
  let x₀ := coalescedFiniteState (m+1) r
  let τ : ℝ := t / x₀.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
  obtain ⟨lam, hlam, ha, α, K, hα, hK, hcomplete⟩ :=
    paperFixedBinding_complete_analytic_law m ξ hξ r τ ε θ
      hθ hr hτ hε hε1 hD hB hbase hk hx heq hET hFT hspec
  have hprinted :=
    paperFixedBindingPrintedCoefficient_eq_published_aconst
      m r τ ε θ hr hD hk hx heq hET hFT hspec
  exact ⟨ξ, hξ, hagree, a, b, c, hrAdequate, ht, hprefix, hfinal,
    lam, hlam, ha, hprinted, α, K, hα, hK, hcomplete⟩

end
end PhosphorylationStableCapacity
