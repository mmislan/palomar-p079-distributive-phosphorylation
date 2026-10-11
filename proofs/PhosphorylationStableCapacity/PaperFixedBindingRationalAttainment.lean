module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingFiniteTupleLaw
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRationality
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingStableSaddleCorollary
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingAnalyticData
public import proofs.PhosphorylationStableCapacity.DyadicEventuallySelection

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

private theorem rationalReal_two_pow (a : ℕ) :
    RationalReal ((2 : ℝ)^a) := by
  refine ⟨(2 : ℚ)^a, ?_⟩
  push_cast
  rfl

private theorem rationalReal_half_pow (a : ℕ) :
    RationalReal ((1/2 : ℝ)^a) := by
  refine ⟨(1/2 : ℚ)^a, ?_⟩
  push_cast
  rfl

/-- The selected analytic family and its dyadic rational realization share
one coalesced unit-current design, one collection of analytic slow branches,
and one pair of quantitative constants. The all-small-distance law is
retained together with the selected positive rational distance. -/
theorem paperFixedBinding_rational_actual_current_analytic_family_attainment
    (m : ℕ) :
    ∃ a b c : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let x₀ := coalescedFiniteState (m+1) r
      let τ : ℝ := t / x₀.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
      let ξ : ℕ → ℝ := fun j => (j : ℝ)
      let k₀ := relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
      (3*(m+2 : ℝ))/2 ≤ r ∧ 0 < t ∧
        (∀ i : Fin (m+1),
          k₀.gamma i.castSucc * x₀.D i.castSucc = 1) ∧
        k₀.gamma (Fin.last (m+1)) * x₀.D (Fin.last (m+1)) = t ∧
        (∀ j : Fin (2*(m+1)+1),
          arbitrarySplitFiniteState (m+1) ξ r 0 j = x₀) ∧
        paperFixedBindingSplitRates m ξ r 0 ε (Fin.lastCases τ θ) = k₀ ∧
        AnalyticAt ℝ (fun ρ => rateVector
          (paperFixedBindingSplitRates m ξ r ρ ε (Fin.lastCases τ θ))) 0 ∧
        (∀ j : Fin (2*(m+1)+1),
          (∀ i : Fin (m+3), AnalyticAt ℝ
            (fun ρ => (arbitrarySplitFiniteState (m+1) ξ r ρ j).S i) 0) ∧
          AnalyticAt ℝ
            (fun ρ => (arbitrarySplitFiniteState (m+1) ξ r ρ j).E) 0 ∧
          AnalyticAt ℝ
            (fun ρ => (arbitrarySplitFiniteState (m+1) ξ r ρ j).F) 0 ∧
          (∀ i : Fin (m+2), AnalyticAt ℝ
            (fun ρ => (arbitrarySplitFiniteState (m+1) ξ r ρ j).C i) 0) ∧
          (∀ i : Fin (m+2), AnalyticAt ℝ
            (fun ρ => (arbitrarySplitFiniteState (m+1) ξ r ρ j).D i) 0)) ∧
        ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
          (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
          ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
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
            (∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ),
              PaperFixedBindingCompletePoint m ξ r τ ε α K ρ θ lam) ∧
            ∃ d : ℕ,
              let δ : ℝ := (1/2 : ℝ)^d
              let k := paperFixedBindingSplitRates m ξ r δ ε
                (Fin.lastCases τ θ)
              RationalRates k ∧
              (∀ j : Fin (2*(m+1)+1),
                RationalState (arbitrarySplitFiniteState (m+1) ξ r δ j)) ∧
              PaperFixedBindingFinitePoint m
                (fun j : Fin (2*(m+1)+1) => (j.val : ℝ))
                ξ r τ ε α K δ θ lam ∧
              (∀ j : Fin (2*(m+1)+1), Even j.val →
                IsLinearlyStable (2*r) 2 (2*(r+1)) k
                  (toCoordinateSpace
                    (chart (arbitrarySplitFiniteState (m+1) ξ r δ j))) ∧
                IsLocallyAsymptoticallyStableClass
                  (2*r) 2 (2*(r+1)) k
                  (toCoordinateSpace
                    (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))) ∧
              (∀ j : Fin (2*(m+1)+1), Odd j.val →
                IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
                  (toCoordinateSpace
                    (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))) := by
  let ξ : ℕ → ℝ := fun j => (j : ℝ)
  have hξ : StrictMono ξ := by
    intro i j hij
    change (i : ℝ) < (j : ℝ)
    exact_mod_cast hij
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
  obtain ⟨hstateZero, hrateZero⟩ :=
    paperFixedBinding_physical_data_coalesces m ξ r τ ε θ
  obtain ⟨hrateAnalytic, hstateAnalytic⟩ :=
    paperFixedBinding_all_physical_data_analyticAt m ξ r τ ε θ
      (ne_of_gt (lt_trans zero_lt_one hr)) hD hB hbase
  have hprinted := paperFixedBindingPrintedCoefficient_eq_published_aconst
    m r τ ε θ hr hD hk hx heq hET hFT hspec
  obtain ⟨lam, hlam, ha, α, K, hα, hK, hEv⟩ :=
    paperFixedBinding_complete_analytic_law
      m ξ hξ r τ ε θ hθ hr hτ hε hε1
      hD hB hbase hk hx heq hET hFT hspec
  obtain ⟨d, hpoint⟩ := eventually_right_has_halving_index _ hEv
  let δ : ℝ := (1/2 : ℝ)^d
  have hrRat : RationalReal r := rationalReal_two_pow a
  have htRat : RationalReal t := rationalReal_half_pow b
  have hεRat : RationalReal ε := rationalReal_half_pow c
  have hδRat : RationalReal δ := rationalReal_half_pow d
  obtain ⟨hkRat, hsRat⟩ :=
    paperFixedBindingSplit_nat_offsets_actual_currents_rational
      m hrRat htRat hδRat hεRat
  refine ⟨a, b, c, hrAdequate, ht, hprefix, hfinal,
    hstateZero, hrateZero, hrateAnalytic, hstateAnalytic,
    lam, hlam, α, K, hα, hK, ha, hprinted, hEv,
    d, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ξ] using hkRat
  · intro j
    simpa only [ξ] using hsRat j
  · exact paperFixedBindingCompletePoint_to_finiteTuple
      m (fun j : Fin (2*(m+1)+1) => (j.val : ℝ)) ξ
      (fun j => rfl) r τ ε α K δ θ lam hpoint
  · intro j heven
    exact paperFixedBinding_completePoint_even_nonlinear_sink
      m ξ r τ ε α K δ θ lam (lt_trans zero_lt_one hr) hα hpoint j heven
  · intro j hodd
    exact (paperFixedBinding_completePoint_sink_or_saddle
      m ξ r τ ε α K δ θ lam hα hpoint j).2 hodd

/-- One rational rate vector and rational labelled states realize the
same exact full configuration, printed law, signs, analytic slow modes,
and transverse gap for the manuscript's unit-current fixed-binding
family. All four search parameters have finite dyadic indices. -/
theorem paperFixedBinding_rational_actual_current_full_attainment
    (m : ℕ) :
    ∃ a b c d : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let δ : ℝ := (1/2 : ℝ)^d
      let x₀ := coalescedFiniteState (m+1) r
      let τ : ℝ := t / x₀.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1 / x₀.D i.castSucc
      let ξ : ℕ → ℝ := fun j => (j : ℝ)
      let k := paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ θ)
      RationalRates k ∧
        (∀ j : Fin (2*(m+1)+1),
          RationalState (arbitrarySplitFiniteState (m+1) ξ r δ j)) ∧
        ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
          (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
          ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
            PaperFixedBindingFinitePoint m
              (fun j : Fin (2*(m+1)+1) => (j.val : ℝ))
              ξ r τ ε α K δ θ lam ∧
            (∀ j : Fin (2*(m+1)+1), Even j.val →
              IsLinearlyStable (2*r) 2 (2*(r+1)) k
                (toCoordinateSpace
                  (chart (arbitrarySplitFiniteState (m+1) ξ r δ j))) ∧
              IsLocallyAsymptoticallyStableClass
                (2*r) 2 (2*(r+1)) k
                (toCoordinateSpace
                  (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))) ∧
            (∀ j : Fin (2*(m+1)+1), Odd j.val →
              IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
                (toCoordinateSpace
                  (chart (arbitrarySplitFiniteState (m+1) ξ r δ j)))) := by
  obtain ⟨a, b, c, _, _, _, _, _, _, _, _, lam, hlam, α, K, hα, hK,
    _, _, _, d, hkRat, hsRat, hfinite, heven, hodd⟩ :=
    paperFixedBinding_rational_actual_current_analytic_family_attainment m
  exact ⟨a, b, c, d, hkRat, hsRat, lam, hlam, α, K, hα, hK,
    hfinite, heven, hodd⟩

end
end PhosphorylationStableCapacity
