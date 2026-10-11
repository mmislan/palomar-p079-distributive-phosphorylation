module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactCharpolyFirstOrder435
public import proofs.PhosphorylationStableCapacity.CompactFiniteCoeffBase435
public import proofs.PhosphorylationStableCapacity.FiniteUniformEventBounds435
public import proofs.PhosphorylationStableCapacity.CompactSecantFromCoefficients435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- A single rectangular first-order characteristic secant estimate
for the actual paper frozen-binding rates and every current in a
compact positive full-edge family. -/
theorem paperFixedBinding_compact_secant_first_order
    {n : ℕ} (ET FT ST ε : ℝ)
    (k : ℝ → Rates n) (u : ℝ → CoordinateSpace n)
    (K : Set (Fin n → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hpos0 : (k 0).Positive)
    (hposev : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), (k δ).Positive)
    (hdiff : ∀ w : Fin n → ℝ, (∀ i, 0 < w i) →
      DifferentiableAt ℝ (fun δ =>
        loadedJacobianMatrix ET FT ST
          (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
          (u δ)) 0) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ w ∈ K, ∀ δ x : ℝ, |δ| < η → |x| ≤ 1 →
        |(constantTermSecant
          ((loadedJacobianMatrix ET FT ST
            (relaxRates (paperFixedBindingRates
              (edgeScaledRates w (k δ))) ε) (u δ)).charpoly)).eval x -
          (loadedJacobianMatrix ET FT ST
            (relaxRates (paperFixedBindingRates
              (edgeScaledRates w (k 0))) ε) (u 0)).charpoly.derivative.eval 0| ≤
          C * (|δ| + |x|) := by
  classical
  let ι := Fin n ⊕ (Fin n ⊕ Fin n)
  let N := 3*n+1
  let J (w : Fin n → ℝ) (δ : ℝ) : Matrix ι ι ℝ :=
    loadedJacobianMatrix ET FT ST
      (relaxRates (paperFixedBindingRates (edgeScaledRates w (k δ))) ε)
      (u δ)
  let P (w : Fin n → ℝ) (δ : ℝ) : ℝ[X] := (J w δ).charpoly
  have hper (q : Fin N) : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), ∀ w ∈ K,
        |(P w δ).coeff (q.val+1)-(P w 0).coeff (q.val+1)| ≤
          C * |δ| := by
    simpa only [P, J] using
      paperFixedBinding_compact_charpoly_coeff_first_order
        ET FT ST ε k u K hK hKpos hpos0 hposev hdiff (q.val+1)
  obtain ⟨η₀, A, hη₀, hA, hcoeffRaw⟩ :=
    finite_uniform_first_order_bounds_on_interval
      K N (fun q w δ => (P w δ).coeff (q.val+1)) hper
  have hcenter : ContinuousOn (fun w => J w 0) K :=
    paperFixedBinding_center_loadedJacobian_continuousOn
      ET FT ST ε (k 0) (u 0) K hKpos hpos0
  obtain ⟨M, hM, hMbound⟩ :=
    compact_matrix_charpoly_finite_coeff_upper
      K hK (fun w => J w 0) hcenter N
  have hbase : ∀ w ∈ K, ∀ q < N,
      |(P w 0).coeff (q+1)| ≤ M := by
    intro w hw q hq
    exact hMbound w hw ⟨q, hq⟩
  have hdegree : ∀ w ∈ K, ∀ δ : ℝ,
      (constantTermSecant (P w δ)).natDegree < N := by
    intro w hw δ
    apply constantTermSecant_degree_lt
    change (J w δ).charpoly.natDegree < N
    rw [(J w δ).charpoly_natDegree_eq_dim]
    dsimp [ι, N]
    simp [Fintype.card_sum, Fintype.card_fin]
    omega
  let η := min (η₀/2) 1
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  obtain ⟨C, hC, hrect⟩ :=
    constantTermSecant_uniform_rectangular_of_coefficients
      K P N η A M hη hA.le hM.le hdegree
      (by
        intro w hw δ hδ q hq
        exact hcoeffRaw δ
          (by
            have hsmall : η ≤ η₀/2 := min_le_left ..
            linarith) w hw ⟨q, hq⟩)
      hbase
  refine ⟨η, C, hη, hC, ?_⟩
  intro w hw δ x hδ hx
  have hδ' : |δ| ≤ η := le_of_lt hδ
  simpa only [P, J] using hrect w hw δ x hδ' hx

end

end PhosphorylationStableCapacity
