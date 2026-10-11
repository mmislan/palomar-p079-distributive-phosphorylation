module
public import proofs.PhosphorylationStableCapacity.RatioCurveSpeciesSmooth

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

/-- Literal kinase-total derivative along the fixed-FT/ST equilibrium
curve, expanded into the species log-ratio slopes. -/
theorem ratioCurve_kinaseTotal_scaled_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    let x := ratioEquilibriumCurve k FT ST u
    let a := ratioCurveSubstrateLogSlope k FT ST u
    let b := ratioCurvePhosphataseLogSlope k FT ST u
    u*deriv (ratioCurveKinaseTotal k FT ST) u =
      x.E*(1+b) +
        ∑ i : Fin n, x.C i*(a+b+((i.val+1:ℕ):ℝ)) := by
  dsimp only
  let q := ratioEquilibriumCurve k FT ST
  have hlocal : (fun v => totalE (q v)) =ᶠ[𝓝 u]
      ratioCurveKinaseTotal k FT ST := by
    have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
    filter_upwards [hpos] with v hv
    obtain ⟨_, _, _, _, hE, _⟩ :=
      ratioEquilibriumCurve_positive_equilibrium_and_totals
        hn k hk FT ST v hFT hST hv
    exact hE
  have hE : DifferentiableAt ℝ (fun v => (q v).E) u :=
    ratioCurve_kinase_differentiableAt hn k hk FT ST u hST hu
  have hC (i : Fin n) :
      DifferentiableAt ℝ (fun v => (q v).C i) u :=
    ratioCurve_kinaseComplex_differentiableAt
      hn k hk FT ST u hST hu i
  have hCsum : HasDerivAt (fun v => ∑ i : Fin n, (q v).C i)
      (∑ i : Fin n, deriv (fun v => (q v).C i) u) u := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hC i).hasDerivAt
  have htotal : deriv (fun v => totalE (q v)) u =
      deriv (fun v => (q v).E) u +
        ∑ i : Fin n, deriv (fun v => (q v).C i) u := by
    change deriv (fun v => (q v).E + ∑ i : Fin n, (q v).C i) u = _
    exact (hE.hasDerivAt.add hCsum).deriv
  rw [← hlocal.deriv_eq, htotal]
  rw [mul_add, Finset.mul_sum,
    ratioCurve_kinase_scaled_deriv hn k hk FT ST u hFT hST hu]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact ratioCurve_kinaseComplex_scaled_deriv
    hn k hk FT ST u hFT hST hu i

/-- The fixed phosphatase total forces the free phosphatase log slope
to balance all phosphatase-complex log slopes. -/
theorem ratioCurve_phosphataseTotal_log_balance {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    let x := ratioEquilibriumCurve k FT ST u
    let a := ratioCurveSubstrateLogSlope k FT ST u
    let b := ratioCurvePhosphataseLogSlope k FT ST u
    x.F*b +
      (∑ i : Fin n, x.D i*(a+b+((i.val+1:ℕ):ℝ))) = 0 := by
  dsimp only
  let q := ratioEquilibriumCurve k FT ST
  have hlocal : (fun v => totalF (q v)) =ᶠ[𝓝 u]
      (fun _ => FT) := by
    have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
    filter_upwards [hpos] with v hv
    obtain ⟨_, _, hF, _, _, _⟩ :=
      ratioEquilibriumCurve_positive_equilibrium_and_totals
        hn k hk FT ST v hFT hST hv
    exact hF
  have hF : DifferentiableAt ℝ (fun v => (q v).F) u :=
    ratioCurve_phosphatase_differentiableAt hn k hk FT ST u hST hu
  have hD (i : Fin n) :
      DifferentiableAt ℝ (fun v => (q v).D i) u :=
    ratioCurve_phosphataseComplex_differentiableAt
      hn k hk FT ST u hST hu i
  have hDsum : HasDerivAt (fun v => ∑ i : Fin n, (q v).D i)
      (∑ i : Fin n, deriv (fun v => (q v).D i) u) u := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hD i).hasDerivAt
  have htotal : deriv (fun v => totalF (q v)) u =
      deriv (fun v => (q v).F) u +
        ∑ i : Fin n, deriv (fun v => (q v).D i) u := by
    change deriv (fun v => (q v).F + ∑ i : Fin n, (q v).D i) u = _
    exact (hF.hasDerivAt.add hDsum).deriv
  have hzero : u*deriv (fun v => totalF (q v)) u = 0 := by
    rw [hlocal.deriv_eq]
    simp
  rw [htotal, mul_add, Finset.mul_sum,
    ratioCurve_phosphatase_scaled_deriv hn k hk FT ST u hFT hST hu]
    at hzero
  convert hzero using 1
  · apply congrArg
      (fun z : ℝ => (q u).F * ratioCurvePhosphataseLogSlope k FT ST u + z)
    apply Finset.sum_congr rfl
    intro i _
    exact (ratioCurve_phosphataseComplex_scaled_deriv
      hn k hk FT ST u hFT hST hu i).symm

/-- The exact fixed substrate total yields the full species-weighted
log-ratio balance, including both bound enzyme families. -/
theorem ratioCurve_substrateTotal_log_balance {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    let x := ratioEquilibriumCurve k FT ST u
    let a := ratioCurveSubstrateLogSlope k FT ST u
    let b := ratioCurvePhosphataseLogSlope k FT ST u
    (∑ j : Fin (n+1), x.S j*(a+(j.val:ℝ))) +
      (∑ i : Fin n, x.C i*(a+b+((i.val+1:ℕ):ℝ))) +
      (∑ i : Fin n, x.D i*(a+b+((i.val+1:ℕ):ℝ))) = 0 := by
  dsimp only
  let q := ratioEquilibriumCurve k FT ST
  have hlocal : (fun v => totalS (q v)) =ᶠ[𝓝 u]
      (fun _ => ST) := by
    have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
    filter_upwards [hpos] with v hv
    obtain ⟨_, _, _, hS, _, _⟩ :=
      ratioEquilibriumCurve_positive_equilibrium_and_totals
        hn k hk FT ST v hFT hST hv
    exact hS
  have hS (j : Fin (n+1)) :
      DifferentiableAt ℝ (fun v => (q v).S j) u :=
    ratioCurve_substrate_differentiableAt hn k hk FT ST u hST hu j
  have hC (i : Fin n) :
      DifferentiableAt ℝ (fun v => (q v).C i) u :=
    ratioCurve_kinaseComplex_differentiableAt
      hn k hk FT ST u hST hu i
  have hD (i : Fin n) :
      DifferentiableAt ℝ (fun v => (q v).D i) u :=
    ratioCurve_phosphataseComplex_differentiableAt
      hn k hk FT ST u hST hu i
  have hSsum : HasDerivAt (fun v => ∑ j : Fin (n+1), (q v).S j)
      (∑ j : Fin (n+1), deriv (fun v => (q v).S j) u) u := by
    apply HasDerivAt.fun_sum
    intro j _
    exact (hS j).hasDerivAt
  have hCsum : HasDerivAt (fun v => ∑ i : Fin n, (q v).C i)
      (∑ i : Fin n, deriv (fun v => (q v).C i) u) u := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hC i).hasDerivAt
  have hDsum : HasDerivAt (fun v => ∑ i : Fin n, (q v).D i)
      (∑ i : Fin n, deriv (fun v => (q v).D i) u) u := by
    apply HasDerivAt.fun_sum
    intro i _
    exact (hD i).hasDerivAt
  have htotal : deriv (fun v => totalS (q v)) u =
      (∑ j : Fin (n+1), deriv (fun v => (q v).S j) u) +
      (∑ i : Fin n, deriv (fun v => (q v).C i) u) +
      (∑ i : Fin n, deriv (fun v => (q v).D i) u) := by
    change deriv (fun v =>
      (∑ j : Fin (n+1), (q v).S j) +
      (∑ i : Fin n, (q v).C i) +
      (∑ i : Fin n, (q v).D i)) u = _
    exact ((hSsum.add hCsum).add hDsum).deriv
  have hzero : u*deriv (fun v => totalS (q v)) u = 0 := by
    rw [hlocal.deriv_eq]
    simp
  rw [htotal, mul_add, mul_add, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum] at hzero
  have hSscaled : (∑ j : Fin (n+1),
      u*deriv (fun v => (q v).S j) u) =
      ∑ j : Fin (n+1), (q u).S j *
        (ratioCurveSubstrateLogSlope k FT ST u+(j.val:ℝ)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact ratioCurve_substrate_scaled_deriv
      hn k hk FT ST u hST hu j
  have hCscaled : (∑ i : Fin n,
      u*deriv (fun v => (q v).C i) u) =
      ∑ i : Fin n, (q u).C i *
        (ratioCurveSubstrateLogSlope k FT ST u +
          ratioCurvePhosphataseLogSlope k FT ST u +
          ((i.val+1:ℕ):ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact ratioCurve_kinaseComplex_scaled_deriv
      hn k hk FT ST u hFT hST hu i
  have hDscaled : (∑ i : Fin n,
      u*deriv (fun v => (q v).D i) u) =
      ∑ i : Fin n, (q u).D i *
        (ratioCurveSubstrateLogSlope k FT ST u +
          ratioCurvePhosphataseLogSlope k FT ST u +
          ((i.val+1:ℕ):ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact ratioCurve_phosphataseComplex_scaled_deriv
      hn k hk FT ST u hFT hST hu i
  rw [hSscaled, hCscaled, hDscaled] at hzero
  exact hzero

end
end PhosphorylationStableCapacity
