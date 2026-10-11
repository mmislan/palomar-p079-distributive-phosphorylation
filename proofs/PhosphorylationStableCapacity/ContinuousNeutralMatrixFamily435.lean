module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSpectrum
public import proofs.PhosphorylationStableCapacity.SaddleSpectrumOpenness435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- Spectral isolation for a jointly varying parameter in an arbitrary
pseudometric space. The local result is suited to compact current sets,
where the parameter is a current vector paired with a split distance. -/
theorem continuousNeutralMatrix_slowMode_eventually_at
    {α ι : Type*} [PseudoMetricSpace α]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (J : α → Matrix ι ι ℝ) (a : α)
    (hJ : ContinuousAt J a)
    (hspec : SimpleNeutralHurwitzComplement (J a)) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ b : α in 𝓝 a,
        ∃ x : ℝ, |x| < ρ ∧ (J b).charpoly.IsRoot x ∧
          (((J b).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J b).map (algebraMap ℝ ℂ)) →
              z.re < 0 ∨ z = (x : ℂ) := by
  let P : α → ℂ[X] :=
    fun b => ((J b).map (algebraMap ℝ ℂ)).charpoly
  have hN : 1 < Fintype.card ι + 1 := by
    have hc : 0 < Fintype.card ι :=
      Fintype.card_pos_iff.mpr ‹Nonempty ι›
    omega
  have hdegree (b : α) : (P b).natDegree < Fintype.card ι + 1 := by
    simp [P]
  have hcoeffR (n : ℕ) :
      ContinuousAt (fun b => (J b).charpoly.coeff n) a :=
    (continuousAt_matrix_charpoly_coeff (J a) n).comp hJ
  have hcoeff (n : ℕ) :
      ContinuousAt (fun b => (P b).coeff n) a := by
    have hc : ContinuousAt
        (fun b => ((J b).charpoly.coeff n : ℂ)) a :=
      Complex.continuous_ofReal.continuousAt.comp (hcoeffR n)
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using hc
  have hcoeff0 : (J a).charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero _ hspec
  have hcoeff1 : (J a).charpoly.coeff 1 ≠ 0 :=
    simpleNeutral_real_charpoly_coeff_one_ne_zero _ hspec
  have hcoeff1C : (P a).coeff 1 ≠ 0 := by
    simpa only [P, Matrix.charpoly_map, Polynomial.coeff_map,
      ← Complex.coe_algebraMap] using
      (Complex.ofReal_ne_zero.mpr hcoeff1)
  obtain ⟨ρu, hρu, huniq⟩ :=
    complex_polynomial_family_unique_root_near_zero_at
      P (Fintype.card ι + 1) a hN hdegree hcoeff hcoeff1C
  obtain ⟨ρd, hρd, hderiv⟩ :=
    complex_polynomial_derivative_near_nonzero_at
      P (Fintype.card ι + 1) a hdegree hcoeff hcoeff1C
  let ρ := min ρu ρd
  have hρ : 0 < ρ := lt_min hρu hρd
  have hcont (x : ℝ) :
      ContinuousAt (fun b => (J b).charpoly.eval x) a :=
    (continuousAt_matrix_charpoly_eval (J a) x).comp hJ
  have hexists := polynomial_simple_zero_real_root_eventually_at
    (fun b => (J b).charpoly) a hcoeff0 hcoeff1 hcont ρ hρ
  let JC : α → Matrix ι ι ℂ :=
    fun b => (J b).map (algebraMap ℝ ℂ)
  have hJC : ContinuousAt JC a := by
    have hmap : Continuous (fun M : Matrix ι ι ℝ =>
        M.map (algebraMap ℝ ℂ)) := by fun_prop
    exact hmap.continuousAt.comp hJ
  obtain ⟨p, hfactor, _, hleft⟩ := hspec
  have hsource : ∀ z : ℂ,
      z ∈ spectrum ℂ (JC a) → z.re < 0 ∨ z = 0 := by
    intro z hz
    have hzroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    rw [hfactor] at hzroot
    have heval : z * p.eval z = 0 := by
      simpa [JC] using hzroot.eq_zero
    rcases mul_eq_zero.mp heval with hzero | hp
    · exact Or.inr hzero
    · exact Or.inl (hleft z hp)
  have hnear := matrix_family_spectrum_eventually_left_or_near_zero
    JC a hJC hsource ρ hρ
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [huniq, hderiv, hexists, hnear] with
    b huniq hderiv hexists hnear
  obtain ⟨x, hx, hroot⟩ := hexists
  have hxC : ‖(x : ℂ)‖ < ρ := by simpa using hx
  have hrootC : (x : ℂ) ∈ spectrum ℂ (JC b) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [JC, Matrix.charpoly_map, ← Complex.coe_algebraMap]
      using (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  refine ⟨x, hx, hroot,
    hderiv (x : ℂ) (lt_of_lt_of_le hxC (min_le_right ..)), ?_⟩
  intro z hz
  rcases hnear z hz with hzleft | hznear
  · exact Or.inl hzleft
  · exact Or.inr (huniq z (x : ℂ)
      (lt_of_lt_of_le hznear (min_le_left ..))
      (lt_of_lt_of_le hxC (min_le_left ..))
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz)
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hrootC))

end

end PhosphorylationStableCapacity
