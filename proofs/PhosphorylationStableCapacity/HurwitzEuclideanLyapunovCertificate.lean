module
public import proofs.PhosphorylationStableCapacity.HurwitzEuclideanGeneratorPower
public import proofs.PhosphorylationStableCapacity.EulerLyapunovDissipation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Every finite real Hurwitz matrix has a concrete finite-sum
quadratic Lyapunov certificate on its Euclidean coordinate space. -/
theorem isHurwitz_exists_euclidean_lyapunov_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ,
      ∃ b q : ℝ, 0 < b ∧ 0 < q ∧
      ∀ v : EuclideanSpace ℝ ι,
        ‖v‖^2 ≤ B v v ∧
        B v v ≤ b * ‖v‖^2 ∧
        B v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A v) +
          B (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A v) v ≤
            -q * ‖v‖^2 := by
  obtain ⟨h, hh, m, hm, r, hr0, hr1, hcontract⟩ :=
    isHurwitz_exists_euclidean_generator_contracting_power A hA
  let J : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
  let T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := 1 + h • J
  let B := finiteLyapunovForm T m
  let b : ℝ := 1 + ∑ j ∈ Finset.range m, ‖T^j‖^2
  let q : ℝ := (1-r^2)/h
  have hb : 0 < b := by
    dsimp [b]
    have hs : 0 ≤ ∑ j ∈ Finset.range m, ‖T^j‖^2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    linarith
  have hq : 0 < q := by
    dsimp [q]
    apply div_pos _ hh
    have hmul : 0 < (1-r)*(1+r) :=
      mul_pos (by linarith) (by linarith)
    nlinarith
  refine ⟨B, b, q, hb, hq, ?_⟩
  intro v
  refine ⟨?_, ?_, ?_⟩
  · exact finiteLyapunovForm_lower T m hm v
  · calc
      B v v ≤ (∑ j ∈ Finset.range m, ‖T^j‖^2) * ‖v‖^2 :=
        finiteLyapunovForm_upper T m v
      _ ≤ b * ‖v‖^2 := by
        gcongr
        dsimp [b]
        linarith
  · exact finiteLyapunovForm_dissipative_of_contracting_power
      J h m r hh hm hr0 hcontract v

end
end PhosphorylationStableCapacity
