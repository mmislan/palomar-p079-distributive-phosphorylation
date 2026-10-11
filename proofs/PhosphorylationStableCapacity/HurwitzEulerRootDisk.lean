module
public import proofs.PhosphorylationStableCapacity.EulerDiskScalar
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Every finite Hurwitz spectrum admits one positive explicit Euler
step that sends all its characteristic roots into the open unit disk.
This is the spectral input for a discrete quadratic Lyapunov sum. -/
theorem isHurwitz_exists_euler_root_step
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : IsHurwitz A) :
    ∃ h : ℝ, 0 < h ∧
      ∀ z : ℂ,
        ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 →
          ‖(1 : ℂ) + (h : ℂ) * z‖ < 1 := by
  classical
  obtain ⟨α, hα, hgap⟩ := isHurwitz_uniform_spectral_gap A hA
  let p : Polynomial ℂ := (A.map (algebraMap ℝ ℂ)).charpoly
  let S : Set ℂ := {z | p.eval z = 0}
  have hp : p ≠ 0 :=
    (A.map (algebraMap ℝ ℂ)).charpoly_monic.ne_zero
  have hfinite : S.Finite := by
    refine (Polynomial.rootSet_finite p ℂ).subset ?_
    intro z hz
    have hz' : p.eval z = 0 := hz
    exact (Polynomial.mem_rootSet_of_ne hp).2 (by simpa using hz')
  rcases S.eq_empty_or_nonempty with hempty | hnonempty
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    have hzS : z ∈ S := hz
    rw [hempty] at hzS
    exact hzS.elim
  · obtain ⟨z₀, hz₀, hmax⟩ :=
      Set.exists_max_image S Complex.normSq hfinite hnonempty
    let R : ℝ := Complex.normSq z₀ + 1
    have hR : 0 < R := by
      dsimp [R]
      have := Complex.normSq_nonneg z₀
      linarith
    let h : ℝ := α / R
    have hh : 0 < h := div_pos hα hR
    have hstep : h * R < 2 * α := by
      have heq : h * R = α := by
        dsimp [h]
        field_simp
      rw [heq]
      linarith
    refine ⟨h, hh, ?_⟩
    intro z hz
    have hzS : z ∈ S := hz
    have hnorm : Complex.normSq z ≤ R := by
      have hle := hmax z hzS
      dsimp [R]
      linarith
    exact euler_root_inside_disk α R h z hh
      (hgap z hz) hnorm hstep

end
end PhosphorylationStableCapacity
