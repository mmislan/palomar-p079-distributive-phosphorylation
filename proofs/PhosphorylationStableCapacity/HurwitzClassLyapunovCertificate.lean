module
public import proofs.PhosphorylationStableCapacity.CoordinateEuclideanEquiv
public import proofs.PhosphorylationStableCapacity.HurwitzEuclideanLyapunovCertificate
public import proofs.PhosphorylationStableCapacity.TransportLyapunovCertificate

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Every nonempty literal phosphorylation class with a Hurwitz
restricted Jacobian has a coercive and strictly dissipative quadratic
Lyapunov form in the manuscript's class coordinates. -/
theorem isLinearlyStable_exists_class_lyapunov_certificate
    {n : ℕ} (hn : 1 ≤ n)
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n)
    (hstable : IsLinearlyStable ET FT ST k x) :
    ∃ B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ,
      ∃ a b q : ℝ, 0 < a ∧ 0 < b ∧ 0 < q ∧
      ∀ v : CoordinateSpace n,
        a * ‖v‖^2 ≤ B v v ∧
        B v v ≤ b * ‖v‖^2 ∧
        B v (restrictedJacobian ET FT ST k x v) +
          B (restrictedJacobian ET FT ST k x v) v ≤
            -q * ‖v‖^2 := by
  let ι := Fin n ⊕ (Fin n ⊕ Fin n)
  have hnonempty : Nonempty ι := ⟨Sum.inl ⟨0, by omega⟩⟩
  let M := restrictedJacobianMatrix ET FT ST k x
  obtain ⟨Be, b, q, hb, hq, hcert⟩ :=
    @isHurwitz_exists_euclidean_lyapunov_certificate ι
      (inferInstance) (inferInstance) hnonempty M hstable
  exact transport_quadratic_lyapunov_certificate
    (coordinateEuclideanEquiv n)
    (restrictedJacobian ET FT ST k x)
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M)
    (coordinateEuclideanEquiv_restrictedJacobian ET FT ST k x)
    Be b q hb hq (fun v => ⟨(hcert v).1, (hcert v).2.1⟩)
    (fun v => (hcert v).2.2)

end
end PhosphorylationStableCapacity
