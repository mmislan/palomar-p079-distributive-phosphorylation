module
public import proofs.PhosphorylationStableCapacity.HurwitzClassLyapunovCertificate
public import proofs.PhosphorylationStableCapacity.BilinearLyapunovCertificate
public import proofs.PhosphorylationStableCapacity.PositiveForwardExistence

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A Hurwitz restricted Jacobian at a positive interior literal
equilibrium gives full nonlinear local asymptotic class stability. -/
theorem isLinearlyStable_locally_asymptotically_stable
    {n : ℕ} (hn : 1 ≤ n)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : x ∈ classPolytopeStrict n ET FT ST)
    (heq : restrictedFieldEuclid ET FT ST k x = 0)
    (hstable : IsLinearlyStable ET FT ST k x) :
    IsLocallyAsymptoticallyStableClass ET FT ST k x := by
  obtain ⟨B, a, b, q, ha, hb, hq, hcert⟩ :=
    isLinearlyStable_exists_class_lyapunov_certificate
      hn ET FT ST k x hstable
  let C : ℝ := Real.sqrt (b/a)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  have hratio : b ≤ a * C^2 := by
    dsimp [C]
    rw [Real.sq_sqrt (div_nonneg hb.le ha.le)]
    apply le_of_eq
    field_simp [ne_of_gt ha]
  exact class_las_of_quadratic_lyapunov_certificate
    ET FT ST k x heq B a b C q
    ha hb hC hq hratio
    (fun v => ⟨(hcert v).1, (hcert v).2.1⟩)
    (fun v => (hcert v).2.2)
    (positive_class_nearby_forward_existence ET FT ST hET k hk x hx)

end
end PhosphorylationStableCapacity
