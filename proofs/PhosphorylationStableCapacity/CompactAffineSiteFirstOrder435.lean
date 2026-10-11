module
public import proofs.PhosphorylationStableCapacity.UniformFiniteProductFirstOrder435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology

/-- An explicit uniform estimate for one factor of the literal frozen-binding
physical rate product.  The current factor is fixed as the split parameter
varies; the source association and conversion rates carry all variation. -/
theorem compact_affine_site_first_order
    {α ι : Type*} (K : Set α)
    (w T : ι → α → ℝ) (c a : ι → ℝ → ℝ)
    (M A B : ℝ) (hM : 1 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hw : ∀ v ∈ K, ∀ i, |w i v| ≤ M)
    (hT : ∀ v ∈ K, ∀ i, |T i v| ≤ M)
    (hbase : ∀ i, |c i 0| ≤ B ∧ |a i 0| ≤ B)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      |δ| ≤ 1 ∧ ∀ i,
        |c i δ-c i 0| ≤ A*|δ| ∧
        |a i δ-a i 0| ≤ A*|δ|) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ v ∈ K, ∀ i,
        |T i v*(1+w i v*c i δ)*a i δ -
          T i v*(1+w i v*c i 0)*a i 0| ≤
            (M*((1+M*(B+A))*A+M*A*B))*|δ| ∧
        |T i v*(1+w i v*c i δ)*a i δ| ≤
            M*(1+M*(B+A))*(B+A) ∧
        |T i v*(1+w i v*c i 0)*a i 0| ≤
            M*(1+M*(B+A))*(B+A) := by
  filter_upwards [hsource] with δ hδ v hv i
  have hMn : 0 ≤ M := by linarith
  have hBA : 0 ≤ B+A := add_nonneg hB hA
  have hcn : |c i δ| ≤ B+A := by
    calc
      |c i δ| = |(c i δ-c i 0)+c i 0| := by congr 1; ring
      _ ≤ |c i δ-c i 0|+|c i 0| := abs_add_le _ _
      _ ≤ A*|δ|+B := add_le_add (hδ.2 i).1 (hbase i).1
      _ ≤ B+A := by nlinarith [hδ.1]
  have han : |a i δ| ≤ B+A := by
    calc
      |a i δ| = |(a i δ-a i 0)+a i 0| := by congr 1; ring
      _ ≤ |a i δ-a i 0|+|a i 0| := abs_add_le _ _
      _ ≤ A*|δ|+B := add_le_add (hδ.2 i).2 (hbase i).2
      _ ≤ B+A := by nlinarith [hδ.1]
  have hfac : |1+w i v*c i δ| ≤ 1+M*(B+A) := by
    calc
      |1+w i v*c i δ| ≤ |(1:ℝ)|+|w i v*c i δ| :=
        abs_add_le _ _
      _ = 1+|w i v| *|c i δ| := by simp [abs_mul]
      _ ≤ 1+M*(B+A) :=
        add_le_add (le_refl (1 : ℝ))
          (mul_le_mul (hw v hv i) hcn (abs_nonneg _) hMn)
  have hfac0 : |1+w i v*c i 0| ≤ 1+M*(B+A) := by
    calc
      |1+w i v*c i 0| ≤ |(1:ℝ)|+|w i v*c i 0| :=
        abs_add_le _ _
      _ = 1+|w i v| *|c i 0| := by simp [abs_mul]
      _ ≤ 1+M*(B+A) :=
        add_le_add (le_refl (1 : ℝ))
          (mul_le_mul (hw v hv i)
            ((hbase i).1.trans (le_add_of_nonneg_right hA))
            (abs_nonneg _) hMn)
  have hfactorNonneg : 0 ≤ 1+M*(B+A) := by positivity
  have hproduct :
      |T i v*(1+w i v*c i δ)*a i δ -
        T i v*(1+w i v*c i 0)*a i 0| ≤
      |T i v| *
        (|1+w i v*c i δ| *|a i δ-a i 0|+
          |w i v| *|c i δ-c i 0| *|a i 0|) := by
    have heq :
        T i v*(1+w i v*c i δ)*a i δ -
          T i v*(1+w i v*c i 0)*a i 0 =
        T i v*((1+w i v*c i δ)*(a i δ-a i 0)+
          w i v*(c i δ-c i 0)*a i 0) := by ring
    rw [heq, abs_mul]
    gcongr
    calc
      |(1+w i v*c i δ)*(a i δ-a i 0)+
          w i v*(c i δ-c i 0)*a i 0| ≤
        |(1+w i v*c i δ)*(a i δ-a i 0)|+
          |w i v*(c i δ-c i 0)*a i 0| := abs_add_le _ _
      _ = _ := by simp [abs_mul, mul_assoc]
  have hfirst :
      |T i v*(1+w i v*c i δ)*a i δ -
        T i v*(1+w i v*c i 0)*a i 0| ≤
        (M*((1+M*(B+A))*A+M*A*B))*|δ| := by
    calc
      _ ≤ |T i v| *
        (|1+w i v*c i δ| *|a i δ-a i 0|+
          |w i v| *|c i δ-c i 0| *|a i 0|) := hproduct
      _ ≤ M*((1+M*(B+A))*(A*|δ|)+M*(A*|δ|)*B) := by
        have hleft : |1+w i v*c i δ| * |a i δ-a i 0| ≤
            (1+M*(B+A))*(A*|δ|) :=
          mul_le_mul hfac (hδ.2 i).2 (abs_nonneg _) hfactorNonneg
        have hmiddle : |w i v| * |c i δ-c i 0| ≤ M*(A*|δ|) :=
          mul_le_mul (hw v hv i) (hδ.2 i).1 (abs_nonneg _) hMn
        have hright : |w i v| * |c i δ-c i 0| * |a i 0| ≤
            M*(A*|δ|)*B :=
          mul_le_mul hmiddle (hbase i).2 (abs_nonneg _)
            (mul_nonneg hMn (mul_nonneg hA (abs_nonneg δ)))
        exact mul_le_mul (hT v hv i) (add_le_add hleft hright)
          (add_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (abs_nonneg _))) hMn
      _ = (M*((1+M*(B+A))*A+M*A*B))*|δ| := by ring
  refine ⟨hfirst, ?_, ?_⟩
  · calc
      |T i v*(1+w i v*c i δ)*a i δ| =
          |T i v| *|1+w i v*c i δ| *|a i δ| := by simp [abs_mul]
      _ ≤ M*(1+M*(B+A))*(B+A) :=
        mul_le_mul
          (mul_le_mul (hT v hv i) hfac (abs_nonneg _) hMn)
          han (abs_nonneg _) (mul_nonneg hMn hfactorNonneg)
  · calc
      |T i v*(1+w i v*c i 0)*a i 0| =
          |T i v| *|1+w i v*c i 0| *|a i 0| := by simp [abs_mul]
      _ ≤ M*(1+M*(B+A))*(B+A) :=
        mul_le_mul
          (mul_le_mul (hT v hv i) hfac0 (abs_nonneg _) hMn)
          ((hbase i).2.trans (le_add_of_nonneg_right hA))
          (abs_nonneg _) (mul_nonneg hMn hfactorNonneg)

end

end PhosphorylationStableCapacity
