module
public import proofs.PhosphorylationSharpness.Conversion

@[expose] public section

namespace PhosphorylationSharpness
noncomputable section
open Polynomial

def prescribedPair (x₀ : ℝ) : List (ℝ × ℝ) → ℝ[X] × ℝ[X]
  | [] => (1, C ((x₀-1)/2))
  | ab :: ps =>
      let pq := prescribedPair x₀ ps
      (nextN ab.1 ab.2 pq.1 pq.2, nextJ ab.1 ab.2 pq.1 pq.2)

theorem prescribedPair_dense (x₀ : ℝ) (ps : List (ℝ × ℝ)) (h₀ : 1 < x₀)
    (hps : ∀ ab ∈ ps, 1 < ab.1 ∧ 1 < ab.2) :
    DensePositive (prescribedPair x₀ ps).1 ps.length ∧
      DensePositive (prescribedPair x₀ ps).2 ps.length := by
  induction ps with
  | nil =>
    exact ⟨by simpa [prescribedPair] using dense_constant 1 (by norm_num),
      by simpa [prescribedPair] using dense_constant ((x₀-1)/2) (by linarith)⟩
  | cons ab ps ih =>
    have hh := ih (fun a ha => hps a (by simp [ha]))
    exact next_dense hh.1 hh.2 (hps ab (by simp)).1 (hps ab (by simp)).2

theorem prescribedPair_identity (x₀ x : ℝ) (ps : List (ℝ × ℝ)) :
    (x-1)*(prescribedPair x₀ ps).1.eval (ratio x) -
      2*(prescribedPair x₀ ps).2.eval (ratio x) =
      (x-x₀)*(ps.map (fun ab => (x-ab.1)*(x-ab.2))).prod := by
  induction ps with
  | nil => simp [prescribedPair]; ring
  | cons ab ps ih =>
    change (x-1)*(nextN _ _ _ _).eval _-2*(nextJ _ _ _ _).eval _ = _
    rw [next_identity, ih]
    simp only [List.map_cons, List.prod_cons]
    ring

theorem enzyme_total_pivot (u s f B D : ℝ) :
    (u*f*B)*(1+s*u*D)-(u*(1+s*B))*(f*u*D)=u*f*(B-u*D) := by ring

theorem residual_factorization (x v ell : ℝ) (hx : 1 < x) :
    v*(ell+v)-2*ratio x*ell^2 =
      -2*ratio x*(ell-2*v/(x-1))*(ell+2*v/(x+1)) := by
  have h1 : x-1 ≠ 0 := by linarith
  have h2 : x+1 ≠ 0 := by linarith
  dsimp [ratio]
  field_simp
  ring

theorem distinct_root_product_ne_zero {k : ℕ} (xs : Fin k → ℝ)
    (hinj : Function.Injective xs) (j : Fin k) :
    (∏ i ∈ Finset.univ.erase j, (xs j-xs i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  intro he
  have hij := hinj he
  exact (Finset.mem_erase.mp hi).1 hij.symm

theorem slope_factor_negative (x r nr jr draw : ℝ) (hx : 1 < x)
    (hr : ratio x < r) (hn : 0 < nr) (hj : 0 < jr) (hd : 0 < draw) :
    -16*(1+ratio x)*(jr*x+4*r*nr-jr)/
      ((r-ratio x)*(x+1)^2*draw) < 0 := by
  have hu := ratio_pos hx
  have hr0 : 0 < r := lt_trans hu hr
  have hfac : 0 < jr*x+4*r*nr-jr := by
    have := mul_pos (sub_pos.mpr hx) hj
    have := mul_pos (mul_pos (by norm_num : (0:ℝ)<4) hr0) hn
    nlinarith
  apply div_neg_of_neg_of_pos
  · have h := mul_pos (by linarith : 0 < 1+ratio x) hfac
    nlinarith
  · exact mul_pos (mul_pos (sub_pos.mpr hr) (sq_pos_of_pos (by linarith))) hd

end
end PhosphorylationSharpness
