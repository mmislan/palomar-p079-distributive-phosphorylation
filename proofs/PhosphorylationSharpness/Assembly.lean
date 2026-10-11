module
public import proofs.PhosphorylationSharpness.Conversion
public import proofs.PhosphorylationSharpness.Source

@[expose] public section

namespace PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators

theorem dense_inventory {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) (u : ℝ) :
    inventory (fun i : Fin (m+1) => p.coeff i) u=p.eval u := by
  rw [eval_eq_sum_range' (show p.natDegree < m+1 by rw [hp.degree_eq]; omega)]
  exact Fin.sum_univ_eq_sum_range (fun i => p.coeff i*u^i) (m+1)

theorem dense_inventory_product {p : ℝ[X]} {m : ℕ} (hp : DensePositive p m) :
    DensePositive ((1+X)*p) (m+1) := by
  have h := dense_step hp hp 1 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa [add_mul] using h

def rootS (x d : ℝ) : ℝ := (x-1)/(2*ratio x*d)
def rootF (x : ℝ) : ℝ := 4/(x+1)

theorem root_totals (x r b d : ℝ) (hx : 1 < x) (hd : 0 < d)
    (hrel : (x-1)*(b-r*d)=2*(r-ratio x)*d) :
    ratio x*rootF x*(1+rootS x d*b)=2*r ∧
    rootF x*(1+rootS x d*ratio x*d)=2 ∧
    rootS x d*((1+ratio x)*d)+ratio x*rootS x d*rootF x*(b+d)=2*(r+1) := by
  have hu := ratio_pos hx
  have hx1 : x+1 ≠ 0 := by linarith
  have hx2 : x^2-1 ≠ 0 := by nlinarith
  have hd0 := ne_of_gt hd
  dsimp [rootS, rootF, ratio] at hrel ⊢
  constructor
  · field_simp
    nlinarith [hrel]
  constructor
  · field_simp
    ring
  · field_simp
    nlinarith [hrel]

theorem source_from_coefficients {m : ℕ} (B D : ℝ[X])
    (hB : DensePositive B m) (hD : DensePositive D m) (r x : ℝ)
    (hx : 1 < x)
    (hrel : (x-1)*(B.eval (ratio x)-r*D.eval (ratio x))=
      2*(r-ratio x)*D.eval (ratio x)) :
    let A := (1+X)*D
    let t := fun i : Fin (m+2) => A.coeff i
    let b := fun i : Fin (m+1) => B.coeff i
    let d := fun i : Fin (m+1) => D.coeff i
    let z := reconstruct t b d (ratio x) (rootS x (D.eval (ratio x))) (rootF x)
    z.Positive ∧ Equilibrium (realize t b d) z ∧
      totalE z=2*r ∧ totalF z=2 ∧ totalS z=2*(r+1) := by
  dsimp only
  have hA := dense_inventory_product hD
  have ht : ∀ i : Fin (m+2), 0 < (((1+X)*D : ℝ[X]).coeff i) :=
    fun i => hA.1 i (by omega)
  have hb : ∀ i : Fin (m+1), 0 < B.coeff i := fun i => hB.1 i (by omega)
  have hd : ∀ i : Fin (m+1), 0 < D.coeff i := fun i => hD.1 i (by omega)
  have hu := ratio_pos hx
  have hdv := hD.eval_pos hu
  have hs : 0 < rootS x (D.eval (ratio x)) := by
    exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hu) hdv)
  have hf : 0 < rootF x := div_pos (by norm_num) (by linarith)
  refine ⟨reconstruct_positive _ _ _ ht hb hd hu hs hf,
    reconstruct_equilibrium _ _ _ ht hb _ _ _, ?_⟩
  have h := reconstruct_totals (fun i : Fin (m+2) => (((1+X)*D : ℝ[X]).coeff i))
    (fun i : Fin (m+1) => B.coeff i) (fun i : Fin (m+1) => D.coeff i)
    (ratio x) (rootS x (D.eval (ratio x))) (rootF x)
  rw [dense_inventory hB, dense_inventory hD, dense_inventory hA] at h
  simp only [eval_mul, eval_add, eval_one, eval_X] at h
  obtain ⟨he,hf,hs⟩ := root_totals x r (B.eval (ratio x)) (D.eval (ratio x)) hx hdv hrel
  exact ⟨h.1.trans he, h.2.1.trans hf, h.2.2.trans hs⟩

end
end PhosphorylationSharpness
