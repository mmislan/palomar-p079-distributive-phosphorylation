module
public import proofs.PhosphorylationStableCapacity.SourceNormalizedLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

def coalescedRawD (m : ℕ) (r : ℝ) : ℝ[X] :=
  rawD (coalescedPair m).1 (coalescedPair m).2 r

def coalescedRawB (m : ℕ) (r : ℝ) : ℝ[X] :=
  rawB (coalescedPair m).1 (coalescedPair m).2 r

def coalescedFiniteRates (m : ℕ) (r : ℝ) : Rates (m + 1) :=
  realize
    (fun i : Fin (m + 2) => ((1 + X) * coalescedRawD m r).coeff i)
    (fun i : Fin (m + 1) => (coalescedRawB m r).coeff i)
    (fun i : Fin (m + 1) => (coalescedRawD m r).coeff i)

def coalescedFiniteState (m : ℕ) (r : ℝ) : State (m + 1) :=
  reconstruct
    (fun i : Fin (m + 2) => ((1 + X) * coalescedRawD m r).coeff i)
    (fun i : Fin (m + 1) => (coalescedRawB m r).coeff i)
    (fun i : Fin (m + 1) => (coalescedRawD m r).coeff i)
    (ratio 3) (rootS 3 ((coalescedRawD m r).eval (ratio 3))) (rootF 3)

theorem rootS_three (d : ℝ) : rootS 3 d = 1 / d := by
  calc
    rootS 3 d = (2 : ℝ) / (2 * d) := by norm_num [rootS, ratio]
    _ = 1 / d := by
      simpa only [mul_one] using
        (mul_div_mul_left (c := (2 : ℝ)) (1 : ℝ) d (by norm_num))

theorem coalescedFiniteState_EF (m : ℕ) (r : ℝ) :
    (coalescedFiniteState m r).E = 1 ∧
      (coalescedFiniteState m r).F = 1 := by
  norm_num [coalescedFiniteState, reconstruct, ratio, rootF]

/-- The inherited conversion gives a literal positive equilibrium with
totals `(2r,2,2(r+1))` for all sufficiently large `r`. -/
theorem coalescedFiniteState_eventually_equilibrium (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (coalescedFiniteRates m r).Positive ∧
      (coalescedFiniteState m r).Positive ∧
      Equilibrium (coalescedFiniteRates m r) (coalescedFiniteState m r) ∧
      totalE (coalescedFiniteState m r) = 2 * r ∧
      totalF (coalescedFiniteState m r) = 2 ∧
      totalS (coalescedFiniteState m r) = 2 * (r + 1) := by
  have hdense := coalescedPair_dense m
  have hevent := conversion_eventually_positive hdense.1 hdense.2
  filter_upwards [hevent] with r hBD
  have hsource : (3 - 1 : ℝ) *
      (coalescedPair m).1.eval (ratio 3) -
        2 * (coalescedPair m).2.eval (ratio 3) = 0 := by
    have hval := coalescedPair_eval_one m
    norm_num [ratio, hval.1, hval.2]
  have hrel := conversion_root (coalescedPair m).1
    (coalescedPair m).2 r 3 hsource
  have hresult := source_from_coefficients
    (coalescedRawB m r) (coalescedRawD m r)
    hBD.2 hBD.1 r 3 (by norm_num) (by simpa [coalescedRawB,
      coalescedRawD] using hrel)
  have hrates : (coalescedFiniteRates m r).Positive := by
    unfold coalescedFiniteRates
    exact realize_positive _ _ _
      (fun i => (dense_inventory_product hBD.1).1 i (by omega))
      (fun i => hBD.2.1 i (by omega))
      (fun i => hBD.1.1 i (by omega))
  exact ⟨hrates, by simpa only [coalescedFiniteState] using hresult.1,
    by simpa only [coalescedFiniteRates, coalescedFiniteState] using hresult.2.1,
    by simpa only [coalescedFiniteState] using hresult.2.2.1,
    by simpa only [coalescedFiniteState] using hresult.2.2.2.1,
    by simpa only [coalescedFiniteState] using hresult.2.2.2.2⟩

theorem coalescedFiniteState_D_tendsto (m : ℕ) (i : Fin (m + 1)) :
    Tendsto (fun r : ℝ => (coalescedFiniteState m r).D i) atTop
      (𝓝 ((coalescedPair m).2.coeff i / (36 : ℝ) ^ m)) := by
  have hdense := coalescedPair_dense m
  have h := finiteD_tendsto hdense.1 hdense.2 i
  rw [(coalescedPair_eval_one m).2] at h
  convert h using 1
  ext r
  norm_num [coalescedFiniteState, reconstruct, finiteD, coalescedRawD,
    ratio, rootS_three, rootF, div_eq_mul_inv]

theorem coalescedFiniteState_C_scaled_tendsto (m : ℕ)
    (i : Fin (m + 1)) :
    Tendsto (fun r : ℝ => (coalescedFiniteState m r).C i / r) atTop
      (𝓝 (((coalescedPair m).1.coeff i +
        (coalescedPair m).2.coeff i) / (36 : ℝ) ^ m)) := by
  have hdense := coalescedPair_dense m
  have h := finiteB_scaled_tendsto hdense.1 hdense.2 i
  rw [(coalescedPair_eval_one m).2] at h
  convert h using 1
  ext r
  norm_num [coalescedFiniteState, reconstruct, finiteB, coalescedRawD,
    coalescedRawB, ratio, rootS_three, rootF, div_eq_mul_inv]

end
end PhosphorylationStableCapacity
