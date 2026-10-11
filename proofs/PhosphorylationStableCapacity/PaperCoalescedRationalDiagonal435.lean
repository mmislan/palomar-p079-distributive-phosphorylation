module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingOrderedAdmissibility435
public import proofs.PhosphorylationStableCapacity.FinitePrefixDiagonalLyapunov435
public import proofs.PhosphorylationStableCapacity.FinitePrefixDiagonalCurrentLyapunov435
public import proofs.PhosphorylationStableCapacity.RationalPositiveDefiniteDecision
public import proofs.PhosphorylationStableCapacity.PositiveDefiniteLyapunovHurwitz
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial Filter
open scoped Topology BigOperators

/-- Total rational arithmetic inverse, including the singular case. Unlike
the abstract matrix inverse instance, this producer is computable. -/
def paperRationalAdjugateInverse {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  M.det⁻¹ • M.adjugate

noncomputable section

def paperRationalCoalescedPair (n : ℕ) : ℚ[X] × ℚ[X] :=
  orderedRationalPair n (fun j => (j : ℚ)) 0

def paperRationalLevelWeight (m i : ℕ) : ℚ :=
  ((paperRationalCoalescedPair (m+1)).1.coeff i +
    (paperRationalCoalescedPair (m+1)).2.coeff i)/(36 : ℚ)^(m+1)

def paperRationalYNext (m i : ℕ) : ℚ :=
  (paperRationalCoalescedPair (m+1)).2.coeff i/(36 : ℚ)^(m+1)

def paperRationalYPrev (m i : ℕ) : ℚ :=
  if i = 0 then 0 else paperRationalYNext m (i-1)

def paperRationalFeedbackLevel (m i : ℕ) : ℚ :=
  let v := paperRationalYNext m (m+1)
  (10*paperRationalYPrev m i+(2+v)*paperRationalYNext m i)/
    (2*(7-4*v)*paperRationalLevelWeight m i)

def paperRationalPathWeights (m : ℕ) : Fin (m+2) → ℚ :=
  fun i => paperRationalLevelWeight m i.val

def paperRationalPathFeedback (m : ℕ) : Fin (m+1) → ℚ :=
  fun i => paperRationalFeedbackLevel m i.succ.val-
    paperRationalFeedbackLevel m i.castSucc.val

def paperRationalPathH (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℚ :=
  let d := paperRationalPathWeights m
  fun i j =>
    if i = j then (d i.castSucc)⁻¹+(d i.succ)⁻¹
    else if i.succ = j.castSucc then -(d i.succ)⁻¹
    else if j.succ = i.castSucc then -(d j.succ)⁻¹ else 0

/-- Exactly the paper's P: both Poisson solutions are computed from the
same rational path matrix, and their component ratio forms the diagonal. -/
def paperRationalDiagonalP (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℚ :=
  let G := paperRationalAdjugateInverse (paperRationalPathH m)
  let z := G.mulVec (fun _ => 1)
  let w := G.mulVec (paperRationalPathFeedback m)
  Matrix.diagonal (fun i => w i/z i)

def paperRationalCoalescedD (m : ℕ) (r : ℚ) : ℚ[X] :=
  orderedRationalRawD (m+1) (fun j => (j : ℚ)) r 0

def paperRationalCoalescedB (m : ℕ) (r : ℚ) : ℚ[X] :=
  orderedRationalRawB (m+1) (fun j => (j : ℚ)) r 0

def paperRationalCoalescedS (m : ℕ) (r : ℚ) (i : Fin (m+3)) : ℚ :=
  (((1+X)*paperRationalCoalescedD m r).coeff i.val)/
    (paperRationalCoalescedD m r).eval 1

def paperRationalCoalescedC (m : ℕ) (r : ℚ) (i : Fin (m+2)) : ℚ :=
  (paperRationalCoalescedB m r).coeff i.val/
    (paperRationalCoalescedD m r).eval 1

def paperRationalCoalescedComplexD (m : ℕ) (r : ℚ) (i : Fin (m+2)) : ℚ :=
  (paperRationalCoalescedD m r).coeff i.val/
    (paperRationalCoalescedD m r).eval 1

def paperRationalCLevel (m : ℕ) (r : ℚ) (i : Fin (m+3)) : ℚ :=
  if h : i.val < m+2 then paperRationalCoalescedC m r ⟨i.val,h⟩ else 0

def paperRationalYLevel (m : ℕ) (r : ℚ) (i : Fin (m+3)) : ℚ :=
  if i.val = 0 then 0 else
    paperRationalCoalescedComplexD m r ⟨i.val-1,by have := i.isLt; omega⟩

def paperRationalFullMass (m : ℕ) (r : ℚ) :
    Matrix (Fin (m+3)) (Fin (m+3)) ℚ :=
  fun i j =>
    (if i = j then paperRationalCoalescedS m r i+
      paperRationalCLevel m r i+paperRationalYLevel m r i else 0)-
      paperRationalCLevel m r i*paperRationalCLevel m r j/(2*r)-
      paperRationalYLevel m r i*paperRationalYLevel m r j/2

def paperRationalPrefixForcing (m : ℕ) (j : Fin (m+1)) : Fin (m+3) → ℚ :=
  fun k => (if k = j.succ.castSucc then 1 else 0)-
    (if k = j.castSucc.castSucc then 1 else 0)

def paperRationalInverseResponse (m : ℕ) (r : ℚ)
    (q : Fin (m+3) → ℚ) : Fin (m+3) → ℚ :=
  r • (paperRationalAdjugateInverse (paperRationalFullMass m r)).mulVec q

def paperRationalInverseFeedback (m : ℕ) (r : ℚ)
    (q : Fin (m+3) → ℚ) : ℚ :=
  ∑ j : Fin (m+3),
    (paperRationalYLevel m r j/2-paperRationalCLevel m r j/(2*r))*
      paperRationalInverseResponse m r q j

/-- The actual finite normalized prefix `r*A_r`, not its limiting path block.
The factor r comes from the scaled inverse-response tangent. -/
def paperRationalPrefixA (m : ℕ) (r : ℚ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℚ :=
  fun i j =>
    let q := paperRationalPrefixForcing m j
    paperRationalInverseResponse m r q i.castSucc.castSucc-
      paperRationalInverseResponse m r q i.succ.castSucc+
      paperRationalInverseFeedback m r q

def paperRationalPrefixQ (m : ℕ) (r : ℚ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℚ :=
  -((paperRationalPrefixA m r).transpose*paperRationalDiagonalP m+
    paperRationalDiagonalP m*paperRationalPrefixA m r)

/-- Literal, unscaled inverse-response prefix. It uses the same physical
coalesced mass, forcing columns and feedback as the normalized matrix. -/
def paperRationalLiteralPrefixA (m : ℕ) (r : ℚ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℚ :=
  r⁻¹ • paperRationalPrefixA m r

def paperRationalLiteralPrefixQ (m : ℕ) (r : ℚ) :
    Matrix (Fin (m+1)) (Fin (m+1)) ℚ :=
  -((paperRationalLiteralPrefixA m r).transpose*paperRationalDiagonalP m+
    paperRationalDiagonalP m*paperRationalLiteralPrefixA m r)

def paperRationalPrefixDiagonalAccepts (m a : ℕ) : Bool :=
  rationalFixedLyapunovAccepts
    (paperRationalLiteralPrefixA m ((2 : ℚ)^a)) (paperRationalDiagonalP m)
    (paperRationalLiteralPrefixQ m ((2 : ℚ)^a))

theorem paperRationalAdjugateInverse_cast {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) :
    (paperRationalAdjugateInverse M).map (algebraMap ℚ ℝ) =
      (M.map (algebraMap ℚ ℝ))⁻¹ := by
  have hdet := (algebraMap ℚ ℝ).map_det M
  have hadj := (algebraMap ℚ ℝ).map_adjugate M
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  ext i j
  have hadjij : ((M.adjugate i j : ℚ) : ℝ) =
      (M.map (algebraMap ℚ ℝ)).adjugate i j :=
    congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hadj
  change (algebraMap ℚ ℝ) (M.det⁻¹ * M.adjugate i j) =
    (M.map (algebraMap ℚ ℝ)).det⁻¹ * (M.map (algebraMap ℚ ℝ)).adjugate i j
  rw [map_mul, map_inv₀, hdet]
  exact congrArg (fun u : ℝ => (M.map (algebraMap ℚ ℝ)).det⁻¹ * u) hadjij

theorem paperRationalCoalescedPair_cast (n : ℕ) :
    ((paperRationalCoalescedPair n).1.map (algebraMap ℚ ℝ) = (coalescedPair n).1) ∧
    ((paperRationalCoalescedPair n).2.map (algebraMap ℚ ℝ) = (coalescedPair n).2) := by
  simpa only [paperRationalCoalescedPair, Rat.cast_zero,
    arbitrarySplitPair_zero_eq_coalesced] using
      orderedRationalPair_cast n (fun j => (j : ℚ)) 0

theorem paperRationalLevelWeight_cast (m i : ℕ) :
    (paperRationalLevelWeight m i : ℝ) = coalescedLevelWeight m i := by
  obtain ⟨hp,hq⟩ := paperRationalCoalescedPair_cast (m+1)
  have hpc := congrArg (fun p : ℝ[X] => p.coeff i) hp
  have hqc := congrArg (fun p : ℝ[X] => p.coeff i) hq
  simp only [Polynomial.coeff_map, eq_ratCast] at hpc hqc
  simp only [paperRationalLevelWeight, coalescedLevelWeight,
    Rat.cast_div, Rat.cast_add, Rat.cast_pow,
    Rat.cast_ofNat, hpc, hqc]

theorem paperRationalYNext_cast (m i : ℕ) :
    (paperRationalYNext m i : ℝ) = coalescedYNext m i := by
  have hq := congrArg (fun p : ℝ[X] => p.coeff i)
    (paperRationalCoalescedPair_cast (m+1)).2
  simp only [Polynomial.coeff_map, eq_ratCast] at hq
  simp only [paperRationalYNext, coalescedYNext,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, hq]

theorem paperRationalFeedbackLevel_cast (m i : ℕ) :
    (paperRationalFeedbackLevel m i : ℝ) = coalescedFeedbackLevel m i := by
  by_cases hi : i = 0 <;> simp [paperRationalFeedbackLevel, coalescedFeedbackLevel, hi,
    paperRationalYPrev, coalescedYPrev, coalescedV,
    paperRationalYNext_cast, paperRationalLevelWeight_cast]

theorem paperRationalPathH_cast (m : ℕ) :
    (paperRationalPathH m).map (algebraMap ℚ ℝ) =
      pathH (coalescedPathWeights m) := by
  ext i j
  simp only [Matrix.map, paperRationalPathH, paperRationalPathWeights,
    pathH, coalescedPathWeights, eq_ratCast]
  split_ifs <;> simp_all [paperRationalLevelWeight_cast]

theorem paperRationalPathFeedback_cast (m : ℕ) (i : Fin (m+1)) :
    (paperRationalPathFeedback m i : ℝ) = coalescedPathEdgeFeedback m i := by
  rw [coalescedPathEdgeFeedback, pathIncidence_mulVec]
  simp [paperRationalPathFeedback, coalescedPathFeedback,
    paperRationalFeedbackLevel_cast]

/-- The computable rational P casts to exactly the printed real P, with
the denominator identified with the already proved positive path vector. -/
theorem paperRationalDiagonalP_cast (m : ℕ) :
    (paperRationalDiagonalP m).map (algebraMap ℚ ℝ) =
      Matrix.diagonal (fun i : Fin (m+1) =>
        ((pathH (coalescedPathWeights m))⁻¹.mulVec
          (coalescedPathEdgeFeedback m)) i /
        pathVectorFin (coalescedPathWeights m) i) := by
  let H := pathH (coalescedPathWeights m)
  let z := pathVectorFin (coalescedPathWeights m)
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr
    (pathH_posDef_of_positive (by omega : 0 < m+1)
      (coalescedPathWeights m) (coalescedPathWeights_pos m)).det_pos.ne'
  have hz : H.mulVec z = (fun _ => 1) := by
    funext i
    exact pathVectorFin_action (by omega : 0 < m+1)
      (coalescedPathWeights m) (coalescedPathWeights_pos m) i
  have hinvz : H⁻¹.mulVec (fun _ => 1) = z := by
    rw [← hz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H hunit,
      Matrix.one_mulVec]
  have hG := paperRationalAdjugateInverse_cast (paperRationalPathH m)
  rw [paperRationalPathH_cast] at hG
  have hzc (i : Fin (m+1)) :
      (((paperRationalAdjugateInverse (paperRationalPathH m)).mulVec
        (fun _ => 1)) i : ℝ) = z i := by
    have h := (algebraMap ℚ ℝ).map_mulVec
      (paperRationalAdjugateInverse (paperRationalPathH m)) (fun _ => 1) i
    simpa only [hG, Function.comp_def, map_one, eq_ratCast, H, hinvz] using h
  have hwc (i : Fin (m+1)) :
      (((paperRationalAdjugateInverse (paperRationalPathH m)).mulVec
        (paperRationalPathFeedback m)) i : ℝ) =
      (H⁻¹.mulVec (coalescedPathEdgeFeedback m)) i := by
    have h := (algebraMap ℚ ℝ).map_mulVec
      (paperRationalAdjugateInverse (paperRationalPathH m))
      (paperRationalPathFeedback m) i
    have hf : (algebraMap ℚ ℝ) ∘ paperRationalPathFeedback m =
        coalescedPathEdgeFeedback m :=
      funext (paperRationalPathFeedback_cast m)
    simpa only [hG, hf, H, eq_ratCast] using h
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [paperRationalDiagonalP, Matrix.map_apply,
      Matrix.diagonal_apply_eq, eq_ratCast, Rat.cast_div, hzc, hwc, H, z]
  · simp [paperRationalDiagonalP, hij]

theorem paperRationalCoalescedD_cast (m : ℕ) (r : ℚ) :
    (paperRationalCoalescedD m r).map (algebraMap ℚ ℝ) =
      coalescedRawD (m+1) (r : ℝ) := by
  simpa [paperRationalCoalescedD, arbitrarySplitRawD,
    coalescedRawD, arbitrarySplitPair_zero_eq_coalesced] using
      orderedRationalRawD_cast (m+1) (fun j => (j : ℚ)) r 0

theorem paperRationalCoalescedB_cast (m : ℕ) (r : ℚ) :
    (paperRationalCoalescedB m r).map (algebraMap ℚ ℝ) =
      coalescedRawB (m+1) (r : ℝ) := by
  simpa [paperRationalCoalescedB, arbitrarySplitRawB,
    coalescedRawB, arbitrarySplitPair_zero_eq_coalesced] using
      orderedRationalRawB_cast (m+1) (fun j => (j : ℚ)) r 0

private theorem paperRationalCoalescedD_eval_cast (m : ℕ) (r : ℚ) :
    (((paperRationalCoalescedD m r).eval (1 : ℚ) : ℚ) : ℝ) =
      (coalescedRawD (m+1) (r : ℝ)).eval 1 := by
  have h := congrArg (fun p : ℝ[X] => p.eval 1)
    (paperRationalCoalescedD_cast m r)
  have hev : ((paperRationalCoalescedD m r).map (algebraMap ℚ ℝ)).eval 1 =
      (((paperRationalCoalescedD m r).eval (1 : ℚ) : ℚ) : ℝ) := by
    simpa only [map_one, eq_ratCast] using
      (Polynomial.eval_map_apply (p := paperRationalCoalescedD m r)
        (f := algebraMap ℚ ℝ) (1 : ℚ))
  exact hev.symm.trans h

theorem paperRationalCoalesced_species_cast (m : ℕ) (r : ℚ) :
    (∀ i, (paperRationalCoalescedS m r i : ℝ) =
      (coalescedFiniteState (m+1) (r : ℝ)).S i) ∧
    (∀ i, (paperRationalCoalescedC m r i : ℝ) =
      (coalescedFiniteState (m+1) (r : ℝ)).C i) ∧
    (∀ i, (paperRationalCoalescedComplexD m r i : ℝ) =
      (coalescedFiniteState (m+1) (r : ℝ)).D i) := by
  have hD := paperRationalCoalescedD_cast m r
  have hB := paperRationalCoalescedB_cast m r
  have hDc (i : ℕ) := congrArg (fun p : ℝ[X] => p.coeff i) hD
  have hBc (i : ℕ) := congrArg (fun p : ℝ[X] => p.coeff i) hB
  have hT : (((1+X)*paperRationalCoalescedD m r).map (algebraMap ℚ ℝ)) =
      (1+X)*coalescedRawD (m+1) (r : ℝ) := by simp [hD]
  have hTc (i : ℕ) := congrArg (fun p : ℝ[X] => p.coeff i) hT
  simp only [Polynomial.coeff_map, eq_ratCast] at hTc
  refine ⟨?_, ?_, ?_⟩ <;> intro i
  · simp only [paperRationalCoalescedS, Rat.cast_div,
      paperRationalCoalescedD_eval_cast, coalescedFiniteState,
      reconstruct, rootS_three]
    norm_num [ratio, rootF, hTc i.val, div_eq_mul_inv]
  · simp only [paperRationalCoalescedC, Rat.cast_div,
      paperRationalCoalescedD_eval_cast, coalescedFiniteState,
      reconstruct, rootS_three]
    norm_num [ratio, rootF, ← hBc i.val, Polynomial.coeff_map, eq_ratCast, div_eq_mul_inv]
  · simp only [paperRationalCoalescedComplexD, Rat.cast_div,
      paperRationalCoalescedD_eval_cast, coalescedFiniteState,
      reconstruct, rootS_three]
    norm_num [ratio, rootF, ← hDc i.val, Polynomial.coeff_map, eq_ratCast, div_eq_mul_inv]

theorem paperRational_levels_cast (m : ℕ) (r : ℚ) :
    (∀ i, (paperRationalCLevel m r i : ℝ) = coalescedFiniteCLevel m (r : ℝ) i) ∧
    (∀ i, (paperRationalYLevel m r i : ℝ) = coalescedFiniteYLevel m (r : ℝ) i) := by
  have hspecies := paperRationalCoalesced_species_cast m r
  constructor <;> intro i
  · by_cases hi : i.val < m+2 <;> simp [paperRationalCLevel, coalescedFiniteCLevel, hi, hspecies.2.1]
  · by_cases hi : i.val = 0 <;> simp [paperRationalYLevel, coalescedFiniteYLevel, hi, hspecies.2.2]

theorem paperRationalFullMass_cast (m : ℕ) (r : ℚ) :
    (paperRationalFullMass m r).map (algebraMap ℚ ℝ) =
      coalescedFullMass m (r : ℝ) := by
  have hs := (paperRationalCoalesced_species_cast m r).1
  obtain ⟨hc,hy⟩ := paperRational_levels_cast m r
  ext i j
  by_cases hij : i = j <;> simp [Matrix.map, paperRationalFullMass, coalescedFullMass, hij, hs, hc, hy]

theorem paperRationalInverseResponse_cast (m : ℕ) (r : ℚ)
    (q : Fin (m+3) → ℚ) (i : Fin (m+3)) :
    (paperRationalInverseResponse m r q i : ℝ) =
      coalescedInverseResponse m (r : ℝ) (fun k => (q k : ℝ)) i := by
  have hG := paperRationalAdjugateInverse_cast (paperRationalFullMass m r)
  rw [paperRationalFullMass_cast] at hG
  have h := (algebraMap ℚ ℝ).map_mulVec
    (paperRationalAdjugateInverse (paperRationalFullMass m r)) q i
  simpa only [paperRationalInverseResponse, coalescedInverseResponse,
    Pi.smul_apply, smul_eq_mul, Rat.cast_mul, hG, Function.comp_def, eq_ratCast] using
      congrArg (fun u : ℝ => (r : ℝ)*u) h

theorem paperRationalPrefixA_cast (m : ℕ) (r : ℚ) :
    (paperRationalPrefixA m r).map (algebraMap ℚ ℝ) =
      coalescedPrefixEdgeActionMatrix m (r : ℝ) := by
  have hforcing (j : Fin (m+1)) :
      (fun k => (paperRationalPrefixForcing m j k : ℝ)) =
        coalescedPrefixEdgeForcing m j := by
    funext k
    simp only [paperRationalPrefixForcing, coalescedPrefixEdgeForcing]
    split_ifs <;> norm_num
  obtain ⟨hc,hy⟩ := paperRational_levels_cast m r
  ext i j
  simp only [paperRationalPrefixA, Matrix.map_apply, eq_ratCast, Rat.cast_add,
    Rat.cast_sub, paperRationalInverseResponse_cast, hforcing,
    coalescedPrefixEdgeActionMatrix, coalescedNormalizedEdgeAction]
  congr 1
  simp only [paperRationalInverseFeedback, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, hc, hy,
    paperRationalInverseResponse_cast, hforcing, coalescedInverseFeedback]

theorem paperRationalPrefixQ_cast (m : ℕ) (r : ℚ) :
    (paperRationalPrefixQ m r).map (algebraMap ℚ ℝ) =
      -((coalescedPrefixEdgeActionMatrix m (r : ℝ)).transpose*
        (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)+
        (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)*
          coalescedPrefixEdgeActionMatrix m (r : ℝ)) := by
  have hA (i j : Fin (m+1)) := congrArg
    (fun A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ => A i j)
    (paperRationalPrefixA_cast m r)
  simp only [Matrix.map_apply, eq_ratCast] at hA
  ext i j
  simp only [paperRationalPrefixQ, Matrix.map_apply, Matrix.neg_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, eq_ratCast,
    Rat.cast_neg, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, hA]

theorem paperRationalLiteralPrefixA_cast (m : ℕ) (r : ℚ) :
    (paperRationalLiteralPrefixA m r).map (algebraMap ℚ ℝ) =
      (r : ℝ)⁻¹ • coalescedPrefixEdgeActionMatrix m (r : ℝ) := by
  have hA (i j : Fin (m+1)) := congrArg
    (fun A : Matrix (Fin (m+1)) (Fin (m+1)) ℝ => A i j)
    (paperRationalPrefixA_cast m r)
  simp only [Matrix.map_apply, eq_ratCast] at hA
  ext i j
  simp only [paperRationalLiteralPrefixA, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul, eq_ratCast, Rat.cast_mul, Rat.cast_inv, hA]

/-- The literal prefix is the actual loaded current derivative with each
row divided by its own coalesced D complex. This fixes the coordinate
convention and the r normalization by an exact finite-parameter identity. -/
theorem paperRationalLiteralPrefixA_cast_loaded
    (m : ℕ) (r : ℚ) (h : orderedRationalPrefixAdmits m r = true) :
    (paperRationalLiteralPrefixA m r).map (algebraMap ℚ ℝ) =
      Matrix.diagonal (fun i : Fin (m+1) =>
        1/(coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc)*
        coalescedPrefixLoadedMatrix m (r : ℝ) := by
  have hx := orderedRationalPrefixAdmits_coalesced_positive m r h
  have hr : 0 < (r : ℝ) := lt_trans zero_lt_one
    ((orderedRationalPrefixAdmits_iff m r).mp h).1
  rw [paperRationalLiteralPrefixA_cast]
  ext i j
  have hd : (coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc ≠ 0 :=
    ne_of_gt (hx.2.2.2.2 i.castSucc)
  have hcurrent := coalescedPrefixCurrentMatrix_eq_r_mul_loaded m (r : ℝ) i j
  have hfactor : coalescedPrefixCurrentMatrix m (r : ℝ) i j =
      (coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc*
        coalescedPrefixEdgeActionMatrix m (r : ℝ) i j := rfl
  rw [hfactor] at hcurrent
  have heq : coalescedPrefixEdgeActionMatrix m (r : ℝ) i j =
      (r : ℝ)*coalescedPrefixLoadedMatrix m (r : ℝ) i j/
        (coalescedFiniteState (m+1) (r : ℝ)).D i.castSucc := by
    apply (eq_div_iff_mul_eq hd).mpr
    simpa only [mul_comm] using hcurrent
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul]
  rw [heq]
  field_simp [ne_of_gt hr, hd]

/-- Positive-r normalization changes Q by the same scalar and leaves
the literal printed P intact. -/
theorem paperRationalLiteralPrefixQ_eq (m : ℕ) (r : ℚ) :
    paperRationalLiteralPrefixQ m r = r⁻¹ • paperRationalPrefixQ m r := by
  let A := paperRationalPrefixA m r
  let P := paperRationalDiagonalP m
  have hfirst (i j : Fin (m+1)) :
      (∑ k, (r⁻¹*A k i)*P k j) = r⁻¹*(∑ k, A k i*P k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsecond (i j : Fin (m+1)) :
      (∑ k, P i k*(r⁻¹*A k j)) = r⁻¹*(∑ k, P i k*A k j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  ext i j
  simp only [paperRationalLiteralPrefixQ, paperRationalLiteralPrefixA,
    paperRationalPrefixQ, Matrix.neg_apply, Matrix.add_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hfirst, hsecond]
  ring

/-- Testing the normalized and literal prefix is equivalent for positive r;
this preserves the specified paper P instead of choosing another certificate. -/
theorem paperRationalPrefixDiagonal_test_equiv (m : ℕ) (r : ℚ) (hr : 0 < r) :
    rationalFixedLyapunovAccepts
      (paperRationalLiteralPrefixA m r) (paperRationalDiagonalP m)
      (paperRationalLiteralPrefixQ m r) = true ↔
    rationalFixedLyapunovAccepts
      (paperRationalPrefixA m r) (paperRationalDiagonalP m)
      (paperRationalPrefixQ m r) = true := by
  rw [rationalFixedLyapunovAccepts_iff, rationalFixedLyapunovAccepts_iff]
  have hscale : (paperRationalLiteralPrefixQ m r).PosDef ↔
      (paperRationalPrefixQ m r).PosDef := by
    rw [paperRationalLiteralPrefixQ_eq]
    constructor
    · intro h
      have hs := h.smul hr
      simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul] using hs
    · intro h
      exact h.smul (inv_pos.mpr hr)
  constructor
  · rintro ⟨hP,hQ,_⟩
    exact ⟨hP,hscale.mp hQ,by simp only [paperRationalPrefixQ,neg_neg]⟩
  · rintro ⟨hP,hQ,_⟩
    exact ⟨hP,hscale.mpr hQ,by simp only [paperRationalLiteralPrefixQ,neg_neg]⟩

/-- The first prescribed doubling loop eventually accepts this very P
on this actual finite prefix, after physical coefficient admission. -/
theorem paperRationalPrefixDiagonal_eventually_accepts (m : ℕ) :
    ∀ᶠ a : ℕ in atTop, paperRationalPrefixDiagonalAccepts m a = true := by
  have ht : Tendsto (fun a : ℕ => (2 : ℝ)^a) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hgood := ht.eventually
    (coalescedPrefixEdgeActionMatrix_eventually_fixed_diagonal_lyapunov m)
  filter_upwards [hgood] with a ha
  apply (paperRationalPrefixDiagonal_test_equiv m ((2 : ℚ)^a)
    (pow_pos (by norm_num) a)).mpr
  apply (rationalFixedLyapunovAccepts_iff _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (rationalMatrix_posDef_cast_iff (paperRationalDiagonalP m)).mp
    rw [paperRationalDiagonalP_cast]
    exact ha.1
  · apply (rationalMatrix_posDef_cast_iff
      (paperRationalPrefixQ m ((2 : ℚ)^a))).mp
    rw [paperRationalPrefixQ_cast, paperRationalDiagonalP_cast]
    simpa using ha.2
  · simp only [paperRationalPrefixQ, neg_neg]

theorem paperRationalPrefixDiagonal_first_admitted_success (m : ℕ) :
    ∃ a, FirstAcceptedIndex
      (fun a => orderedRationalPrefixAdmits m ((2 : ℚ)^a) &&
        paperRationalPrefixDiagonalAccepts m a) a := by
  exact orderedRational_admitted_prefix_first_acceptance m
    (paperRationalPrefixDiagonalAccepts m)
    (paperRationalPrefixDiagonal_eventually_accepts m)

theorem paperRationalPrefixDiagonal_accepted_actual_hurwitz
    (m a : ℕ) (h : paperRationalPrefixDiagonalAccepts m a = true) :
    IsHurwitz (((2 : ℝ)^a)⁻¹ • coalescedPrefixEdgeActionMatrix m ((2 : ℝ)^a)) := by
  have hh := rationalFixedLyapunovAccepts_hurwitz
    (paperRationalLiteralPrefixA m ((2 : ℚ)^a)) (paperRationalDiagonalP m)
    (paperRationalLiteralPrefixQ m ((2 : ℚ)^a)) h
  rw [paperRationalLiteralPrefixA_cast] at hh
  simpa using hh

theorem paperRationalLiteralPrefixQ_cast (m : ℕ) (r : ℚ) :
    (paperRationalLiteralPrefixQ m r).map (algebraMap ℚ ℝ) =
      -(((paperRationalLiteralPrefixA m r).map (algebraMap ℚ ℝ)).transpose*
          (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)+
        (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)*
          (paperRationalLiteralPrefixA m r).map (algebraMap ℚ ℝ)) := by
  ext i j
  simp only [paperRationalLiteralPrefixQ, Matrix.map_apply, Matrix.neg_apply,
    Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, eq_ratCast,
    Rat.cast_neg, Rat.cast_add, Rat.cast_sum, Rat.cast_mul]

/-- Undoing a positive diagonal row normalization is valid here because
the prescribed Lyapunov matrix is itself diagonal. The loaded certificate
is explicitly `P*diag(1/d)`; its dissipation is exactly the original one. -/
theorem paper_diagonal_row_denormalization_lyapunov
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) (p d : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hd : ∀ i, 0 < d i) :
    let P := Matrix.diagonal p
    let A := Matrix.diagonal (fun i => 1/d i)*L
    let PL := P*Matrix.diagonal (fun i => 1/d i)
    PL.PosDef ∧ L.transpose*PL+PL*L = A.transpose*P+P*A := by
  intro P A PL
  have hPL : PL = Matrix.diagonal (fun i => p i/d i) := by
    ext i j
    simp [PL, P, Matrix.diagonal_mul_diagonal, div_eq_mul_inv]
  constructor
  · rw [hPL]
    exact Matrix.posDef_diagonal_iff.mpr (fun i => div_pos (hp i) (hd i))
  · ext i j
    simp only [hPL, A, P, Matrix.add_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.transpose_apply]
    ring

/-- Exact certificate on the actual loaded prefix. Physical admission
supplies positive coalesced D complexes; the accepted finite test supplies
the same printed P and Q. No appeal to general row-scaling invariance is used.

Coordinate convention: the rational test matrix is `diag(1/D_i)*L`,
its normalized form is `r*diag(1/D_i)*L`, and `L` below is the literal
`coalescedPrefixLoadedMatrix`. Its explicit diagonal certificate is
the prescribed paper P multiplied by `diag(1/D_i)`. -/
theorem paperRationalPrefixDiagonal_accepted_loaded_certificate
    (m a : ℕ)
    (hadmit : orderedRationalPrefixAdmits m ((2 : ℚ)^a) = true)
    (haccept : paperRationalPrefixDiagonalAccepts m a = true) :
    let r : ℝ := (2 : ℝ)^a
    let L := coalescedPrefixLoadedMatrix m r
    let P := (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)
    let Q := (paperRationalLiteralPrefixQ m ((2 : ℚ)^a)).map (algebraMap ℚ ℝ)
    let PL := P*Matrix.diagonal (fun i : Fin (m+1) =>
      1/(coalescedFiniteState (m+1) r).D i.castSucc)
    Q.PosDef ∧ PL.PosDef ∧ L.transpose*PL+PL*L = -Q ∧ IsHurwitz L := by
  intro r L P Q PL
  obtain ⟨hPq,hQq,_⟩ :=
    (rationalFixedLyapunovAccepts_iff
      (paperRationalLiteralPrefixA m ((2 : ℚ)^a)) (paperRationalDiagonalP m)
      (paperRationalLiteralPrefixQ m ((2 : ℚ)^a))).mp haccept
  have hP : P.PosDef := (rationalMatrix_posDef_cast_iff _).mpr hPq
  have hQ : Q.PosDef := (rationalMatrix_posDef_cast_iff _).mpr hQq
  let p : Fin (m+1) → ℝ := fun i =>
    ((pathH (coalescedPathWeights m))⁻¹.mulVec
      (coalescedPathEdgeFeedback m)) i/pathVectorFin (coalescedPathWeights m) i
  let d : Fin (m+1) → ℝ := fun i =>
    (coalescedFiniteState (m+1) r).D i.castSucc
  have hPeq : P = Matrix.diagonal p := paperRationalDiagonalP_cast m
  have hp : ∀ i, 0 < p i := Matrix.posDef_diagonal_iff.mp (hPeq ▸ hP)
  have hx := orderedRationalPrefixAdmits_coalesced_positive m ((2 : ℚ)^a) hadmit
  have hd : ∀ i, 0 < d i := by
    intro i
    simpa [d, r] using hx.2.2.2.2 i.castSucc
  have hAeq : (paperRationalLiteralPrefixA m ((2 : ℚ)^a)).map
      (algebraMap ℚ ℝ) = Matrix.diagonal (fun i => 1/d i)*L := by
    simpa [d, L, r] using
      paperRationalLiteralPrefixA_cast_loaded m ((2 : ℚ)^a) hadmit
  have hQeq : Q = -((Matrix.diagonal (fun i => 1/d i)*L).transpose*P+
      P*(Matrix.diagonal (fun i => 1/d i)*L)) := by
    simpa only [hAeq, P, Q] using
      paperRationalLiteralPrefixQ_cast m ((2 : ℚ)^a)
  obtain ⟨hPL,hidentity⟩ := paper_diagonal_row_denormalization_lyapunov L p d hp hd
  have hPLactual : PL.PosDef := by
    simpa only [PL, hPeq, d] using hPL
  have hlyap : L.transpose*PL+PL*L = -Q := by
    rw [hQeq, neg_neg]
    simpa only [PL, hPeq, d] using hidentity
  exact ⟨hQ,hPLactual,hlyap,
    hurwitz_of_posDef_lyapunov L PL Q hPLactual hQ hlyap⟩

/-- The first physically admitted success of the actual specified-P
doubling loop certifies the loaded slow prefix required by the next loop. -/
theorem paperRationalPrefixDiagonal_first_success_loaded_hurwitz (m : ℕ) :
    ∃ a, FirstAcceptedIndex
      (fun a => orderedRationalPrefixAdmits m ((2 : ℚ)^a) &&
        paperRationalPrefixDiagonalAccepts m a) a ∧
      IsHurwitz (coalescedPrefixLoadedMatrix m ((2 : ℝ)^a)) := by
  obtain ⟨a,ha⟩ := paperRationalPrefixDiagonal_first_admitted_success m
  obtain ⟨hadmit,haccept⟩ := Bool.and_eq_true_iff.mp ha.1
  exact ⟨a,ha,
    (paperRationalPrefixDiagonal_accepted_loaded_certificate m a hadmit haccept).2.2.2⟩

/-- Proposition `diagonal` on the very first-loop witness: every positive
diagonal vector of actual prefix currents is certified with `Omega*P`.
P is the exact printed matrix from the accepted rational test, and r is
unchanged. This calls the established diagonal-column transfer theorem. -/
theorem paperRationalPrefixDiagonal_accepted_all_positive_currents
    (m a : ℕ)
    (hadmit : orderedRationalPrefixAdmits m ((2 : ℚ)^a) = true)
    (haccept : paperRationalPrefixDiagonalAccepts m a = true) :
    let r : ℝ := (2 : ℝ)^a
    let A := r⁻¹ • coalescedPrefixEdgeActionMatrix m r
    let P := (paperRationalDiagonalP m).map (algebraMap ℚ ℝ)
    (coalescedFiniteState (m+1) r).Positive ∧
      ∀ ω : Fin (m+1) → ℝ, (∀ i, 0 < ω i) →
        let Ω := Matrix.diagonal ω
        let Pω := Ω*P
        Pω.PosDef ∧ (-((A*Ω).transpose*Pω+Pω*(A*Ω))).PosDef ∧
          IsHurwitz (A*Ω) := by
  intro r A P
  have hx := orderedRationalPrefixAdmits_coalesced_positive m ((2 : ℚ)^a) hadmit
  refine ⟨by simpa [r] using hx, ?_⟩
  intro ω hω
  obtain ⟨hPq,hQq,_⟩ :=
    (rationalFixedLyapunovAccepts_iff
      (paperRationalLiteralPrefixA m ((2 : ℚ)^a)) (paperRationalDiagonalP m)
      (paperRationalLiteralPrefixQ m ((2 : ℚ)^a))).mp haccept
  have hP : P.PosDef := (rationalMatrix_posDef_cast_iff _).mpr hPq
  let p : Fin (m+1) → ℝ := fun i =>
    ((pathH (coalescedPathWeights m))⁻¹.mulVec
      (coalescedPathEdgeFeedback m)) i/pathVectorFin (coalescedPathWeights m) i
  have hPeq : P = Matrix.diagonal p := paperRationalDiagonalP_cast m
  have hp : ∀ i, 0 < p i := Matrix.posDef_diagonal_iff.mp (hPeq ▸ hP)
  have hAeq : (paperRationalLiteralPrefixA m ((2 : ℚ)^a)).map
      (algebraMap ℚ ℝ) = A := by
    simpa [A, r] using paperRationalLiteralPrefixA_cast m ((2 : ℚ)^a)
  have hQ := (rationalMatrix_posDef_cast_iff
    (paperRationalLiteralPrefixQ m ((2 : ℚ)^a))).mpr hQq
  rw [paperRationalLiteralPrefixQ_cast, hAeq] at hQ
  have hneg : (-(A.transpose*Matrix.diagonal p+Matrix.diagonal p*A)).PosDef := by
    simpa only [← hPeq, P] using hQ
  have hcert := diagonal_lyapunov_all_positive_currents A p ω hp hω hneg
  simpa only [← hPeq] using hcert

end
end PhosphorylationStableCapacity
