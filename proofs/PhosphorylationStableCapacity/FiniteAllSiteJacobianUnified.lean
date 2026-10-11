module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Fin.Basic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! A single strict endpoint for the actual arbitrary-size class Jacobian. -/

/-! ## FiniteAllSiteFieldFormula -/
namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal class substrate at site `i`, including the eliminated `S₀`. -/
def allSiteClassS {n : ℕ} (ST : ℝ) (u : CoordinateSpace n) :
    Fin (n + 1) → ℝ :=
  Fin.cases (ST - (∑ i, u.1 i) - (∑ i, u.2.1 i) - (∑ i, u.2.2 i)) u.1

def allSiteClassE {n : ℕ} (ET : ℝ) (u : CoordinateSpace n) : ℝ :=
  ET - ∑ i, u.2.1 i

def allSiteClassF {n : ℕ} (FT : ℝ) (u : CoordinateSpace n) : ℝ :=
  FT - ∑ i, u.2.2 i

def allSiteClassKinase {n : ℕ} (ET ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) : ℝ :=
  k.a i * allSiteClassS ST u i.castSucc * allSiteClassE ET u -
    k.b i * u.2.1 i

def allSiteClassPhosphatase {n : ℕ} (FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) : ℝ :=
  k.alpha i * allSiteClassS ST u i.succ * allSiteClassF FT u -
    k.beta i * u.2.2 i

/-- An explicit finite-sum formula for the actual `3n` class field.
This is the algebraic starting point for one arbitrary-size derivative formula. -/
def allSiteExplicitField {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : CoordinateSpace n :=
  ((fun j => ∑ i : Fin n, (
      (if i.castSucc = j.succ then
        -allSiteClassKinase ET ST k u i + k.gamma i * u.2.2 i else 0) +
      (if i.succ = j.succ then
        k.c i * u.2.1 i - allSiteClassPhosphatase FT ST k u i else 0))),
    (fun i => allSiteClassKinase ET ST k u i - k.c i * u.2.1 i),
    (fun i => allSiteClassPhosphatase FT ST k u i - k.gamma i * u.2.2 i))

theorem restrictedFieldEuclid_eq_allSiteExplicitField {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    restrictedFieldEuclid ET FT ST k u =
      allSiteExplicitField ET FT ST k u := by
  rfl

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianLinear -/
namespace PhosphorylationStableCapacity

noncomputable section
open Module

private abbrev SitePi (n : ℕ) := Fin n → ℝ

def allSitePS {n : ℕ} (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ (SitePi n) ((SitePi n) × (SitePi n)))

def allSitePC {n : ℕ} (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ (SitePi n) (SitePi n)).comp
      (ContinuousLinearMap.snd ℝ (SitePi n) ((SitePi n) × (SitePi n))))

def allSitePD {n : ℕ} (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ (SitePi n) (SitePi n)).comp
      (ContinuousLinearMap.snd ℝ (SitePi n) ((SitePi n) × (SitePi n))))

@[simp] theorem allSitePS_apply {n : ℕ} (i : Fin n) (u : CoordinateSpace n) :
    allSitePS i u = u.1 i := rfl

@[simp] theorem allSitePC_apply {n : ℕ} (i : Fin n) (u : CoordinateSpace n) :
    allSitePC i u = u.2.1 i := rfl

@[simp] theorem allSitePD_apply {n : ℕ} (i : Fin n) (u : CoordinateSpace n) :
    allSitePD i u = u.2.2 i := rfl

/-- The site-zero substrate, free-enzyme, and free-phosphatase linear parts. -/
def allSiteS0Linear (n : ℕ) : CoordinateSpace n →L[ℝ] ℝ :=
  -(∑ i, allSitePS i) - (∑ i, allSitePC i) - (∑ i, allSitePD i)

def allSiteELinear (n : ℕ) : CoordinateSpace n →L[ℝ] ℝ :=
  -(∑ i, allSitePC i)

def allSiteFLinear (n : ℕ) : CoordinateSpace n →L[ℝ] ℝ :=
  -(∑ i, allSitePD i)

def allSiteSLinear {n : ℕ} :
    Fin (n + 1) → CoordinateSpace n →L[ℝ] ℝ :=
  Fin.cases (allSiteS0Linear n) allSitePS

@[simp] theorem allSiteS0Linear_apply {n : ℕ} (u : CoordinateSpace n) :
    allSiteS0Linear n u =
      -(∑ i, u.1 i) - (∑ i, u.2.1 i) - (∑ i, u.2.2 i) := by
  simp [allSiteS0Linear]

@[simp] theorem allSiteELinear_apply {n : ℕ} (u : CoordinateSpace n) :
    allSiteELinear n u = -(∑ i, u.2.1 i) := by
  simp [allSiteELinear]

@[simp] theorem allSiteFLinear_apply {n : ℕ} (u : CoordinateSpace n) :
    allSiteFLinear n u = -(∑ i, u.2.2 i) := by
  simp [allSiteFLinear]

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianAffine -/
namespace PhosphorylationStableCapacity

noncomputable section

theorem allSiteClassS_hasFDerivAt {n : ℕ} (ST : ℝ)
    (u : CoordinateSpace n) (i : Fin (n + 1)) :
    HasFDerivAt (fun v : CoordinateSpace n => allSiteClassS ST v i)
      (allSiteSLinear i) u := by
  cases i using Fin.cases with
  | zero =>
      have hfun :
          (fun v : CoordinateSpace n => allSiteClassS ST v 0) =
            fun v => ST + allSiteS0Linear n v := by
        funext v
        simp [allSiteClassS]; ring
      rw [hfun]
      exact (allSiteS0Linear n).hasFDerivAt.const_add ST
  | succ i =>
      exact (allSitePS i).hasFDerivAt

theorem allSiteClassE_hasFDerivAt {n : ℕ} (ET : ℝ)
    (u : CoordinateSpace n) :
    HasFDerivAt (allSiteClassE ET) (allSiteELinear n) u := by
  have hfun : allSiteClassE (n := n) ET =
      fun v => ET + allSiteELinear n v := by
    funext v
    simp [allSiteClassE, sub_eq_add_neg]
  rw [hfun]
  exact (allSiteELinear n).hasFDerivAt.const_add ET

theorem allSiteClassF_hasFDerivAt {n : ℕ} (FT : ℝ)
    (u : CoordinateSpace n) :
    HasFDerivAt (allSiteClassF FT) (allSiteFLinear n) u := by
  have hfun : allSiteClassF (n := n) FT =
      fun v => FT + allSiteFLinear n v := by
    funext v
    simp [allSiteClassF, sub_eq_add_neg]
  rw [hfun]
  exact (allSiteFLinear n).hasFDerivAt.const_add FT

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianFlux -/
namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

set_option maxHeartbeats 2000000

def allSiteKinaseRow {n : ℕ} (ET ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  k.a i • (allSiteClassE ET u • allSiteSLinear i.castSucc +
    allSiteClassS ST u i.castSucc • allSiteELinear n) -
      k.b i • allSitePC i

def allSitePhosphataseRow {n : ℕ} (FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  k.alpha i • (allSiteClassF FT u • allSiteSLinear i.succ +
    allSiteClassS ST u i.succ • allSiteFLinear n) -
      k.beta i • allSitePD i

theorem allSiteClassKinase_hasFDerivAt {n : ℕ}
    (ET ST : ℝ) (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    HasFDerivAt (fun v => allSiteClassKinase ET ST k v i)
      (allSiteKinaseRow ET ST k u i) u := by
  have hs := allSiteClassS_hasFDerivAt ST u i.castSucc
  have he := allSiteClassE_hasFDerivAt ET u
  have hc := (allSitePC i).hasFDerivAt (x := u)
  let fcalc : CoordinateSpace n → ℝ := fun v =>
    k.a i * (allSiteClassS ST v i.castSucc * allSiteClassE ET v) -
      k.b i * v.2.1 i
  let Dcalc : CoordinateSpace n →L[ℝ] ℝ :=
    k.a i • (allSiteClassS ST u i.castSucc • allSiteELinear n +
      allSiteClassE ET u • allSiteSLinear i.castSucc) -
      k.b i • allSitePC i
  have hcalc : HasFDerivAt fcalc Dcalc u := by
    exact ((hs.mul he).const_mul (k.a i)).sub
      (hc.const_mul (k.b i))
  have hf : fcalc = fun v => allSiteClassKinase ET ST k v i := by
    funext v
    dsimp [fcalc, allSiteClassKinase]
    ring
  have hD : Dcalc = allSiteKinaseRow ET ST k u i := by
    apply ContinuousLinearMap.ext
    intro v
    simp [Dcalc, allSiteKinaseRow]; ring
  rw [hf, hD] at hcalc
  exact hcalc

theorem allSiteClassPhosphatase_hasFDerivAt {n : ℕ}
    (FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    HasFDerivAt (fun v => allSiteClassPhosphatase FT ST k v i)
      (allSitePhosphataseRow FT ST k u i) u := by
  have hs := allSiteClassS_hasFDerivAt ST u i.succ
  have hf := allSiteClassF_hasFDerivAt FT u
  have hd := (allSitePD i).hasFDerivAt (x := u)
  let fcalc : CoordinateSpace n → ℝ := fun v =>
    k.alpha i * (allSiteClassS ST v i.succ * allSiteClassF FT v) -
      k.beta i * v.2.2 i
  let Dcalc : CoordinateSpace n →L[ℝ] ℝ :=
    k.alpha i • (allSiteClassS ST u i.succ • allSiteFLinear n +
      allSiteClassF FT u • allSiteSLinear i.succ) -
      k.beta i • allSitePD i
  have hcalc : HasFDerivAt fcalc Dcalc u := by
    exact ((hs.mul hf).const_mul (k.alpha i)).sub
      (hd.const_mul (k.beta i))
  have hfun : fcalc = fun v => allSiteClassPhosphatase FT ST k v i := by
    funext v
    dsimp [fcalc, allSiteClassPhosphatase]
    ring
  have hD : Dcalc = allSitePhosphataseRow FT ST k u i := by
    apply ContinuousLinearMap.ext
    intro v
    simp [Dcalc, allSitePhosphataseRow]; ring
  rw [hfun, hD] at hcalc
  exact hcalc

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianRows -/
namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

set_option maxHeartbeats 2000000

/-- The three arbitrary-size class-Jacobian row families. -/
def allSiteRowS {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (j : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  ∑ i : Fin n, (
    (if i.castSucc = j.succ then
      -allSiteKinaseRow ET ST k u i + k.gamma i • allSitePD i else 0) +
    (if i.succ = j.succ then
      k.c i • allSitePC i - allSitePhosphataseRow FT ST k u i else 0))

def allSiteRowC {n : ℕ} (ET ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  allSiteKinaseRow ET ST k u i - k.c i • allSitePC i

def allSiteRowD {n : ℕ} (FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) : CoordinateSpace n →L[ℝ] ℝ :=
  allSitePhosphataseRow FT ST k u i - k.gamma i • allSitePD i

theorem allSiteRowS_hasFDerivAt {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (j : Fin n) :
    HasFDerivAt
      (fun v : CoordinateSpace n => (allSiteExplicitField ET FT ST k v).1 j)
      (allSiteRowS ET FT ST k u j) u := by
  have hterm (i : Fin n) : HasFDerivAt
      (fun v : CoordinateSpace n =>
        (if i.castSucc = j.succ then
          -allSiteClassKinase ET ST k v i + k.gamma i * v.2.2 i else 0) +
        (if i.succ = j.succ then
          k.c i * v.2.1 i - allSiteClassPhosphatase FT ST k v i else 0))
      ((if i.castSucc = j.succ then
          -allSiteKinaseRow ET ST k u i + k.gamma i • allSitePD i else 0) +
        (if i.succ = j.succ then
          k.c i • allSitePC i - allSitePhosphataseRow FT ST k u i else 0)) u := by
    have hleft : HasFDerivAt
        (fun v : CoordinateSpace n =>
          if i.castSucc = j.succ then
            -allSiteClassKinase ET ST k v i + k.gamma i * v.2.2 i else 0)
        (if i.castSucc = j.succ then
          -allSiteKinaseRow ET ST k u i + k.gamma i • allSitePD i else 0) u := by
      by_cases hp : i.castSucc = j.succ
      · simp only [hp, ite_true]
        let fcalc : CoordinateSpace n → ℝ := fun v =>
          -allSiteClassKinase ET ST k v i + k.gamma i * allSitePD i v
        let Dcalc : CoordinateSpace n →L[ℝ] ℝ :=
          -allSiteKinaseRow ET ST k u i + k.gamma i • allSitePD i
        have hcalc : HasFDerivAt fcalc Dcalc u := by
          exact (allSiteClassKinase_hasFDerivAt ET ST k u i).neg.add
            ((allSitePD i).hasFDerivAt.const_mul (k.gamma i))
        have hf : fcalc = fun v : CoordinateSpace n =>
            -allSiteClassKinase ET ST k v i + k.gamma i * v.2.2 i := by
          funext v
          simp [fcalc]
        rw [hf] at hcalc
        exact hcalc
      · simp only [hp, ite_false]
        exact hasFDerivAt_const (0 : ℝ) u
    have hright : HasFDerivAt
        (fun v : CoordinateSpace n =>
          if i.succ = j.succ then
            k.c i * v.2.1 i - allSiteClassPhosphatase FT ST k v i else 0)
        (if i.succ = j.succ then
          k.c i • allSitePC i - allSitePhosphataseRow FT ST k u i else 0) u := by
      by_cases hp : i.succ = j.succ
      · simp only [hp, ite_true]
        let fcalc : CoordinateSpace n → ℝ := fun v =>
          k.c i * allSitePC i v - allSiteClassPhosphatase FT ST k v i
        let Dcalc : CoordinateSpace n →L[ℝ] ℝ :=
          k.c i • allSitePC i - allSitePhosphataseRow FT ST k u i
        have hcalc : HasFDerivAt fcalc Dcalc u := by
          exact ((allSitePC i).hasFDerivAt.const_mul (k.c i)).sub
            (allSiteClassPhosphatase_hasFDerivAt FT ST k u i)
        have hf : fcalc = fun v : CoordinateSpace n =>
            k.c i * v.2.1 i - allSiteClassPhosphatase FT ST k v i := by
          funext v
          simp [fcalc]
        rw [hf] at hcalc
        exact hcalc
      · simp only [hp, ite_false]
        exact hasFDerivAt_const (0 : ℝ) u
    exact hleft.add hright
  simpa only [allSiteExplicitField, allSiteRowS] using
    (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i))

theorem allSiteRowC_hasFDerivAt {n : ℕ} (ET ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    HasFDerivAt
      (fun v : CoordinateSpace n =>
        allSiteClassKinase ET ST k v i - k.c i * v.2.1 i)
      (allSiteRowC ET ST k u i) u := by
  let fcalc : CoordinateSpace n → ℝ := fun v =>
    allSiteClassKinase ET ST k v i - k.c i * allSitePC i v
  let Dcalc : CoordinateSpace n →L[ℝ] ℝ :=
    allSiteKinaseRow ET ST k u i - k.c i • allSitePC i
  have hcalc : HasFDerivAt fcalc Dcalc u := by
    exact (allSiteClassKinase_hasFDerivAt ET ST k u i).sub
      ((allSitePC i).hasFDerivAt.const_mul (k.c i))
  have hf : fcalc = fun v : CoordinateSpace n =>
      allSiteClassKinase ET ST k v i - k.c i * v.2.1 i := by
    funext v
    simp [fcalc]
  rw [hf, show Dcalc = allSiteRowC ET ST k u i from rfl] at hcalc
  exact hcalc

theorem allSiteRowD_hasFDerivAt {n : ℕ} (FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    HasFDerivAt
      (fun v : CoordinateSpace n =>
        allSiteClassPhosphatase FT ST k v i - k.gamma i * v.2.2 i)
      (allSiteRowD FT ST k u i) u := by
  let fcalc : CoordinateSpace n → ℝ := fun v =>
    allSiteClassPhosphatase FT ST k v i - k.gamma i * allSitePD i v
  let Dcalc : CoordinateSpace n →L[ℝ] ℝ :=
    allSitePhosphataseRow FT ST k u i - k.gamma i • allSitePD i
  have hcalc : HasFDerivAt fcalc Dcalc u := by
    exact (allSiteClassPhosphatase_hasFDerivAt FT ST k u i).sub
      ((allSitePD i).hasFDerivAt.const_mul (k.gamma i))
  have hf : fcalc = fun v : CoordinateSpace n =>
      allSiteClassPhosphatase FT ST k v i - k.gamma i * v.2.2 i := by
    funext v
    simp [fcalc]
  rw [hf, show Dcalc = allSiteRowD FT ST k u i from rfl] at hcalc
  exact hcalc

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianAction -/
namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

def allSiteJacobianCLM {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  (ContinuousLinearMap.pi (fun j => allSiteRowS ET FT ST k u j)).prod
    ((ContinuousLinearMap.pi (fun i => allSiteRowC ET ST k u i)).prod
      (ContinuousLinearMap.pi (fun i => allSiteRowD FT ST k u i)))

theorem allSiteExplicitField_hasFDerivAt {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    HasFDerivAt (allSiteExplicitField ET FT ST k)
      (allSiteJacobianCLM ET FT ST k u) u := by
  have hs : HasFDerivAt
      (fun v : CoordinateSpace n => (allSiteExplicitField ET FT ST k v).1)
      (ContinuousLinearMap.pi (fun j => allSiteRowS ET FT ST k u j)) u := by
    apply hasFDerivAt_pi'.2
    intro j
    exact allSiteRowS_hasFDerivAt ET FT ST k u j
  have hc : HasFDerivAt
      (fun v : CoordinateSpace n => (allSiteExplicitField ET FT ST k v).2.1)
      (ContinuousLinearMap.pi (fun i => allSiteRowC ET ST k u i)) u := by
    apply hasFDerivAt_pi'.2
    intro i
    simpa [allSiteExplicitField] using
      allSiteRowC_hasFDerivAt ET ST k u i
  have hd : HasFDerivAt
      (fun v : CoordinateSpace n => (allSiteExplicitField ET FT ST k v).2.2)
      (ContinuousLinearMap.pi (fun i => allSiteRowD FT ST k u i)) u := by
    apply hasFDerivAt_pi'.2
    intro i
    simpa [allSiteExplicitField] using
      allSiteRowD_hasFDerivAt FT ST k u i
  simpa only [allSiteJacobianCLM] using hs.prodMk (hc.prodMk hd)

/-- Literal class derivative equals the explicit arbitrary-size row formula. -/
theorem restrictedJacobian_eq_allSiteJacobianCLM {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    restrictedJacobian ET FT ST k u =
      allSiteJacobianCLM ET FT ST k u := by
  have hfield : restrictedFieldEuclid ET FT ST k =
      allSiteExplicitField ET FT ST k :=
    funext (restrictedFieldEuclid_eq_allSiteExplicitField ET FT ST k)
  simp only [restrictedJacobian, hfield]
  exact (allSiteExplicitField_hasFDerivAt ET FT ST k u).fderiv

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianMatrix -/
namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- A computable finite-sum presentation of the actual class Jacobian at any
site count. The entries use explicit flux rows, with no opaque `fderiv`. -/
def allSiteExplicitJacobianMatrix {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    Matrix (Fin n ⊕ (Fin n ⊕ Fin n))
      (Fin n ⊕ (Fin n ⊕ Fin n)) ℝ :=
  LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
    (allSiteJacobianCLM ET FT ST k u).toLinearMap

/-- Every certificate entry evaluates an explicit row map on one standard
coordinate vector; there is no derivative operator left to compute. -/
theorem allSiteExplicitJacobianMatrix_apply {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n)
    (i j : Fin n ⊕ (Fin n ⊕ Fin n)) :
    allSiteExplicitJacobianMatrix ET FT ST k u i j =
      (coordinateBasis n).repr
        (allSiteJacobianCLM ET FT ST k u (coordinateBasis n j)) i := by
  simp [allSiteExplicitJacobianMatrix, LinearMap.toMatrix_apply]

theorem restrictedJacobianMatrix_eq_allSiteExplicit {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    restrictedJacobianMatrix ET FT ST k u =
      allSiteExplicitJacobianMatrix ET FT ST k u := by
  rw [restrictedJacobianMatrix,
    restrictedJacobian_eq_allSiteJacobianCLM]
  rfl

end
end PhosphorylationStableCapacity

/-! ## FiniteAllSiteJacobianFin -/
namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The certificate order is the `n` free substrates, followed by `n`
kinase complexes and `n` phosphatase complexes. -/
def allSiteIndexEquiv (n : ℕ) :
    (Fin n ⊕ (Fin n ⊕ Fin n)) ≃ Fin (3 * n) :=
  ((Equiv.sumCongr (Equiv.refl (Fin n))
      (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n))).trans
    (finSumFinEquiv : Fin n ⊕ Fin (n + n) ≃ Fin (n + (n + n)))).trans
      (Fin.castOrderIso (by omega : n + (n + n) = 3 * n)).toEquiv

def allSiteExplicitFinMatrix {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : Matrix (Fin (3 * n)) (Fin (3 * n)) ℝ :=
  Matrix.reindex (allSiteIndexEquiv n) (allSiteIndexEquiv n)
    (allSiteExplicitJacobianMatrix ET FT ST k u)

theorem allSiteExplicitFinMatrix_apply {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i j : Fin (3 * n)) :
    allSiteExplicitFinMatrix ET FT ST k u i j =
      (coordinateBasis n).repr
        (allSiteJacobianCLM ET FT ST k u
          (coordinateBasis n ((allSiteIndexEquiv n).symm j)))
        ((allSiteIndexEquiv n).symm i) := by
  simp only [allSiteExplicitFinMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, allSiteExplicitJacobianMatrix_apply]

/-- Any finite certificate replayed against this explicit matrix is a
certificate for the literal restricted class Jacobian. -/
theorem allSiteExplicitFinMatrix_charpoly_eq_restricted {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (allSiteExplicitFinMatrix ET FT ST k u).charpoly =
      (restrictedJacobianMatrix ET FT ST k u).charpoly := by
  rw [allSiteExplicitFinMatrix, Matrix.charpoly_reindex,
    restrictedJacobianMatrix_eq_allSiteExplicit]

end
end PhosphorylationStableCapacity
