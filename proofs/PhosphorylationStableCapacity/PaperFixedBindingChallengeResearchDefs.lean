module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.RationalSplitWitnessAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-
Mathlib-only P079 Challenge fragment. Insert inside the existing
`PhosphorylationStableCapacity` namespace of Registry/P079/Challenge.lean.
It uses that Challenge's State, Rates, Equilibrium, InClass,
restrictedJacobianMatrix, IsLinearlyStable, IsOneUnstableSaddle, and
IsLocallyAsymptoticallyStableClass. It imports no project proof module.
The theorem realizing `PaperFixedBindingFiniteLaw` is deliberately not
stated here until its Solution-side endpoint has a strict module receipt.
-/

open Polynomial Filter
open scoped Topology

def paperNextN (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C ((a+1)*(b+1))*p + C 8*(X*p) + C (2*(a+b))*q
def paperNextJ (a b : ℝ) (p q : ℝ[X]) : ℝ[X] :=
  C ((a-1)*(b-1))*q + C 8*(X*q) + C (4*(a+b))*(X*p)
def paperCoalescedPair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 1)
  | m+1 =>
      let pq := paperCoalescedPair m
      (paperNextN 3 3 pq.1 pq.2, paperNextJ 3 3 pq.1 pq.2)
def paperOffsetRoot (ξ : ℕ → ℝ) (δ : ℝ) (j : ℕ) : ℝ :=
  3+δ*ξ j
def paperSplitPair : ℕ → (ℕ → ℝ) → ℝ → ℝ[X] × ℝ[X]
  | 0, ξ, δ => (1, C ((paperOffsetRoot ξ δ 0-1)/2))
  | m+1, ξ, δ =>
      let pq := paperSplitPair m ξ δ
      (paperNextN (paperOffsetRoot ξ δ (2*m+1))
        (paperOffsetRoot ξ δ (2*m+2)) pq.1 pq.2,
       paperNextJ (paperOffsetRoot ξ δ (2*m+1))
        (paperOffsetRoot ξ δ (2*m+2)) pq.1 pq.2)
def paperRatio (x : ℝ) : ℝ := (x^2-1)/8
def paperQuotient (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  (C (q.eval r)*(X*p)-C (r*p.eval r)*q) /ₘ (X-C r)
def paperRawD (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C 4*paperQuotient p q r
def paperRawB (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C r*paperRawD p q r+C (4*r*p.eval r-2*q.eval r)*p-C (2*q.eval r)*q
def paperSplitD (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  paperRawD (paperSplitPair m ξ δ).1 (paperSplitPair m ξ δ).2 r
def paperSplitB (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) : ℝ[X] :=
  paperRawB (paperSplitPair m ξ δ).1 (paperSplitPair m ξ δ).2 r
def paperCoalescedD (m : ℕ) (r : ℝ) : ℝ[X] :=
  paperRawD (paperCoalescedPair m).1 (paperCoalescedPair m).2 r
def paperCoalescedB (m : ℕ) (r : ℝ) : ℝ[X] :=
  paperRawB (paperCoalescedPair m).1 (paperCoalescedPair m).2 r

def paperRealize {n : ℕ}
    (T : Fin (n+1) → ℝ) (B D : Fin n → ℝ) : Rates n where
  a i := 2*D i/T i.castSucc
  b i := D i/B i
  c i := D i/B i
  alpha i := 2*D i/T i.succ
  beta _ := 1
  gamma _ := 1
def paperReconstruct {n : ℕ}
    (T : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ) : State n where
  S i := T i*u^i.val*s
  E := u*f
  F := f
  C i := B i*u^(i.val+1)*s*f
  D i := D i*u^(i.val+1)*s*f
def paperSourceRates (m : ℕ) (ξ : ℕ → ℝ)
    (r δ : ℝ) : Rates (m+2) :=
  paperRealize
    (fun i : Fin (m+3) => ((1+X)*paperSplitD (m+1) ξ r δ).coeff i)
    (fun i : Fin (m+2) => (paperSplitB (m+1) ξ r δ).coeff i)
    (fun i : Fin (m+2) => (paperSplitD (m+1) ξ r δ).coeff i)
def paperSourceState (m : ℕ) (ξ : ℕ → ℝ)
    (r δ : ℝ) (j : Fin (2*(m+1)+1)) : State (m+2) :=
  let x := paperOffsetRoot ξ δ j.val
  let D := paperSplitD (m+1) ξ r δ
  paperReconstruct
    (fun i : Fin (m+3) => ((1+X)*D).coeff i)
    (fun i : Fin (m+2) => (paperSplitB (m+1) ξ r δ).coeff i)
    (fun i : Fin (m+2) => D.coeff i)
    (paperRatio x) ((x-1)/(2*paperRatio x*D.eval (paperRatio x)))
    (4/(x+1))
def paperCoalescedState (m : ℕ) (r : ℝ) : State (m+2) :=
  let D := paperCoalescedD (m+1) r
  paperReconstruct
    (fun i : Fin (m+3) => ((1+X)*D).coeff i)
    (fun i : Fin (m+2) => (paperCoalescedB (m+1) r).coeff i)
    (fun i : Fin (m+2) => D.coeff i)
    (paperRatio 3) ((3-1)/(2*paperRatio 3*D.eval (paperRatio 3)))
    (4/(3+1))
def paperScaleRates {n : ℕ}
    (w : Fin n → ℝ) (k : Rates n) : Rates n where
  a i := w i*k.a i
  b i := w i*k.b i
  c i := w i*k.c i
  alpha i := w i*k.alpha i
  beta i := w i*k.beta i
  gamma i := w i*k.gamma i
def paperFixBinding {n : ℕ} (k : Rates n) : Rates n where
  a i := (1+k.c i)*(k.a i/(k.b i+k.c i))
  b _ := 1
  c := k.c
  alpha i := (1+k.gamma i)*(k.alpha i/(k.beta i+k.gamma i))
  beta _ := 1
  gamma := k.gamma
def paperRelax {n : ℕ} (k : Rates n) (ε : ℝ) : Rates n where
  a i := k.a i/ε
  b i := (k.b i+k.c i)/ε-k.c i
  c := k.c
  alpha i := k.alpha i/ε
  beta i := (k.beta i+k.gamma i)/ε-k.gamma i
  gamma := k.gamma
def paperRates (m : ℕ) (ξ : ℕ → ℝ)
    (r δ ε : ℝ) (w : Fin (m+2) → ℝ) : Rates (m+2) :=
  paperRelax (paperFixBinding
    (paperScaleRates w (paperSourceRates m ξ r δ))) ε
def paperFiniteGap {N : ℕ} (x : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset (Fin N)).erase j, (x j-x i)

def PaperFixedBindingSignedLawAt
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) (ξ : ℕ → ℝ)
    (r δ ε A α K : ℝ) (w : Fin (m+2) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  let k := paperRates m ξ r δ ε w
  let z := paperSourceState m ξ r δ
  k.Positive ∧ Function.Injective z ∧
    {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧
      InClass (2*r) 2 (2*(r+1)) s} = Set.range z ∧
    {s : State (m+2) | s.Positive ∧ Equilibrium k s ∧
      InClass (2*r) 2 (2*(r+1)) s}.ncard = 2*(m+1)+1 ∧
    ∀ j : Fin (2*(m+1)+1),
      let s := z j
      let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s))
      s.Positive ∧ Equilibrium k s ∧ InClass (2*r) 2 (2*(r+1)) s ∧
      Real.sqrt (1+8*s.E/s.F)=3+δ*x j ∧ J.charpoly.IsRoot (lam j δ) ∧
      ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval ((lam j δ) : ℂ) ≠ 0 ∧
      (∀ ζ : ℂ, ζ ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
        ζ = ((lam j δ) : ℂ) ∨ ζ.re ≤ -α) ∧
      |lam j δ/(-A*δ^(2*(m+1))*paperFiniteGap x j)-1| ≤ K*|δ| ∧
      (∃ err : ℝ, |err| ≤ 2*K*|δ| ∧
        1/|lam j δ|=(1+err)/(A*|paperFiniteGap x j| *δ^(2*(m+1)))) ∧
      (Even j.val → lam j δ < 0) ∧ (Odd j.val → 0 < lam j δ) ∧
      (Even j.val → IsLinearlyStable (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s)) ∧
        IsLocallyAsymptoticallyStableClass (2*r) 2 (2*(r+1)) k
          (toCoordinateSpace (chart s))) ∧
      (Odd j.val → IsOneUnstableSaddle (2*r) 2 (2*(r+1)) k
        (toCoordinateSpace (chart s)))

def PaperFixedBindingFamilyData (m : ℕ) (ξ : ℕ → ℝ)
    (r t ε : ℝ) (w : Fin (m+2) → ℝ) : Prop :=
  let X₀ := paperCoalescedState m r
  let kUnrelaxed := paperFixBinding (paperScaleRates w (paperSourceRates m ξ r 0))
  let k₀ := paperRates m ξ r 0 ε w
  (3*(m+2 : ℝ))/2 ≤ r ∧ 0 < t ∧
    (∀ i : Fin (m+2), kUnrelaxed.b i=1 ∧ kUnrelaxed.beta i=1) ∧
    (∀ i : Fin (m+1), k₀.gamma i.castSucc*X₀.D i.castSucc=1) ∧
    k₀.gamma (Fin.last (m+1))*X₀.D (Fin.last (m+1))=t ∧
    (∀ j, paperSourceState m ξ r 0 j = X₀) ∧
    (∀ i : Fin (m+2),
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).a i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).b i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).c i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).alpha i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).beta i) 0 ∧
      AnalyticAt ℝ (fun δ => (paperRates m ξ r δ ε w).gamma i) 0) ∧
    (∀ j : Fin (2*(m+1)+1),
      (∀ i : Fin (m+3), AnalyticAt ℝ
        (fun δ => (paperSourceState m ξ r δ j).S i) 0) ∧
      AnalyticAt ℝ (fun δ => (paperSourceState m ξ r δ j).E) 0 ∧
      AnalyticAt ℝ (fun δ => (paperSourceState m ξ r δ j).F) 0 ∧
      (∀ i : Fin (m+2), AnalyticAt ℝ
        (fun δ => (paperSourceState m ξ r δ j).C i) 0) ∧
      (∀ i : Fin (m+2), AnalyticAt ℝ
        (fun δ => (paperSourceState m ξ r δ j).D i) 0))

def PaperFixedBindingSelectedLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) (ξ : ℕ → ℝ)
    (r ε A α K : ℝ) (w : Fin (m+2) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ) : Prop :=
  let X₀ := paperCoalescedState m r
  let k₀ := paperRates m ξ r 0 ε w
  (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0=0) ∧
    0 < A ∧ 0 < α ∧ 0 < K ∧
    (A =
      let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k₀
        (toCoordinateSpace (chart X₀))
      let Θ₀ : ℂ := ((J₀.map (algebraMap ℝ ℂ)).charpoly.roots.erase 0).prod
      let P := paperCoalescedPair (m+1)
      let D := paperCoalescedD (m+1) r
      let B := paperCoalescedB (m+1) r
      let C := 2*r*P.1.eval r+P.2.eval r
      let M := (B.eval 1-D.eval 1)/D.coeff 0
      (4*C*M/((r-1)*D.eval 1*‖Θ₀‖))*
        (∏ i : Fin (m+2), (k₀.b i+k₀.c i)*k₀.alpha i*k₀.gamma i)) ∧
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      PaperFixedBindingSignedLawAt m x ξ r δ ε A α K w lam

def PaperFixedBindingFiniteLaw
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) : Prop :=
  StrictMono x → ∃ ξ : ℕ → ℝ, StrictMono ξ ∧
    (∀ j : Fin (2*(m+1)+1), ξ j.val=x j) ∧ ∃ a b c : ℕ,
      let r : ℝ := 2^a; let t : ℝ := (1/2)^b; let ε : ℝ := (1/2)^c
      let X₀ := paperCoalescedState m r
      let w : Fin (m+2) → ℝ := Fin.lastCases (t/X₀.D (Fin.last (m+1)))
        (fun i => 1/X₀.D i.castSucc)
      PaperFixedBindingFamilyData m ξ r t ε w ∧
      ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ, ∃ A α K : ℝ,
        PaperFixedBindingSelectedLaw m x ξ r ε A α K w lam

def PaperFixedBindingRationalAttainment (m : ℕ) : Prop :=
  ∃ a b c : ℕ,
    let r : ℝ := 2^a; let t : ℝ := (1/2)^b; let ε : ℝ := (1/2)^c
    let X₀ := paperCoalescedState m r
    let w : Fin (m+2) → ℝ := Fin.lastCases (t/X₀.D (Fin.last (m+1)))
      (fun i => 1/X₀.D i.castSucc)
    let ξ : ℕ → ℝ := fun j => (j : ℝ)
    let x : Fin (2*(m+1)+1) → ℝ := fun j => (j.val : ℝ)
    PaperFixedBindingFamilyData m ξ r t ε w ∧
    ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ, ∃ A α K : ℝ,
      PaperFixedBindingSelectedLaw m x ξ r ε A α K w lam ∧
      ∃ d : ℕ, let δ : ℝ := (1/2)^d
        RationalRates (paperRates m ξ r δ ε w) ∧
        (∀ j, RationalState (paperSourceState m ξ r δ j)) ∧
        PaperFixedBindingSignedLawAt m x ξ r δ ε A α K w lam

end
end PhosphorylationStableCapacity
