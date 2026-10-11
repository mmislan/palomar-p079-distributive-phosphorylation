module
public import proofs.PhosphorylationStableCapacity.LoadedFieldCurrent
public import proofs.PhosphorylationStableCapacity.ProjectedPathIncidence

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- Nonnegative concentration of every literal species. -/
def NonnegativeState {n : ℕ} (x : State n) : Prop :=
  (∀ i, 0 ≤ x.S i) ∧ 0 ≤ x.E ∧ 0 ≤ x.F ∧
    (∀ i, 0 ≤ x.C i) ∧ (∀ i, 0 ≤ x.D i)

/-- A positive kinase total excludes a zero free kinase at any
nonnegative equilibrium. -/
theorem equilibrium_free_kinase_positive {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : NonnegativeState x)
    (heq : Equilibrium k x)
    {ET : ℝ} (hET : 0 < ET) (htotal : totalE x = ET) :
    0 < x.E := by
  by_contra hEpos
  have hE0 : x.E = 0 := le_antisymm (le_of_not_gt hEpos) hx.2.1
  have hC0 (i : Fin n) : x.C i = 0 := by
    have hbal := heq.2.2.2.1 i
    have hbc : 0 < k.b i + k.c i :=
      add_pos (hk i).2.1 (hk i).2.2.1
    have hmul : (k.b i + k.c i) * x.C i = 0 := by
      dsimp [field, kinaseNet] at hbal
      rw [hE0] at hbal
      nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hbc)
  have hzero : totalE x = 0 := by
    simp [totalE, hE0, hC0]
  linarith

/-- A positive phosphatase total likewise excludes a zero free
phosphatase. -/
theorem equilibrium_free_phosphatase_positive {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : NonnegativeState x)
    (heq : Equilibrium k x)
    {FT : ℝ} (hFT : 0 < FT) (htotal : totalF x = FT) :
    0 < x.F := by
  by_contra hFpos
  have hF0 : x.F = 0 := le_antisymm (le_of_not_gt hFpos) hx.2.2.1
  have hD0 (i : Fin n) : x.D i = 0 := by
    have hbal := heq.2.2.2.2 i
    have hbg : 0 < k.beta i + k.gamma i :=
      add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2
    have hmul : (k.beta i + k.gamma i) * x.D i = 0 := by
      dsimp [field, phosphataseNet] at hbal
      rw [hF0] at hbal
      nlinarith
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hbg)
  have hzero : totalF x = 0 := by
    simp [totalF, hF0, hD0]
  linarith

/-- Every catalytic edge current vanishes at a literal equilibrium.
Invertibility of the projected path incidence makes this true without
assuming positivity or nondegeneracy. -/
theorem equilibrium_catalytic_balance {n : ℕ}
    (k : Rates n) (x : State n) (heq : Equilibrium k x)
    (i : Fin n) : k.c i * x.C i = k.gamma i * x.D i := by
  let j : Fin n → ℝ := fun a => k.c a * x.C a - k.gamma a * x.D a
  have hloaded (a : Fin n) : loadedLevel (field k x) a.succ = 0 := by
    simp [loadedLevel, heq.1, heq.2.2.2.1, heq.2.2.2.2]
  have hmat : (projectedPathIncidence n).mulVec j = 0 := by
    funext a
    rw [projectedPathIncidence_mulVec]
    have hflux := loadedLevel_field_eq_catalytic_flux k x a.succ
    rw [hloaded a] at hflux
    change (pathIncidence n).transpose.mulVec j a.succ = 0
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      pathIncidence, Finset.sum_sub_distrib, sub_mul]
    simpa [j, eq_comm] using hflux.symm
  have hinj := Matrix.mulVec_injective_of_isUnit
    (projectedPathIncidence_isUnit n)
  have hj : j = 0 := hinj (by simpa using hmat)
  have hj0 : j i = 0 := congrFun hj i
  dsimp [j] at hj0
  linarith

/-- With positive free enzymes, a substrate vanishes on one side of an
edge exactly when it vanishes on the other. -/
theorem equilibrium_substrate_zero_iff_succ {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (heq : Equilibrium k x)
    (hE : 0 < x.E) (hF : 0 < x.F)
    (i : Fin n) : x.S i.castSucc = 0 ↔ x.S i.succ = 0 := by
  have hC : k.a i * x.S i.castSucc * x.E =
      (k.b i + k.c i) * x.C i := by
    have h := heq.2.2.2.1 i
    dsimp [field, kinaseNet] at h
    nlinarith
  have hD : k.alpha i * x.S i.succ * x.F =
      (k.beta i + k.gamma i) * x.D i := by
    have h := heq.2.2.2.2 i
    dsimp [field, phosphataseNet] at h
    nlinarith
  have hcat := equilibrium_catalytic_balance k x heq i
  have ha : 0 < k.a i := (hk i).1
  have hbc : 0 < k.b i + k.c i :=
    add_pos (hk i).2.1 (hk i).2.2.1
  have hc : 0 < k.c i := (hk i).2.2.1
  have halpha : 0 < k.alpha i := (hk i).2.2.2.1
  have hbg : 0 < k.beta i + k.gamma i :=
    add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2
  have hgamma : 0 < k.gamma i := (hk i).2.2.2.2.2
  constructor
  · intro hS
    have hC0 : x.C i = 0 := by
      have hm : (k.b i + k.c i) * x.C i = 0 := by
        rw [hS] at hC
        nlinarith [hC]
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hbc)
    have hD0 : x.D i = 0 := by
      have hm : k.gamma i * x.D i = 0 := by rw [← hcat, hC0]; ring
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hgamma)
    have hm : (k.alpha i * x.F) * x.S i.succ = 0 := by
      rw [hD0] at hD
      nlinarith [hD]
    exact (mul_eq_zero.mp hm).resolve_left
      (ne_of_gt (mul_pos halpha hF))
  · intro hS
    have hD0 : x.D i = 0 := by
      have hm : (k.beta i + k.gamma i) * x.D i = 0 := by
        rw [hS] at hD
        nlinarith [hD]
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hbg)
    have hC0 : x.C i = 0 := by
      have hm : k.c i * x.C i = 0 := by rw [hcat, hD0]; ring
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hc)
    have hm : (k.a i * x.E) * x.S i.castSucc = 0 := by
      rw [hC0] at hC
      nlinarith [hC]
    exact (mul_eq_zero.mp hm).resolve_left
      (ne_of_gt (mul_pos ha hE))

/-- Zero substrate at any level is equivalent to zero substrate at level
zero, by the linked catalytic path. -/
theorem equilibrium_substrate_zero_iff_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (heq : Equilibrium k x)
    (hE : 0 < x.E) (hF : 0 < x.F)
    (j : Fin (n + 1)) : x.S j = 0 ↔ x.S 0 = 0 := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
      exact (equilibrium_substrate_zero_iff_succ k x hk heq hE hF i).symm.trans ih

/-- A nonnegative equilibrium in a class with three positive totals is
strictly positive in every literal species. Thus the class has no boundary
equilibria. -/
theorem equilibrium_positive_of_nonnegative {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : NonnegativeState x)
    (heq : Equilibrium k x)
    (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT) (hST : 0 < ST)
    (hclass : InClass ET FT ST x) : x.Positive := by
  have hE : 0 < x.E :=
    equilibrium_free_kinase_positive k x hk hx heq hET hclass.1
  have hF : 0 < x.F :=
    equilibrium_free_phosphatase_positive k x hk hx heq hFT hclass.2.1
  have hS0 : x.S 0 ≠ 0 := by
    intro hzero
    have hSall (j : Fin (n + 1)) : x.S j = 0 :=
      (equilibrium_substrate_zero_iff_zero k x hk heq hE hF j).2 hzero
    have hCall (i : Fin n) : x.C i = 0 := by
      have h := heq.2.2.2.1 i
      have hbc : 0 < k.b i + k.c i :=
        add_pos (hk i).2.1 (hk i).2.2.1
      dsimp [field, kinaseNet] at h
      rw [hSall i.castSucc] at h
      have hm : (k.b i + k.c i) * x.C i = 0 := by nlinarith [h]
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hbc)
    have hDall (i : Fin n) : x.D i = 0 := by
      have h := heq.2.2.2.2 i
      have hbg : 0 < k.beta i + k.gamma i :=
        add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2
      dsimp [field, phosphataseNet] at h
      rw [hSall i.succ] at h
      have hm : (k.beta i + k.gamma i) * x.D i = 0 := by nlinarith [h]
      exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt hbg)
    have htotal0 : totalS x = 0 := by
      simp [totalS, hSall, hCall, hDall]
    linarith [hclass.2.2]
  have hSpos (j : Fin (n + 1)) : 0 < x.S j := by
    have hj0 : x.S j ≠ 0 := by
      intro hj
      exact hS0 ((equilibrium_substrate_zero_iff_zero k x hk heq hE hF j).1 hj)
    exact lt_of_le_of_ne (hx.1 j) (Ne.symm hj0)
  have hCpos (i : Fin n) : 0 < x.C i := by
    have hC0 : x.C i ≠ 0 := by
      intro hzero
      have h := heq.2.2.2.1 i
      dsimp [field, kinaseNet] at h
      rw [hzero] at h
      have hp : 0 < k.a i * x.S i.castSucc * x.E :=
        mul_pos (mul_pos (hk i).1 (hSpos i.castSucc)) hE
      nlinarith
    exact lt_of_le_of_ne (hx.2.2.2.1 i) (Ne.symm hC0)
  have hDpos (i : Fin n) : 0 < x.D i := by
    have hD0 : x.D i ≠ 0 := by
      intro hzero
      have h := heq.2.2.2.2 i
      dsimp [field, phosphataseNet] at h
      rw [hzero] at h
      have hp : 0 < k.alpha i * x.S i.succ * x.F :=
        mul_pos (mul_pos (hk i).2.2.2.1 (hSpos i.succ)) hF
      nlinarith
    exact lt_of_le_of_ne (hx.2.2.2.2 i) (Ne.symm hD0)
  exact ⟨hSpos, hE, hF, hCpos, hDpos⟩

end
end PhosphorylationStableCapacity
