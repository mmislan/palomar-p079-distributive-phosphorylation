module
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast

@[expose] public section

/-
Adapted from CRNT/Dynamics/FlowConstruction.lean in
https://github.com/marpaia/crnt-lean at commit
99137993e729c8add247388718a22a0e0f393dab.

MIT License
Copyright (c) 2026 Mike Arpaia

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

namespace PhosphorylationStableCapacity.BoundedODE

open Filter
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bounded globally Lipschitz autonomous field has a solution on
any prescribed symmetric open time interval. -/
theorem exists_solution_Ioo {f : E → E} {K M : ℝ≥0}
    (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M)
    (x₀ : E) (R : ℝ≥0) :
    ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-(R : ℝ)) (R : ℝ),
        HasDerivAt α (f (α t)) t := by
  have ht₀ : (0 : ℝ) ∈ Set.Icc (-(R : ℝ)) (R : ℝ) :=
    ⟨neg_nonpos_of_nonneg R.coe_nonneg, R.coe_nonneg⟩
  have hpl : IsPicardLindelof (fun _ => f)
      (⟨0, ht₀⟩ : Set.Icc (-(R : ℝ)) (R : ℝ)) x₀
      (M * R) 0 M K :=
    IsPicardLindelof.of_time_independent
      (fun x _ => hb x) hl.lipschitzOnWith (by
        simp only [NNReal.coe_mul, NNReal.coe_zero, sub_zero,
          sub_neg_eq_add, zero_add, max_self]
        simp)
  obtain ⟨α, hα0, hα⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (Metric.mem_closedBall_self le_rfl)
  refine ⟨α, hα0, fun t ht => ?_⟩
  exact (hα t (Set.Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- A bounded globally Lipschitz autonomous field has a global
integral curve through every initial point. -/
theorem exists_isIntegralCurve {f : E → E} {K M : ℝ≥0}
    (hl : LipschitzWith K f) (hb : ∀ x, ‖f x‖ ≤ M)
    (x₀ : E) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧
      ∀ t : ℝ, HasDerivAt γ (f (γ t)) t := by
  have hsol : ∀ n : ℕ, ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivAt α (f (α t)) t := by
    intro n
    have hcast : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) =
        (n : ℝ) + 1 := by push_cast; ring
    have := exists_solution_Ioo hl hb x₀ ((n : ℝ≥0) + 1)
    rwa [hcast] at this
  choose α hα0 hα using hsol
  have huniq : ∀ (a b : ℕ) (t : ℝ),
      t ∈ Set.Ioo (-((a : ℝ) + 1)) ((a : ℝ) + 1) →
      t ∈ Set.Ioo (-((b : ℝ) + 1)) ((b : ℝ) + 1) →
      α a t = α b t := by
    intro a b t hta htb
    have hca : min (a : ℝ) (b : ℝ) ≤ (a : ℝ) :=
      min_le_left _ _
    have hcb : min (a : ℝ) (b : ℝ) ≤ (b : ℝ) :=
      min_le_right _ _
    have hmn : (0 : ℝ) ≤ min (a : ℝ) (b : ℝ) :=
      le_min (Nat.cast_nonneg a) (Nat.cast_nonneg b)
    have ht0 : (0 : ℝ) ∈
        Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1))
          (min (a : ℝ) (b : ℝ) + 1) :=
      ⟨by linarith, by linarith⟩
    have hsa : Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1))
        (min (a : ℝ) (b : ℝ) + 1) ⊆
        Set.Ioo (-((a : ℝ) + 1)) ((a : ℝ) + 1) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith)
    have hsb : Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1))
        (min (a : ℝ) (b : ℝ) + 1) ⊆
        Set.Ioo (-((b : ℝ) + 1)) ((b : ℝ) + 1) :=
      Set.Ioo_subset_Ioo (by linarith) (by linarith)
    have htc : t ∈ Set.Ioo (-(min (a : ℝ) (b : ℝ) + 1))
        (min (a : ℝ) (b : ℝ) + 1) := by
      rcases min_choice (a : ℝ) (b : ℝ) with h | h
      · rw [h]; exact hta
      · rw [h]; exact htb
    exact ODE_solution_unique_of_mem_Ioo (v := fun _ => f)
      (s := fun _ => Set.univ)
      (fun _ _ => hl.lipschitzOnWith) ht0
      (fun s hs => ⟨hα a s (hsa hs), Set.mem_univ _⟩)
      (fun s hs => ⟨hα b s (hsb hs), Set.mem_univ _⟩)
      (by rw [hα0 a, hα0 b]) htc
  have hmem : ∀ t : ℝ,
      t ∈ Set.Ioo (-((⌊|t|⌋₊ : ℝ) + 1))
        ((⌊|t|⌋₊ : ℝ) + 1) := fun t =>
    Set.mem_Ioo.mpr (abs_lt.mp (Nat.lt_floor_add_one |t|))
  refine ⟨fun t => α ⌊|t|⌋₊ t, hα0 ⌊|(0 : ℝ)|⌋₊, fun t => ?_⟩
  have hEq : (fun s => α ⌊|s|⌋₊ s) =ᶠ[nhds t]
      α ⌊|t|⌋₊ :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds (hmem t))
      (fun s hs => huniq ⌊|s|⌋₊ ⌊|t|⌋₊ s (hmem s) hs)
  exact (hα ⌊|t|⌋₊ t (hmem t)).congr_of_eventuallyEq hEq

end PhosphorylationStableCapacity.BoundedODE
