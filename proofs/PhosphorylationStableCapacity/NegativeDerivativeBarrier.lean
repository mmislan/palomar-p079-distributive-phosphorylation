module
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-
The first-exit proof is adapted from CRNT/Dynamics/Nagumo.lean in
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

namespace PhosphorylationStableCapacity

open Filter Set
open scoped Topology

/-- A differentiable real curve starting nonnegative cannot cross into
the negative half-line when its derivative is nonnegative whenever
its value is negative. -/
theorem nonnegative_of_deriv_nonneg_when_negative
    {g : ℝ → ℝ}
    (hd : ∀ t, HasDerivAt g (deriv g t) t)
    (hin : ∀ t, g t < 0 → 0 ≤ deriv g t)
    (h0 : 0 ≤ g 0) :
    ∀ t, 0 ≤ t → 0 ≤ g t := by
  have hcont : Continuous g := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hd t).continuousAt
  intro T hT
  by_contra hgT
  rw [not_le] at hgT
  set A : Set ℝ := Set.Icc 0 T ∩ {t | 0 ≤ g t}
  have hAne : A.Nonempty := ⟨0, ⟨le_refl 0, hT⟩, h0⟩
  have hAcl : IsClosed A :=
    isClosed_Icc.inter (isClosed_le continuous_const hcont)
  have hAbdd : BddAbove A := ⟨T, fun t ht => ht.1.2⟩
  set t₀ := sSup A
  have ht₀A : t₀ ∈ A := hAcl.csSup_mem hAne hAbdd
  have ht₀0 : 0 ≤ t₀ := ht₀A.1.1
  have ht₀T : t₀ ≤ T := ht₀A.1.2
  have hgt₀ : 0 ≤ g t₀ := ht₀A.2
  have ht₀ltT : t₀ < T :=
    lt_of_le_of_ne ht₀T
      (fun h => absurd (h ▸ hgt₀) (not_le.mpr hgT))
  have hneg_after : ∀ t, t₀ < t → t ≤ T → g t < 0 := by
    intro t htlt htle
    by_contra hle
    rw [not_lt] at hle
    exact absurd
      (le_csSup hAbdd ⟨⟨le_trans ht₀0 htlt.le, htle⟩, hle⟩)
      (not_le.mpr htlt)
  have hgt₀eq : g t₀ = 0 := by
    refine le_antisymm ?_ hgt₀
    have htend : Tendsto g (𝓝[>] t₀) (𝓝 (g t₀)) :=
      (hcont.continuousAt).continuousWithinAt.tendsto
    refine le_of_tendsto htend ?_
    have hlt : ∀ᶠ t in 𝓝[>] t₀, t < T :=
      eventually_nhdsWithin_of_eventually_nhds
        (eventually_lt_nhds ht₀ltT)
    have hself : ∀ᶠ t in 𝓝[>] t₀, t₀ < t :=
      eventually_mem_nhdsWithin.mono fun t ht => ht
    filter_upwards [hlt, hself] with t htT ht₀t
    exact (hneg_after t ht₀t htT.le).le
  have hmono : MonotoneOn g (Set.Icc t₀ T) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc t₀ T)
      hcont.continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    rw [interior_Icc, Set.mem_Ioo] at ht
    exact hin t (hneg_after t ht.1 ht.2.le)
  have hle : g t₀ ≤ g T :=
    hmono ⟨le_refl t₀, ht₀T⟩ ⟨ht₀T, le_refl T⟩ ht₀T
  rw [hgt₀eq] at hle
  exact absurd hle (not_le.mpr hgT)

end PhosphorylationStableCapacity
