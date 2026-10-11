module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSourceFirstOrder435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.CompactAffineSiteFirstOrder435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRateProduct435
public import proofs.PhosphorylationStableCapacity.CompactFiniteScalarBound435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- The coalesced physical rate product is uniformly bounded over a
compact family of positive full-edge factors, with the literal
fixed-binding realization retained. -/
theorem paperFixedBinding_compact_physical_rateProduct_zero_upper
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hbase0 : (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive) :
    ∃ B : ℝ, 0 < B ∧ ∀ w ∈ K,
      |∏ i : Fin (m+2),
        let k := paperFixedBindingSplitRates m ξ r 0 ε w
        (k.b i+k.c i)*k.alpha i*k.gamma i| ≤ B := by
  classical
  let base := arbitrarySplitFiniteRates (m+1) ξ r 0
  let f (i : Fin (m+2)) (w : Fin (m+2) → ℝ) : ℝ :=
    ((1+w i*base.c i)*(1+w i)*(base.alpha i/2)*w i)/ε^2
  have hcont : Continuous (fun w : Fin (m+2) → ℝ =>
      ∏ i : Fin (m+2), f i w) := by
    apply continuous_finsetProd
    intro i hi
    dsimp [f]
    fun_prop
  obtain ⟨B, hB, hbound⟩ :=
    compact_finite_scalar_abs_upper K hK
      (fun (_ : Unit) w => ∏ i : Fin (m+2), f i w)
      (fun _ => hcont.continuousOn)
  refine ⟨B, hB, ?_⟩
  intro w hw
  dsimp only [paperFixedBindingSplitRates]
  rw [paperFixedBinding_split_relaxed_rateProduct_product
    m ξ r 0 ε w (hKpos w hw) hbase0]
  exact hbound w hw ()

/-- The literal product of the six physical fixed-binding rate arrays has
one first-order split-parameter bound over every compact family of
positive full-edge factors.  This is the rate-dependent part of the
printed physical slow-eigenvalue coefficient. -/
theorem paperFixedBinding_compact_physical_rateProduct_first_order
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hr : r ≠ 0) (_hε : 0 < ε)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase0 : (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ w ∈ K,
          |(∏ i : Fin (m+2),
              let k := paperFixedBindingSplitRates m ξ r δ ε w
              (k.b i+k.c i)*k.alpha i*k.gamma i) -
            (∏ i : Fin (m+2),
              let k := paperFixedBindingSplitRates m ξ r 0 ε w
              (k.b i+k.c i)*k.alpha i*k.gamma i)| ≤ C*|δ| := by
  classical
  let n := m+2
  let base (δ : ℝ) := arbitrarySplitFiniteRates (m+1) ξ r δ
  let T (i : Fin n) (w : Fin n → ℝ) : ℝ :=
    ((1+w i)*w i)/(2*ε^2)
  let f (i : Fin n) (w : Fin n → ℝ) (δ : ℝ) : ℝ :=
    T i w*(1+w i*(base δ).c i)*(base δ).alpha i
  obtain ⟨A, B, hA, hB, hbase, hsourceFirst⟩ :=
    paperFixedBinding_source_alpha_c_finite_first_order
      m ξ r hr hD₀ hB₀
  obtain ⟨Mw, hMw, hwbound⟩ :=
    compact_finite_scalar_abs_upper K hK
      (fun i w => w i)
      (fun i => (continuous_apply i).continuousOn)
  have hTcontinuous (i : Fin n) : ContinuousOn (T i) K := by
    have hi : Continuous (fun w : Fin n → ℝ => w i) :=
      continuous_apply i
    exact (((continuous_const.add hi).mul hi).div_const
      (2*ε^2)).continuousOn
  obtain ⟨Mt, hMt, hTbound⟩ :=
    compact_finite_scalar_abs_upper K hK T hTcontinuous
  let M := max 1 (max Mw Mt)
  have hM : 1 ≤ M := le_max_left ..
  have hw (w : Fin n → ℝ) (h : w ∈ K) (i : Fin n) :
      |w i| ≤ M :=
    (hwbound w h i).trans
      ((le_max_left Mw Mt).trans (le_max_right 1 (max Mw Mt)))
  have hT (w : Fin n → ℝ) (h : w ∈ K) (i : Fin n) :
      |T i w| ≤ M :=
    (hTbound w h i).trans
      ((le_max_right Mw Mt).trans (le_max_right 1 (max Mw Mt)))
  have hsite := compact_affine_site_first_order
    K (fun i w => w i) T
      (fun i δ => (base δ).c i)
      (fun i δ => (base δ).alpha i)
      M A B hM hA.le hB.le hw hT hbase hsourceFirst
  let Af := M*((1+M*(B+A))*A+M*A*B)
  let Bf := max 1 (M*(1+M*(B+A))*(B+A))
  have hAf : 0 ≤ Af := by dsimp [Af]; positivity
  have hBf : 1 ≤ Bf := le_max_left ..
  have hfirst : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ w ∈ K, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        |f i w δ-f i w 0| ≤ Af*|δ| := by
    filter_upwards [hsite] with δ hd w hwK i hi
    exact (hd w hwK i).1
  have hbound : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ w ∈ K, ∀ i ∈ (Finset.univ : Finset (Fin n)),
        |f i w δ| ≤ Bf ∧ |f i w 0| ≤ Bf := by
    filter_upwards [hsite] with δ hd w hwK i hi
    exact ⟨(hd w hwK i).2.1.trans (le_max_right ..),
      (hd w hwK i).2.2.trans (le_max_right ..)⟩
  obtain ⟨C, hC, hprod⟩ :=
    uniform_finite_product_first_order
      (Finset.univ : Finset (Fin n)) K f
      Af Bf hAf hBf hfirst hbound
  have hphysical (w : Fin n → ℝ) (hwK : w ∈ K)
      (δ : ℝ) (hb : (base δ).Positive) :
      (∏ i : Fin n,
        let k := paperFixedBindingSplitRates m ξ r δ ε w
        (k.b i+k.c i)*k.alpha i*k.gamma i) =
        ∏ i : Fin n, f i w δ := by
    dsimp only [paperFixedBindingSplitRates]
    rw [paperFixedBinding_split_relaxed_rateProduct_product
      m ξ r δ ε w (hKpos w hwK) hb]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [f, T, base]
    ring
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsource, hprod] with δ hb hδ w hwK
  rw [hphysical w hwK δ hb,
    hphysical w hwK 0 hbase0]
  exact hδ w hwK

end

end PhosphorylationStableCapacity
