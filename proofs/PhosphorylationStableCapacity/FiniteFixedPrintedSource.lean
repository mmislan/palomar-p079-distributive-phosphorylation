module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- Once the fixed coefficient lists and the coalesced complexes are certified
positive, all printed states are positive equilibria of one common literal
unrelaxed rate vector with the three printed totals. -/
theorem finiteFixedPrinted_source_of_coeff_positive
    (m : ℕ)
    (hD : DensePositive
      (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hB : DensePositive
      (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hcoalD : ∀ i : Fin (m + 1),
      0 < (coalescedFiniteState m (finiteFixedRadius m)).D i)
    (j : Fin (2 * m + 1))
    (hroot : 1 < offsetSplitRoot (finiteFixedOffset m)
      (finiteFixedSpacing m) j.val) :
    (finiteFixedPrintedRates m).Positive ∧
      (finiteFixedPrintedState m j).Positive ∧
      Equilibrium (finiteFixedPrintedRates m)
        (finiteFixedPrintedState m j) ∧
      totalE (finiteFixedPrintedState m j) = 2 * finiteFixedRadius m ∧
      totalF (finiteFixedPrintedState m j) = 2 ∧
      totalS (finiteFixedPrintedState m j) =
        2 * (finiteFixedRadius m + 1) := by
  let r := finiteFixedRadius m
  let δ := finiteFixedSpacing m
  let ξ := finiteFixedOffset m
  let k := arbitrarySplitFiniteRates m ξ r δ
  let x := arbitrarySplitFiniteState m ξ r δ j
  let ℓ : Fin (m + 1) → ℝ :=
    fun i => 1 / (coalescedFiniteState m r).D i
  obtain ⟨hk, hx, heq, hET, hFT, hST⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      m ξ r δ hD hB j hroot
  have hℓ (i : Fin (m + 1)) : 0 < ℓ i :=
    div_pos (by norm_num) (hcoalD i)
  have hC (i : Fin (m + 1)) : kinaseNet k x i = k.c i * x.C i := by
    have h := heq.2.2.2.1 i
    dsimp [field] at h
    linarith
  have hY (i : Fin (m + 1)) :
      phosphataseNet k x i = k.gamma i * x.D i := by
    have h := heq.2.2.2.2 i
    dsimp [field] at h
    linarith
  have hcat (i : Fin (m + 1)) :
      k.c i * x.C i = k.gamma i * x.D i :=
    equilibrium_catalytic_balance k x heq i
  have hE (i : Fin (m + 1)) :
      k.a i * x.S i.castSucc * x.E = (k.b i + k.c i) * x.C i := by
    have hi := hC i
    dsimp [kinaseNet] at hi
    linarith
  have hF (i : Fin (m + 1)) :
      k.alpha i * x.S i.succ * x.F =
        (k.beta i + k.gamma i) * x.D i := by
    have hi := hY i
    dsimp [phosphataseNet] at hi
    linarith
  have hpositive : (retune k ℓ (fun _ => 1) (fun _ => 1)).Positive :=
    retune_positive k ℓ (fun _ => 1) (fun _ => 1) hk hℓ
      (fun _ => by norm_num) (fun _ => by norm_num)
  have hretune : Equilibrium (retune k ℓ (fun _ => 1) (fun _ => 1)) x :=
    retune_equilibrium k x ℓ (fun _ => 1) (fun _ => 1)
      hk hE hF hcat
  exact ⟨hpositive, hx, hretune, hET, hFT, hST⟩

end
end PhosphorylationStableCapacity
