module
public import proofs.PhosphorylationStableCapacity.ExactCapacity435

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A single positive compatibility class admits `q` distinct nonlinear
locally asymptotically stable equilibria exactly when it has at least `q`
phosphorylation sites. -/
theorem stable_labels_iff_sites_ge
    (n q : ℕ) (hn : 1 ≤ n) :
    NonlinearlyStableClassAttains n q ↔ q ≤ n := by
  constructor
  · rintro ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, hstates⟩
    let x : Fin q → State n :=
      fun j => unChart ET FT ST (ofCoordinateSpace (u j))
    have hxmem : ∀ j, x j ∈ locallyStablePositiveStates ET FT ST k := by
      intro j
      refine ⟨(hstates j).1, unChart_inClass ET FT ST _, ?_⟩
      simpa only [x, chart_unChart, to_ofCoordinateSpace] using (hstates j).2
    have hxinj : Function.Injective x := by
      intro i j hij
      apply hinj
      have h := congrArg (fun z : State n => toCoordinateSpace (chart z)) hij
      simpa only [x, chart_unChart, to_ofCoordinateSpace] using h
    have hsub : Set.range x ⊆ locallyStablePositiveStates ET FT ST k := by
      rintro y ⟨j, rfl⟩
      exact hxmem j
    have hfinite := (all_size_exact_capacity_finite_435 n hn).2
      ET FT ST hET hFT hST k hk
    have hcard : (Set.range x).ncard = q := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hxinj,
        Set.ncard_univ, Nat.card_fin]
    have hle : q ≤ (locallyStablePositiveStates ET FT ST k).ncard := by
      rw [← hcard]
      exact Set.ncard_le_ncard hsub hfinite.1
    exact hle.trans hfinite.2
  · intro hqn
    obtain ⟨k, ET, FT, ST, u, hk, hET, hFT, hST, hinj, hstates⟩ :=
      (all_size_exact_capacity_finite_435 n hn).1
    refine ⟨k, ET, FT, ST, (fun j : Fin q => u (Fin.castLE hqn j)),
      hk, hET, hFT, hST, ?_, ?_⟩
    · intro i j hij
      apply Fin.ext
      have h := hinj hij
      simpa using congrArg Fin.val h
    · intro j
      exact hstates (Fin.castLE hqn j)

/-- `b` independent binary stable-state labels require at least `2^b` sites. -/
theorem stable_bit_labels_iff_sites_ge
    (n b : ℕ) (hn : 1 ≤ n) :
    NonlinearlyStableClassAttains n (2^b) ↔ 2^b ≤ n :=
  stable_labels_iff_sites_ge n (2^b) hn

end

end PhosphorylationStableCapacity
