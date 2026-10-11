module
public import proofs.PhosphorylationStableCapacity.MetzlerWeighted

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A strict Metzler limit with a common positive negative-action vector
gives Hurwitz matrices eventually. This transfer asks for convergence of
each entry and of each finite weighted row sum. -/
theorem eventually_hurwitz_of_strict_metzler_limit
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (A : α → Matrix ι ι ℝ) (B : Matrix ι ι ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hentry : ∀ i j, Filter.Tendsto (fun t => A t i j) l (nhds (B i j)))
    (haction : ∀ i, Filter.Tendsto (fun t => ∑ j, A t i j * w j)
      l (nhds (∑ j, B i j * w j)))
    (hoff : ∀ i j, i ≠ j → 0 < B i j)
    (hcert : ∀ i, ∑ j, B i j * w j < 0) :
    ∀ᶠ t in l, IsHurwitz (A t) := by
  have hOffEventually : ∀ᶠ t in l, ∀ i j, i ≠ j → 0 ≤ A t i j := by
    suffices h : ∀ᶠ t in l, ∀ i ∈ (Finset.univ : Finset ι),
        ∀ j ∈ (Finset.univ : Finset ι), i ≠ j → 0 ≤ A t i j by
      simpa using h
    apply (Filter.eventually_all_finset (Finset.univ : Finset ι)).2
    intro i _
    apply (Filter.eventually_all_finset (Finset.univ : Finset ι)).2
    intro j _
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hij))
    · have hpos : ∀ᶠ t in l, 0 < A t i j :=
        (hentry i j).eventually (isOpen_Ioi.mem_nhds (hoff i j hij))
      exact hpos.mono (fun _ hp _ => hp.le)
  have hNegEventually : ∀ᶠ t in l, ∀ i,
      (∑ j, A t i j * w j) < 0 := by
    suffices h : ∀ᶠ t in l, ∀ i ∈ (Finset.univ : Finset ι),
        (∑ j, A t i j * w j) < 0 by
      simpa using h
    apply (Filter.eventually_all_finset (Finset.univ : Finset ι)).2
    intro i _
    exact (haction i).eventually (isOpen_Iio.mem_nhds (hcert i))
  filter_upwards [hOffEventually, hNegEventually] with t htOff htNeg
  exact hurwitz_of_metzler_positive_vector (A t) w hw htOff htNeg

/-- Entrywise convergence alone supplies the weighted row-sum convergence
needed by the strict Metzler limit certificate. -/
theorem eventually_hurwitz_of_entrywise_strict_metzler_limit
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {l : Filter α} (A : α → Matrix ι ι ℝ) (B : Matrix ι ι ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hentry : ∀ i j, Filter.Tendsto (fun t => A t i j) l (nhds (B i j)))
    (hoff : ∀ i j, i ≠ j → 0 < B i j)
    (hcert : ∀ i, ∑ j, B i j * w j < 0) :
    ∀ᶠ t in l, IsHurwitz (A t) := by
  apply eventually_hurwitz_of_strict_metzler_limit A B w hw hentry
    (fun i => ?_) hoff hcert
  apply tendsto_finsetSum (Finset.univ : Finset ι)
  intro j _
  exact (hentry i j).mul tendsto_const_nhds

end
end PhosphorylationStableCapacity
