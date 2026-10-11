module
public import proofs.PhosphorylationStableCapacity.RateSelectedInversePairDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- If a differentiable map of two class-coordinate arguments vanishes
on the zero second section and is linear on the fixed first section,
its derivative at that section depends only on the second direction. -/
theorem fderiv_pair_zero_first_linear_second {n : ℕ}
    (g : CoordinateSpace n × CoordinateSpace n → CoordinateSpace n)
    (u : CoordinateSpace n)
    (hg : DifferentiableAt ℝ g (u, 0))
    (hzero : ∀ z, g (z, 0) = 0)
    (L : CoordinateSpace n →L[ℝ] CoordinateSpace n)
    (hsection : ∀ v, g (u, v) = L v)
    (p : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ g (u, 0) p = L p.2 := by
  let D := fderiv ℝ g (u, 0)
  have hleft : ∀ a : CoordinateSpace n, D (a, 0) = 0 := by
    intro a
    have hemb : DifferentiableAt ℝ
        (fun z : CoordinateSpace n => (z, (0 : CoordinateSpace n))) u := by
      fun_prop
    have hc := fderiv_comp u hg hemb
    have hfun : (fun z : CoordinateSpace n => g (z, 0)) =
        fun _ => (0 : CoordinateSpace n) := by
      funext z
      exact hzero z
    have hderiv : fderiv ℝ
        (fun z : CoordinateSpace n => (z, (0 : CoordinateSpace n))) u =
        (ContinuousLinearMap.id ℝ (CoordinateSpace n)).prod 0 := by
      have hfirst : DifferentiableAt ℝ
          (fun z : CoordinateSpace n => z) u := by fun_prop
      have hsecond : DifferentiableAt ℝ
          (fun _ : CoordinateSpace n => (0 : CoordinateSpace n)) u := by fun_prop
      simpa using hfirst.fderiv_prodMk hsecond
    change fderiv ℝ (fun z : CoordinateSpace n => g (z, 0)) u =
      D.comp (fderiv ℝ
        (fun z : CoordinateSpace n => (z, (0 : CoordinateSpace n))) u) at hc
    rw [hfun, fderiv_const_apply, hderiv] at hc
    have ha := congrArg (fun T : CoordinateSpace n →L[ℝ] CoordinateSpace n => T a) hc
    simpa [D] using ha.symm
  have hright : ∀ b : CoordinateSpace n, D (0, b) = L b := by
    intro b
    have hemb : DifferentiableAt ℝ
        (fun z : CoordinateSpace n => (u, z)) 0 := by fun_prop
    have hc := fderiv_comp (0 : CoordinateSpace n) hg hemb
    have hfun : (fun z : CoordinateSpace n => g (u, z)) = L := by
      funext z
      exact hsection z
    have hderiv : fderiv ℝ (fun z : CoordinateSpace n => (u, z)) 0 =
        (0 : CoordinateSpace n →L[ℝ] CoordinateSpace n).prod
          (ContinuousLinearMap.id ℝ (CoordinateSpace n)) := by
      have hfirst : DifferentiableAt ℝ
          (fun _ : CoordinateSpace n => u) 0 := by fun_prop
      have hsecond : DifferentiableAt ℝ
          (fun z : CoordinateSpace n => z) 0 := by fun_prop
      simpa using hfirst.fderiv_prodMk hsecond
    change fderiv ℝ (fun z : CoordinateSpace n => g (u, z)) 0 =
      D.comp (fderiv ℝ (fun z : CoordinateSpace n => (u, z)) 0) at hc
    rw [hfun, ContinuousLinearMap.fderiv, hderiv] at hc
    have hb := congrArg (fun T : CoordinateSpace n →L[ℝ] CoordinateSpace n => T b) hc
    simpa [D] using hb.symm
  rcases p with ⟨a, b⟩
  change D (a, b) = L b
  have hp : (a, b) = (a, (0 : CoordinateSpace n)) + (0, b) := by
    simp
  rw [hp, map_add, hleft, hright, zero_add]

/-- The derivative of the explicit inverse response at zero velocity is
the fixed-state linear inverse applied to the velocity direction. -/
theorem fderiv_selectedRateRightInverse_pair_zero {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (p : CoordinateSpace n × CoordinateSpace n) :
    fderiv ℝ (fun q : CoordinateSpace n × CoordinateSpace n =>
      selectedRateRightInverse (stateFromLoaded ET FT ST q.1) q.2)
        (u, 0) p =
      (selectedRateRightInverseLinear
        (stateFromLoaded ET FT ST u)).toContinuousLinearMap p.2 := by
  apply fderiv_pair_zero_first_linear_second
    (fun q : CoordinateSpace n × CoordinateSpace n =>
      selectedRateRightInverse (stateFromLoaded ET FT ST q.1) q.2)
    u (differentiableAt_selectedRateRightInverse_pair ET FT ST u 0 hx)
    (by intro z; ext i <;> simp [selectedRateRightInverse])
    (selectedRateRightInverseLinear
      (stateFromLoaded ET FT ST u)).toContinuousLinearMap
    (by intro v; rfl) p

end
end PhosphorylationStableCapacity
