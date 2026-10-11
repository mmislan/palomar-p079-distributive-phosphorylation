module
public import proofs.PhosphorylationStableCapacity.ReadoutDerivative435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitDifferentiability

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

private theorem moving_split_ratio_hasDerivAt (a : ℝ) :
    HasDerivAt (fun δ : ℝ => ratio (3+δ*a)) ((3/4)*a) 0 := by
  have hx : HasDerivAt (fun δ : ℝ => 3+δ*a) a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add 3 using 1
    · funext δ; simp only [id_eq]; ring
    · simp
  have hu : HasDerivAt ratio (3/4) 3 := by
    convert (((hasDerivAt_id (3 : ℝ)).pow 2).sub_const 1).div_const 8 using 1
    · funext x; rfl
    · norm_num
  have houter : HasDerivAt ratio (3/4) (3+0*a) := by simpa using hu
  convert houter.comp 0 hx using 1
  · funext δ; rfl

/-- Evaluation of the arbitrary conversion polynomial at a moving real
argument is differentiable in the root-separation parameter. -/
theorem arbitrarySplitRawD_moving_eval_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (u : ℝ → ℝ) (hu : Differentiable ℝ u) :
    Differentiable ℝ (fun δ =>
      (arbitrarySplitRawD m ξ r δ).eval (u δ)) := by
  have hsum : Differentiable ℝ (fun δ : ℝ =>
      ∑ i ∈ Finset.range (m+1),
        (arbitrarySplitRawD m ξ r δ).coeff i * (u δ)^i) := by
    apply Differentiable.fun_sum
    intro i hi
    exact (arbitrarySplitRawD_coeff_differentiable m ξ r hr i).mul (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range'
    (show (arbitrarySplitRawD m ξ r δ).natDegree < m+1 by
      have hle := natDegree_le_iff_coeff_eq_zero.mpr
        (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).1)
      omega) (u δ)

/-- The moving-polynomial coefficient derivative cancels when two roots
are compared. Only the fixed coalesced polynomial derivative remains. -/
theorem arbitrarySplitRawD_eval_difference_hasDerivAt_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r a b : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun δ : ℝ =>
      (arbitrarySplitRawD m ξ r δ).eval (ratio (3+δ*a)) -
        (arbitrarySplitRawD m ξ r δ).eval (ratio (3+δ*b)))
      ((coalescedRawD m r).derivative.eval 1 * (3/4) * (a-b)) 0 := by
  let D : ℝ → ℝ[X] := fun δ => arbitrarySplitRawD m ξ r δ
  have hua := moving_split_ratio_hasDerivAt a
  have hub := moving_split_ratio_hasDerivAt b
  have hterm (i : ℕ) :
      HasDerivAt (fun δ : ℝ => (D δ).coeff i *
        ((ratio (3+δ*a))^i-(ratio (3+δ*b))^i))
        ((D 0).coeff i * ((i : ℝ)*(3/4)*(a-b))) 0 := by
    have hpow : HasDerivAt (fun δ : ℝ =>
        (ratio (3+δ*a))^i-(ratio (3+δ*b))^i)
        ((i : ℝ)*(3/4)*(a-b)) 0 := by
      convert (hua.pow i).sub (hub.pow i) using 1
      · norm_num [ratio]; ring
    have hc : HasDerivAt (fun δ => (D δ).coeff i)
        (deriv (fun δ => (D δ).coeff i) 0) 0 :=
      (arbitrarySplitRawD_coeff_differentiable m ξ r hr i).differentiableAt.hasDerivAt
    convert hc.mul hpow using 1
    · norm_num [ratio]
  have hsum := HasDerivAt.fun_sum (u := Finset.range (m+1))
    (fun i _ => hterm i)
  have hsum_eq : (fun δ : ℝ => ∑ i ∈ Finset.range (m+1),
      (D δ).coeff i * ((ratio (3+δ*a))^i-(ratio (3+δ*b))^i)) =
      (fun δ : ℝ => (D δ).eval (ratio (3+δ*a)) -
        (D δ).eval (ratio (3+δ*b))) := by
    funext δ
    have hdeg : (D δ).natDegree < m+1 := by
      change (arbitrarySplitRawD m ξ r δ).natDegree < m+1
      have hle := natDegree_le_iff_coeff_eq_zero.mpr
        (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).1)
      omega
    rw [eval_eq_sum_range' hdeg, eval_eq_sum_range' hdeg,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hsum_eq]
  convert hsum using 1
  have hdeg : (D 0).natDegree ≤ m := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact (arbitrarySplitRaw_coeff_zero_above m ξ r 0 i hi).1
  have hmom := derivative_eval_one_eq_coeff_moment (D 0) m hdeg
  rw [show D 0 = coalescedRawD m r by
    simp [D, arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced]] at hmom ⊢
  rw [hmom]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private def splitReadoutNumerator (m : ℕ) (x : ℝ) : ℝ :=
  (ratio x)^m * ((x-1)*(x+5)/(x+1))

private theorem splitReadoutNumerator_hasDerivAt_three (m : ℕ) :
    HasDerivAt (splitReadoutNumerator m) ((m : ℝ)*3+3/2) 3 := by
  have hu : HasDerivAt ratio (3/4) 3 := by
    convert (((hasDerivAt_id (3 : ℝ)).pow 2).sub_const 1).div_const 8 using 1
    · funext x; rfl
    · norm_num
  have hg : HasDerivAt (fun x : ℝ => (x-1)*(x+5)/(x+1)) (3/2) 3 := by
    convert (((hasDerivAt_id (3 : ℝ)).sub_const 1).mul
      ((hasDerivAt_id (3 : ℝ)).add_const 5)).div
      ((hasDerivAt_id (3 : ℝ)).add_const 1) (by norm_num) using 1
    · funext x; rfl
    · norm_num
  convert (hu.pow m).mul hg using 1
  · funext x; rfl
  · norm_num [ratio]; ring

private theorem splitReadoutNumerator_three (m : ℕ) :
    splitReadoutNumerator m 3 = 4 := by
  norm_num [splitReadoutNumerator, ratio]

private theorem splitReadoutScalar_eq (m : ℕ) (D : ℝ[X]) (x : ℝ) :
    splitReadoutScalar m D x =
      (D.coeff m / 2) * splitReadoutNumerator m x / D.eval (ratio x) := by
  simp only [splitReadoutScalar, splitReadoutNumerator, div_eq_mul_inv]
  ring

private theorem moving_split_readout_numerator_difference_hasDerivAt_zero
    (m : ℕ) (a b : ℝ) :
    HasDerivAt (fun δ : ℝ =>
      splitReadoutNumerator m (3+δ*a) -
        splitReadoutNumerator m (3+δ*b))
      (((m : ℝ)*3+3/2)*(a-b)) 0 := by
  have ha : HasDerivAt (fun δ : ℝ => 3+δ*a) a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul a).const_add 3 using 1
    · funext δ; simp only [id_eq]; ring
    · simp
  have hb : HasDerivAt (fun δ : ℝ => 3+δ*b) b 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul b).const_add 3 using 1
    · funext δ; simp only [id_eq]; ring
    · simp
  have hnum := splitReadoutNumerator_hasDerivAt_three m
  have hna : HasDerivAt (fun δ => splitReadoutNumerator m (3+δ*a))
      (((m : ℝ)*3+3/2)*a) 0 := by
    have houter : HasDerivAt (splitReadoutNumerator m) ((m : ℝ)*3+3/2)
        (3+0*a) := by simpa using hnum
    convert houter.comp 0 ha using 1
    · funext δ; rfl
  have hnb : HasDerivAt (fun δ => splitReadoutNumerator m (3+δ*b))
      (((m : ℝ)*3+3/2)*b) 0 := by
    have houter : HasDerivAt (splitReadoutNumerator m) ((m : ℝ)*3+3/2)
        (3+0*b) := by simpa using hnum
    convert houter.comp 0 hb using 1
    · funext δ; rfl
  convert hna.sub hnb using 1
  ring

/-- Differentiating a difference with one shared parameter factor cancels
the derivative of that factor at coincident base points. -/
private theorem shared_quotient_difference_hasDerivAt_zero
    (c A B C D : ℝ → ℝ) (a' b' c' d' : ℝ)
    (hc : DifferentiableAt ℝ c 0)
    (hA : HasDerivAt A a' 0) (hB : HasDerivAt B b' 0)
    (hC : HasDerivAt C c' 0) (hD : HasDerivAt D d' 0)
    (hAC : A 0 = C 0) (hBD : B 0 = D 0)
    (hB0 : B 0 ≠ 0) :
    HasDerivAt (fun δ => c δ * (A δ / B δ - C δ / D δ))
      (c 0 * (((a'-c')*B 0 - A 0*(b'-d'))/(B 0)^2)) 0 := by
  have hD0 : D 0 ≠ 0 := by simpa [← hBD] using hB0
  have h := hc.hasDerivAt.mul
    ((hA.div hB hB0).sub (hC.div hD hD0))
  convert h using 1
  simp only [Pi.sub_apply, Pi.div_apply]
  rw [← hAC, ← hBD]
  field_simp [hB0]
  ring

/-- First-order readout separation uses the same varying conversion
polynomial at both roots; its parameter derivative cancels exactly. -/
theorem arbitrarySplitReadout_scalar_difference_hasDerivAt_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r a b : ℝ) (hr : r ≠ 0)
    (hD₀ : (coalescedRawD m r).eval 1 ≠ 0) :
    HasDerivAt (fun δ : ℝ =>
      splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*a) -
        splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*b))
      ((a-b) * deriv (splitReadoutScalar m (coalescedRawD m r)) 3) 0 := by
  let D : ℝ → ℝ[X] := fun δ => arbitrarySplitRawD m ξ r δ
  let A : ℝ → ℝ := fun δ => splitReadoutNumerator m (3+δ*a)
  let C : ℝ → ℝ := fun δ => splitReadoutNumerator m (3+δ*b)
  let B : ℝ → ℝ := fun δ => (D δ).eval (ratio (3+δ*a))
  let E : ℝ → ℝ := fun δ => (D δ).eval (ratio (3+δ*b))
  let c : ℝ → ℝ := fun δ => (D δ).coeff m / 2
  have hDzero : D 0 = coalescedRawD m r := by
    simp [D, arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced]
  have hroot (t : ℝ) : HasDerivAt (fun δ : ℝ => 3+δ*t) t 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul t).const_add 3 using 1
    · funext δ; simp only [id_eq]; ring
    · simp
  have hA : HasDerivAt A (((m : ℝ)*3+3/2)*a) 0 := by
    have houter : HasDerivAt (splitReadoutNumerator m) ((m : ℝ)*3+3/2)
        (3+0*a) := by simpa using splitReadoutNumerator_hasDerivAt_three m
    convert houter.comp 0 (hroot a) using 1
    · funext δ; rfl
  have hC : HasDerivAt C (((m : ℝ)*3+3/2)*b) 0 := by
    have houter : HasDerivAt (splitReadoutNumerator m) ((m : ℝ)*3+3/2)
        (3+0*b) := by simpa using splitReadoutNumerator_hasDerivAt_three m
    convert houter.comp 0 (hroot b) using 1
    · funext δ; rfl
  have hu (t : ℝ) : Differentiable ℝ (fun δ : ℝ => ratio (3+δ*t)) := by
    change Differentiable ℝ (fun δ : ℝ => ((3+δ*t)^2-1)/8)
    fun_prop
  have hB : HasDerivAt B (deriv B 0) 0 :=
    (arbitrarySplitRawD_moving_eval_differentiable m ξ r hr _ (hu a)).differentiableAt.hasDerivAt
  have hE : HasDerivAt E (deriv E 0) 0 :=
    (arbitrarySplitRawD_moving_eval_differentiable m ξ r hr _ (hu b)).differentiableAt.hasDerivAt
  have hc : DifferentiableAt ℝ c 0 := by
    exact (arbitrarySplitRawD_coeff_differentiable m ξ r hr m).differentiableAt.div_const 2
  have hAC : A 0 = C 0 := by simp [A, C]
  have hBE : B 0 = E 0 := by simp [B, E]
  have hB0 : B 0 ≠ 0 := by
    change (D 0).eval (ratio (3+0*a)) ≠ 0
    rw [hDzero]
    have hratio3 : ratio (3 : ℝ) = 1 := by norm_num [ratio]
    simpa only [zero_mul, add_zero, hratio3] using hD₀
  have hBder : deriv B 0 - deriv E 0 =
      (coalescedRawD m r).derivative.eval 1 * (3/4) * (a-b) := by
    have hdiff := arbitrarySplitRawD_eval_difference_hasDerivAt_zero m ξ r a b hr
    have hsub := (hB.sub hE).deriv
    exact hsub.symm.trans hdiff.deriv
  have hshared := shared_quotient_difference_hasDerivAt_zero
    c A B C E _ _ _ _ hc hA hB hC hE hAC hBE hB0
  convert hshared using 1
  · funext δ
    simp only [splitReadoutScalar_eq]
    dsimp [c, A, B, C, D, E]
    ring
  · rw [(splitReadoutScalar_hasDerivAt_three m (coalescedRawD m r) hD₀).deriv]
    rw [hBder]
    simp only [c, A, B, zero_mul, add_zero, hDzero]
    norm_num [ratio, splitReadoutNumerator]
    field_simp [hD₀]
    ring

theorem arbitrarySplitReadout_scalar_spacing_limit
    (m : ℕ) (ξ : ℕ → ℝ) (r a b : ℝ) (hr : r ≠ 0)
    (hD₀ : (coalescedRawD m r).eval 1 ≠ 0) :
    Tendsto (fun δ : ℝ =>
      (splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*a) -
        splitReadoutScalar m (arbitrarySplitRawD m ξ r δ) (3+δ*b)) / δ)
      (𝓝[>] 0)
      (𝓝 ((a-b) * deriv (splitReadoutScalar m (coalescedRawD m r)) 3)) := by
  have h := (arbitrarySplitReadout_scalar_difference_hasDerivAt_zero
    m ξ r a b hr hD₀).tendsto_slope_zero_right
  convert h using 1
  funext δ
  simp only [zero_add, zero_mul, add_zero, sub_self, sub_zero,
    smul_eq_mul, div_eq_mul_inv]
  ring

/-- The first-order separation limit holds for the actual fully
phosphorylated species readouts of two members of the common-class split
family. -/
theorem arbitrarySplitReadout_actual_spacing_limit
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD m r) m)
    (hB₀ : DensePositive (coalescedRawB m r) m)
    (j k : Fin (2*m+1)) :
    Tendsto (fun δ : ℝ =>
      (fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) -
        fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)) / δ)
      (𝓝[>] 0)
      (𝓝 ((ξ j.val-ξ k.val) *
        deriv (splitReadoutScalar m (coalescedRawD m r)) 3)) := by
  have hDnear := arbitrarySplit_conversion_positive_near_zero
    m ξ r hr hD₀ hB₀
  have hroot (i : Fin (2*m+1)) :
      ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
        1 < offsetSplitRoot ξ δ i.val := by
    have hc : Continuous (fun δ : ℝ => offsetSplitRoot ξ δ i.val) := by
      unfold offsetSplitRoot
      fun_prop
    have ht : Tendsto (fun δ : ℝ => offsetSplitRoot ξ δ i.val)
        (𝓝[>] (0 : ℝ)) (𝓝 (3 : ℝ)) := by
      simpa [offsetSplitRoot] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact ht.eventually (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 3))
  have heq : (fun δ : ℝ =>
      (fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) -
        fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)) / δ) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ =>
        (splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
          (3+δ*ξ j.val) -
         splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
          (3+δ*ξ k.val)) / δ) := by
    filter_upwards [hDnear, hroot j, hroot k] with δ hDB hj hk
    rw [show fullyPhosphorylatedReadout m
          (arbitrarySplitFiniteState m ξ r δ j) =
          splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
            (offsetSplitRoot ξ δ j.val) by
          simpa only [splitReadoutScalar] using
            arbitrarySplitReadout_closed_form m ξ r δ hDB.1 j hj,
        show fullyPhosphorylatedReadout m
          (arbitrarySplitFiniteState m ξ r δ k) =
          splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
            (offsetSplitRoot ξ δ k.val) by
          simpa only [splitReadoutScalar] using
            arbitrarySplitReadout_closed_form m ξ r δ hDB.1 k hk]
    simp only [offsetSplitRoot]
  have hval : (coalescedRawD m r).eval 1 ≠ 0 :=
    ne_of_gt (hD₀.eval_pos (by norm_num))
  exact (arbitrarySplitReadout_scalar_spacing_limit m ξ r
    (ξ j.val) (ξ k.val) hr hval).congr' heq.symm

end

end PhosphorylationStableCapacity
