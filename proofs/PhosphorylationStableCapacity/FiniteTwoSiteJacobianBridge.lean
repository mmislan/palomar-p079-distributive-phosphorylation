module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteManuscriptWitness
public import proofs.PhosphorylationStableCapacity.Jacobian
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSink0Spectral
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSink2Spectral

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Module
open scoped Matrix

set_option maxHeartbeats 2000000

private def twoSiteFreeS0 (ST : ℝ) (u : CoordinateSpace 2) : ℝ :=
  ST - u.1 0 - u.1 1 - u.2.1 0 - u.2.1 1 - u.2.2 0 - u.2.2 1

private def twoSiteFreeE (ET : ℝ) (u : CoordinateSpace 2) : ℝ :=
  ET - u.2.1 0 - u.2.1 1

private def twoSiteFreeF (FT : ℝ) (u : CoordinateSpace 2) : ℝ :=
  FT - u.2.2 0 - u.2.2 1

private def twoSiteField (ET FT ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 :=
  (![k.c 0 * u.2.1 0 - k.alpha 0 * u.1 0 * twoSiteFreeF FT u +
      k.beta 0 * u.2.2 0 - k.a 1 * u.1 0 * twoSiteFreeE ET u +
      k.b 1 * u.2.1 1 + k.gamma 1 * u.2.2 1,
     k.c 1 * u.2.1 1 - k.alpha 1 * u.1 1 * twoSiteFreeF FT u +
      k.beta 1 * u.2.2 1],
   (![k.a 0 * twoSiteFreeS0 ST u * twoSiteFreeE ET u -
      (k.b 0 + k.c 0) * u.2.1 0,
     k.a 1 * u.1 0 * twoSiteFreeE ET u -
      (k.b 1 + k.c 1) * u.2.1 1],
    ![k.alpha 0 * u.1 0 * twoSiteFreeF FT u -
      (k.beta 0 + k.gamma 0) * u.2.2 0,
      k.alpha 1 * u.1 1 * twoSiteFreeF FT u -
      (k.beta 1 + k.gamma 1) * u.2.2 1]))

private theorem fin3_cases_one (a : ℝ) (f : Fin 2 → ℝ) :
    Fin.cases a f (1 : Fin 3) = f 0 := by
  rfl

private theorem fin3_cases_two (a : ℝ) (f : Fin 2 → ℝ) :
    Fin.cases a f (2 : Fin 3) = f 1 := by
  rfl

private theorem restrictedFieldEuclid_twoSite
    (ET FT ST : ℝ) (k : Rates 2) (u : CoordinateSpace 2) :
    restrictedFieldEuclid ET FT ST k u = twoSiteField ET FT ST k u := by
  ext i <;> fin_cases i <;>
    simp [restrictedFieldEuclid, restrictedField, chart, field, unChart,
      ofCoordinateSpace, toCoordinateSpace, kinaseNet, phosphataseNet,
      twoSiteField, twoSiteFreeS0, twoSiteFreeE, twoSiteFreeF,
      Fin.sum_univ_succ, fin3_cases_one] <;> ring

private abbrev TwoPi := Fin 2 → ℝ

private def twoSitePS (i : Fin 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ TwoPi (TwoPi × TwoPi))

private def twoSitePC (i : Fin 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ TwoPi TwoPi).comp
      (ContinuousLinearMap.snd ℝ TwoPi (TwoPi × TwoPi)))

private def twoSitePD (i : Fin 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ TwoPi TwoPi).comp
      (ContinuousLinearMap.snd ℝ TwoPi (TwoPi × TwoPi)))

@[simp] private theorem twoSitePS_apply (i : Fin 2) (u : CoordinateSpace 2) :
    twoSitePS i u = u.1 i := rfl

@[simp] private theorem twoSitePC_apply (i : Fin 2) (u : CoordinateSpace 2) :
    twoSitePC i u = u.2.1 i := rfl

@[simp] private theorem twoSitePD_apply (i : Fin 2) (u : CoordinateSpace 2) :
    twoSitePD i u = u.2.2 i := rfl

private def twoSiteS0Linear : CoordinateSpace 2 →L[ℝ] ℝ :=
  -twoSitePS 0 - twoSitePS 1 - twoSitePC 0 - twoSitePC 1 -
    twoSitePD 0 - twoSitePD 1

private def twoSiteELinear : CoordinateSpace 2 →L[ℝ] ℝ :=
  -twoSitePC 0 - twoSitePC 1

private def twoSiteFLinear : CoordinateSpace 2 →L[ℝ] ℝ :=
  -twoSitePD 0 - twoSitePD 1

private theorem twoSiteFreeS0_hasFDerivAt (ST : ℝ) (u : CoordinateSpace 2) :
    HasFDerivAt (twoSiteFreeS0 ST) twoSiteS0Linear u := by
  convert ((((((((twoSitePS 0).hasFDerivAt.const_sub ST).sub
    (twoSitePS 1).hasFDerivAt).sub (twoSitePC 0).hasFDerivAt).sub
    (twoSitePC 1).hasFDerivAt).sub (twoSitePD 0).hasFDerivAt).sub
    (twoSitePD 1).hasFDerivAt)) using 1
  · funext v; simp [twoSiteFreeS0]
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteS0Linear]

private theorem twoSiteFreeE_hasFDerivAt (ET : ℝ) (u : CoordinateSpace 2) :
    HasFDerivAt (twoSiteFreeE ET) twoSiteELinear u := by
  convert (((twoSitePC 0).hasFDerivAt.const_sub ET).sub
    (twoSitePC 1).hasFDerivAt) using 1
  · funext v; simp [twoSiteFreeE]
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteELinear]

private theorem twoSiteFreeF_hasFDerivAt (FT : ℝ) (u : CoordinateSpace 2) :
    HasFDerivAt (twoSiteFreeF FT) twoSiteFLinear u := by
  convert (((twoSitePD 0).hasFDerivAt.const_sub FT).sub
    (twoSitePD 1).hasFDerivAt) using 1
  · funext v; simp [twoSiteFreeF]
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteFLinear]

private def twoSiteRowS1 (ET FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  k.c 0 • twoSitePC 0 -
    k.alpha 0 • (twoSiteFreeF FT u • twoSitePS 0 + u.1 0 • twoSiteFLinear) +
    k.beta 0 • twoSitePD 0 -
    k.a 1 • (twoSiteFreeE ET u • twoSitePS 0 + u.1 0 • twoSiteELinear) +
    k.b 1 • twoSitePC 1 + k.gamma 1 • twoSitePD 1

private def twoSiteRowS2 (FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  k.c 1 • twoSitePC 1 -
    k.alpha 1 • (twoSiteFreeF FT u • twoSitePS 1 + u.1 1 • twoSiteFLinear) +
    k.beta 1 • twoSitePD 1

private def twoSiteRowC0 (ET ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  k.a 0 • (twoSiteFreeE ET u • twoSiteS0Linear +
    twoSiteFreeS0 ST u • twoSiteELinear) -
    (k.b 0 + k.c 0) • twoSitePC 0

private def twoSiteRowC1 (ET : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  k.a 1 • (twoSiteFreeE ET u • twoSitePS 0 +
    u.1 0 • twoSiteELinear) -
    (k.b 1 + k.c 1) • twoSitePC 1

private def twoSiteRowD0 (FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  k.alpha 0 • (twoSiteFreeF FT u • twoSitePS 0 +
    u.1 0 • twoSiteFLinear) -
    (k.beta 0 + k.gamma 0) • twoSitePD 0

private def twoSiteRowD1 (FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] ℝ :=
  k.alpha 1 • (twoSiteFreeF FT u • twoSitePS 1 +
    u.1 1 • twoSiteFLinear) -
    (k.beta 1 + k.gamma 1) • twoSitePD 1

private def twoSiteJacobianCLM (ET FT ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : CoordinateSpace 2 →L[ℝ] CoordinateSpace 2 :=
  (ContinuousLinearMap.pi ![twoSiteRowS1 ET FT k u,
    twoSiteRowS2 FT k u]).prod
    ((ContinuousLinearMap.pi ![twoSiteRowC0 ET ST k u,
      twoSiteRowC1 ET k u]).prod
      (ContinuousLinearMap.pi ![twoSiteRowD0 FT k u,
        twoSiteRowD1 FT k u]))

private theorem twoSiteD0_hasFDerivAt (FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt
      (fun v : CoordinateSpace 2 =>
        k.alpha 0 * v.1 0 * twoSiteFreeF FT v -
          (k.beta 0 + k.gamma 0) * v.2.2 0)
      (twoSiteRowD0 FT k u) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 2 => v.1 0)
      (twoSitePS 0) u := (twoSitePS 0).hasFDerivAt
  have hd : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.2 0)
      (twoSitePD 0) u := (twoSitePD 0).hasFDerivAt
  convert (((hs.mul (twoSiteFreeF_hasFDerivAt FT u)).const_mul
    (k.alpha 0)).sub (hd.const_mul (k.beta 0 + k.gamma 0))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteRowD0]
    ring

private theorem twoSiteD1_hasFDerivAt (FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt
      (fun v : CoordinateSpace 2 =>
        k.alpha 1 * v.1 1 * twoSiteFreeF FT v -
          (k.beta 1 + k.gamma 1) * v.2.2 1)
      (twoSiteRowD1 FT k u) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 2 => v.1 1)
      (twoSitePS 1) u := (twoSitePS 1).hasFDerivAt
  have hd : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.2 1)
      (twoSitePD 1) u := (twoSitePD 1).hasFDerivAt
  convert (((hs.mul (twoSiteFreeF_hasFDerivAt FT u)).const_mul
    (k.alpha 1)).sub (hd.const_mul (k.beta 1 + k.gamma 1))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteRowD1]
    ring

private theorem twoSiteC0_hasFDerivAt (ET ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt
      (fun v : CoordinateSpace 2 =>
        k.a 0 * twoSiteFreeS0 ST v * twoSiteFreeE ET v -
          (k.b 0 + k.c 0) * v.2.1 0)
      (twoSiteRowC0 ET ST k u) u := by
  have hc : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.1 0)
      (twoSitePC 0) u := (twoSitePC 0).hasFDerivAt
  convert (((twoSiteFreeS0_hasFDerivAt ST u).mul
    (twoSiteFreeE_hasFDerivAt ET u)).const_mul
    (k.a 0)).sub (hc.const_mul (k.b 0 + k.c 0)) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteRowC0]
    ring

private theorem twoSiteC1_hasFDerivAt (ET : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt
      (fun v : CoordinateSpace 2 =>
        k.a 1 * v.1 0 * twoSiteFreeE ET v -
          (k.b 1 + k.c 1) * v.2.1 1)
      (twoSiteRowC1 ET k u) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 2 => v.1 0)
      (twoSitePS 0) u := (twoSitePS 0).hasFDerivAt
  have hc : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.1 1)
      (twoSitePC 1) u := (twoSitePC 1).hasFDerivAt
  convert (((hs.mul (twoSiteFreeE_hasFDerivAt ET u)).const_mul
    (k.a 1)).sub (hc.const_mul (k.b 1 + k.c 1))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteRowC1]
    ring

private theorem twoSiteS2_hasFDerivAt (FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt
      (fun v : CoordinateSpace 2 =>
        k.c 1 * v.2.1 1 - k.alpha 1 * v.1 1 * twoSiteFreeF FT v +
          k.beta 1 * v.2.2 1)
      (twoSiteRowS2 FT k u) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 2 => v.1 1)
      (twoSitePS 1) u := (twoSitePS 1).hasFDerivAt
  have hc : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.1 1)
      (twoSitePC 1) u := (twoSitePC 1).hasFDerivAt
  have hd : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.2 1)
      (twoSitePD 1) u := (twoSitePD 1).hasFDerivAt
  convert (((hc.const_mul (k.c 1)).sub
    ((hs.mul (twoSiteFreeF_hasFDerivAt FT u)).const_mul
      (k.alpha 1))).add (hd.const_mul (k.beta 1))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteRowS2]
    ring

private theorem twoSiteS1_hasFDerivAt (ET FT : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt
      (fun v : CoordinateSpace 2 =>
        k.c 0 * v.2.1 0 - k.alpha 0 * v.1 0 * twoSiteFreeF FT v +
          k.beta 0 * v.2.2 0 - k.a 1 * v.1 0 * twoSiteFreeE ET v +
          k.b 1 * v.2.1 1 + k.gamma 1 * v.2.2 1)
      (twoSiteRowS1 ET FT k u) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 2 => v.1 0)
      (twoSitePS 0) u := (twoSitePS 0).hasFDerivAt
  have hc0 : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.1 0)
      (twoSitePC 0) u := (twoSitePC 0).hasFDerivAt
  have hc1 : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.1 1)
      (twoSitePC 1) u := (twoSitePC 1).hasFDerivAt
  have hd0 : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.2 0)
      (twoSitePD 0) u := (twoSitePD 0).hasFDerivAt
  have hd1 : HasFDerivAt (fun v : CoordinateSpace 2 => v.2.2 1)
      (twoSitePD 1) u := (twoSitePD 1).hasFDerivAt
  convert ((((((hc0.const_mul (k.c 0)).sub
    ((hs.mul (twoSiteFreeF_hasFDerivAt FT u)).const_mul
      (k.alpha 0))).add (hd0.const_mul (k.beta 0))).sub
    ((hs.mul (twoSiteFreeE_hasFDerivAt ET u)).const_mul
      (k.a 1))).add (hc1.const_mul (k.b 1))).add
    (hd1.const_mul (k.gamma 1))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [twoSiteRowS1]
    ring

private theorem twoSiteField_hasFDerivAt (ET FT ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    HasFDerivAt (twoSiteField ET FT ST k)
      (twoSiteJacobianCLM ET FT ST k u) u := by
  have hs : HasFDerivAt
      (fun v : CoordinateSpace 2 => (twoSiteField ET FT ST k v).1)
      (ContinuousLinearMap.pi ![twoSiteRowS1 ET FT k u,
        twoSiteRowS2 FT k u]) u := by
    apply hasFDerivAt_pi'.2
    intro i
    fin_cases i
    · simpa [twoSiteField] using twoSiteS1_hasFDerivAt ET FT k u
    · simpa [twoSiteField] using twoSiteS2_hasFDerivAt FT k u
  have hc : HasFDerivAt
      (fun v : CoordinateSpace 2 => (twoSiteField ET FT ST k v).2.1)
      (ContinuousLinearMap.pi ![twoSiteRowC0 ET ST k u,
        twoSiteRowC1 ET k u]) u := by
    apply hasFDerivAt_pi'.2
    intro i
    fin_cases i
    · simpa [twoSiteField] using twoSiteC0_hasFDerivAt ET ST k u
    · simpa [twoSiteField] using twoSiteC1_hasFDerivAt ET k u
  have hd : HasFDerivAt
      (fun v : CoordinateSpace 2 => (twoSiteField ET FT ST k v).2.2)
      (ContinuousLinearMap.pi ![twoSiteRowD0 FT k u,
        twoSiteRowD1 FT k u]) u := by
    apply hasFDerivAt_pi'.2
    intro i
    fin_cases i
    · simpa [twoSiteField] using twoSiteD0_hasFDerivAt FT k u
    · simpa [twoSiteField] using twoSiteD1_hasFDerivAt FT k u
  simpa [twoSiteJacobianCLM] using hs.prodMk (hc.prodMk hd)

theorem restrictedJacobian_twoSite (ET FT ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    restrictedJacobian ET FT ST k u = twoSiteJacobianCLM ET FT ST k u := by
  have hfield : restrictedFieldEuclid ET FT ST k = twoSiteField ET FT ST k :=
    funext (restrictedFieldEuclid_twoSite ET FT ST k)
  simp only [restrictedJacobian, hfield]
  exact (twoSiteField_hasFDerivAt ET FT ST k u).fderiv

def twoSiteIndexEquiv :
    (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) ≃ Fin 6 :=
  { toFun := fun i => match i with
      | .inl j => if j = 0 then 0 else 1
      | .inr (.inl j) => if j = 0 then 2 else 3
      | .inr (.inr j) => if j = 0 then 4 else 5
    invFun := fun i =>
      if i = 0 then .inl 0 else
      if i = 1 then .inl 1 else
      if i = 2 then .inr (.inl 0) else
      if i = 3 then .inr (.inl 1) else
      if i = 4 then .inr (.inr 0) else .inr (.inr 1)
    left_inv := by
      intro i
      rcases i with j | j
      · fin_cases j <;> simp
      · rcases j with j | j <;> fin_cases j <;> simp
    right_inv := by
      intro i
      fin_cases i <;> simp }

def manuscriptTwoSiteMatrixFin (j : Fin 3) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.reindex twoSiteIndexEquiv twoSiteIndexEquiv
    (restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates
      (toCoordinateSpace (chart (manuscriptTwoSiteStates j))))

private def twoSiteBasisVec : Fin 6 → CoordinateSpace 2 :=
  ![(![1,0], (![0,0], ![0,0])),
    (![0,1], (![0,0], ![0,0])),
    (![0,0], (![1,0], ![0,0])),
    (![0,0], (![0,1], ![0,0])),
    (![0,0], (![0,0], ![1,0])),
    (![0,0], (![0,0], ![0,1]))]

private def twoSiteRead : Fin 6 → CoordinateSpace 2 → ℝ :=
  ![fun v => v.1 0,
    fun v => v.1 1,
    fun v => v.2.1 0,
    fun v => v.2.1 1,
    fun v => v.2.2 0,
    fun v => v.2.2 1]

private theorem twoSiteBasisVec_eq (j : Fin 6) :
    coordinateBasis 2 (twoSiteIndexEquiv.symm j) = twoSiteBasisVec j := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    simp [twoSiteBasisVec, twoSiteIndexEquiv, coordinateBasis]

private theorem twoSiteRead_eq (i : Fin 6) (v : CoordinateSpace 2) :
    (coordinateBasis 2).repr v (twoSiteIndexEquiv.symm i) =
      twoSiteRead i v := by
  fin_cases i <;>
    simp [twoSiteRead, twoSiteIndexEquiv, coordinateBasis]

def twoSiteExplicitJacobian (ET FT ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) : Matrix (Fin 6) (Fin 6) ℝ :=
  let e := twoSiteFreeE ET u
  let f := twoSiteFreeF FT u
  let s0 := twoSiteFreeS0 ST u
  !![-k.alpha 0 * f - k.a 1 * e, 0,
       k.c 0 + k.a 1 * u.1 0, k.b 1 + k.a 1 * u.1 0,
       k.beta 0 + k.alpha 0 * u.1 0,
       k.gamma 1 + k.alpha 0 * u.1 0;
     0, -k.alpha 1 * f, 0, k.c 1,
       k.alpha 1 * u.1 1, k.beta 1 + k.alpha 1 * u.1 1;
     -k.a 0 * e, -k.a 0 * e,
       -k.a 0 * (s0 + e) - k.b 0 - k.c 0,
       -k.a 0 * (s0 + e), -k.a 0 * e, -k.a 0 * e;
     k.a 1 * e, 0, -k.a 1 * u.1 0,
       -k.a 1 * u.1 0 - k.b 1 - k.c 1, 0, 0;
     k.alpha 0 * f, 0, 0, 0,
       -k.alpha 0 * u.1 0 - k.beta 0 - k.gamma 0,
       -k.alpha 0 * u.1 0;
     0, k.alpha 1 * f, 0, 0,
       -k.alpha 1 * u.1 1,
       -k.alpha 1 * u.1 1 - k.beta 1 - k.gamma 1]

theorem twoSiteMatrixFin_eq_explicit (ET FT ST : ℝ) (k : Rates 2)
    (u : CoordinateSpace 2) :
    Matrix.reindex twoSiteIndexEquiv twoSiteIndexEquiv
        (restrictedJacobianMatrix ET FT ST k u) =
      twoSiteExplicitJacobian ET FT ST k u := by
  rw [restrictedJacobianMatrix, restrictedJacobian_twoSite]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply]
  rw [twoSiteRead_eq, twoSiteBasisVec_eq]
  fin_cases i <;> fin_cases j <;>
    simp [twoSiteRead, twoSiteBasisVec,
      twoSiteJacobianCLM, twoSiteRowS1, twoSiteRowS2,
      twoSiteRowC0, twoSiteRowC1, twoSiteRowD0, twoSiteRowD1,
      twoSiteS0Linear, twoSiteELinear, twoSiteFLinear,
      twoSitePS, twoSitePC, twoSitePD,
      twoSiteExplicitJacobian] <;> ring

theorem manuscriptTwoSiteMatrixFin_zero_eq :
    manuscriptTwoSiteMatrixFin 0 = twoSiteA0Real := by
  rw [manuscriptTwoSiteMatrixFin, twoSiteMatrixFin_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteExplicitJacobian,
      twoSiteFreeS0, twoSiteFreeE, twoSiteFreeF,
      manuscriptTwoSiteRates, manuscriptTwoSiteStates,
      twoSiteA0Real, manuscriptTwoSiteA0,
      toCoordinateSpace, chart]

theorem manuscriptTwoSiteMatrixFin_two_eq :
    manuscriptTwoSiteMatrixFin 2 = twoSiteA2Real := by
  rw [manuscriptTwoSiteMatrixFin, twoSiteMatrixFin_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteExplicitJacobian,
      twoSiteFreeS0, twoSiteFreeE, twoSiteFreeF,
      manuscriptTwoSiteRates, manuscriptTwoSiteStates,
      twoSiteA2Real, manuscriptTwoSiteA2,
      toCoordinateSpace, chart]

def twoSiteA1Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteA1.map (fun q : ℚ => (q : ℝ))

theorem manuscriptTwoSiteMatrixFin_one_eq :
    manuscriptTwoSiteMatrixFin 1 = twoSiteA1Real := by
  rw [manuscriptTwoSiteMatrixFin, twoSiteMatrixFin_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteExplicitJacobian,
      twoSiteFreeS0, twoSiteFreeE, twoSiteFreeF,
      manuscriptTwoSiteRates, manuscriptTwoSiteStates,
      twoSiteA1Real, manuscriptTwoSiteA1,
      toCoordinateSpace, chart]

end
end PhosphorylationStableCapacity
