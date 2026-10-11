module
public import proofs.PhosphorylationStableCapacity.FastBindingLinearTerm

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At a positive equilibrium, the exact kinase-complex field difference
has the concentration-affinity linear term and a quadratic remainder. -/
theorem loadedFastField_difference_C_affinity {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.1 i -
      (loadedRestrictedField ET FT ST k u).2.1 i =
      -(k.a i * (stateFromLoaded ET FT ST u).S i.castSucc *
          (stateFromLoaded ET FT ST u).E) *
        (v.1 i / (stateFromLoaded ET FT ST u).C i -
          fastDeltaS v i.castSucc /
            (stateFromLoaded ET FT ST u).S i.castSucc -
          fastDeltaE v / (stateFromLoaded ET FT ST u).E) +
        k.a i * fastDeltaS v i.castSucc * fastDeltaE v := by
  let x := stateFromLoaded ET FT ST u
  have hb := equilibrium_kinase_binding_balance k x heq i
  have hS : x.S i.castSucc ≠ 0 := ne_of_gt (hpos.1 _)
  have hE : x.E ≠ 0 := ne_of_gt hpos.2.1
  have hC : x.C i ≠ 0 := ne_of_gt (hpos.2.2.2.1 i)
  calc
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.1 i -
        (loadedRestrictedField ET FT ST k u).2.1 i =
        k.a i * (x.S i.castSucc * fastDeltaE v +
          x.E * fastDeltaS v i.castSucc +
          fastDeltaS v i.castSucc * fastDeltaE v) -
          (k.b i + k.c i) * v.1 i :=
      loadedFastField_difference_C ET FT ST k u v i
    _ = -(k.a i * x.S i.castSucc * x.E) *
          (v.1 i / x.C i - fastDeltaS v i.castSucc / x.S i.castSucc -
            fastDeltaE v / x.E) +
          k.a i * fastDeltaS v i.castSucc * fastDeltaE v :=
      bindingFieldDifference_eq_affinity _ _ _ _ _ _ _ _ hS hE hC hb

/-- The analogous exact phosphatase-complex decomposition. -/
theorem loadedFastField_difference_D_affinity {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.2 i -
      (loadedRestrictedField ET FT ST k u).2.2 i =
      -(k.alpha i * (stateFromLoaded ET FT ST u).S i.succ *
          (stateFromLoaded ET FT ST u).F) *
        (v.2 i / (stateFromLoaded ET FT ST u).D i -
          fastDeltaS v i.succ /
            (stateFromLoaded ET FT ST u).S i.succ -
          fastDeltaF v / (stateFromLoaded ET FT ST u).F) +
        k.alpha i * fastDeltaS v i.succ * fastDeltaF v := by
  let x := stateFromLoaded ET FT ST u
  have hb := equilibrium_phosphatase_binding_balance k x heq i
  have hS : x.S i.succ ≠ 0 := ne_of_gt (hpos.1 _)
  have hF : x.F ≠ 0 := ne_of_gt hpos.2.2.1
  have hD : x.D i ≠ 0 := ne_of_gt (hpos.2.2.2.2 i)
  calc
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.2 i -
        (loadedRestrictedField ET FT ST k u).2.2 i =
        k.alpha i * (x.S i.succ * fastDeltaF v +
          x.F * fastDeltaS v i.succ +
          fastDeltaS v i.succ * fastDeltaF v) -
          (k.beta i + k.gamma i) * v.2 i :=
      loadedFastField_difference_D ET FT ST k u v i
    _ = -(k.alpha i * x.S i.succ * x.F) *
          (v.2 i / x.D i - fastDeltaS v i.succ / x.S i.succ -
            fastDeltaF v / x.F) +
          k.alpha i * fastDeltaS v i.succ * fastDeltaF v :=
      bindingFieldDifference_eq_affinity _ _ _ _ _ _ _ _ hS hF hD hb

/-- The exact equilibrium field difference uses the verified abstract fast
operator as its linear part. -/
theorem loadedFastField_difference_C_fastBinding {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.1 i -
      (loadedRestrictedField ET FT ST k u).2.1 i =
      (fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).1 i +
      k.a i * fastDeltaS v i.castSucc * fastDeltaE v := by
  rw [loadedFastField_difference_C_affinity ET FT ST k u v i hpos heq]
  rw [← fastAffinityC_eq_delta (stateFromLoaded ET FT ST u) v i]
  rfl

theorem loadedFastField_difference_D_fastBinding {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.2 i -
      (loadedRestrictedField ET FT ST k u).2.2 i =
      (fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).2 i +
      k.alpha i * fastDeltaS v i.succ * fastDeltaF v := by
  rw [loadedFastField_difference_D_affinity ET FT ST k u v i hpos heq]
  rw [← fastAffinityD_eq_delta (stateFromLoaded ET FT ST u) v i]
  rfl

end
end PhosphorylationStableCapacity
