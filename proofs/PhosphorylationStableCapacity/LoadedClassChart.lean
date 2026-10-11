module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import proofs.PhosphorylationStableCapacity.RelaxationFieldBlocks

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Complex substrate bound at a level, expressed in the free class chart. -/
def boundComplexAt {n : ℕ} (C D : Fin n → ℝ) (j : Fin (n + 1)) : ℝ :=
  (∑ i : Fin n, if i.castSucc = j then C i else 0) +
    (∑ i : Fin n, if i.succ = j then D i else 0)

/-- Replace each free substrate by its loaded inventory at that level. -/
def toLoadedCoord {n : ℕ} (u : CoordinateSpace n) : CoordinateSpace n :=
  (fun i => u.1 i + boundComplexAt u.2.1 u.2.2 i.succ, u.2.1, u.2.2)

/-- Recover the free substrate from the loaded inventory and complexes. -/
def fromLoadedCoord {n : ℕ} (u : CoordinateSpace n) : CoordinateSpace n :=
  (fun i => u.1 i - boundComplexAt u.2.1 u.2.2 i.succ, u.2.1, u.2.2)

theorem from_toLoadedCoord {n : ℕ} (u : CoordinateSpace n) :
    fromLoadedCoord (toLoadedCoord u) = u := by
  rcases u with ⟨S, C, D⟩
  simp only [fromLoadedCoord, toLoadedCoord]
  congr 1
  funext i
  ring

theorem to_fromLoadedCoord {n : ℕ} (u : CoordinateSpace n) :
    toLoadedCoord (fromLoadedCoord u) = u := by
  rcases u with ⟨S, C, D⟩
  simp only [fromLoadedCoord, toLoadedCoord]
  congr 1
  funext i
  ring

/-- The first chart component is literally the full-state loaded inventory. -/
theorem toLoadedCoord_eq_loadedLevel {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (i : Fin n) :
    (toLoadedCoord u).1 i =
      loadedLevel (unChart ET FT ST (ofCoordinateSpace u)) i.succ := by
  simp [toLoadedCoord, boundComplexAt, loadedLevel, unChart, ofCoordinateSpace]
  ring

/-- The class field in loaded inventory and complex coordinates. -/
def loadedRestrictedField {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u : CoordinateSpace n) : CoordinateSpace n :=
  toLoadedCoord (restrictedFieldEuclid ET FT ST k (fromLoadedCoord u))

/-- The loaded class field's slow component is the literal loaded velocity. -/
theorem loadedRestrictedField_slow {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k u).1 i =
      loadedLevel
        (field k (unChart ET FT ST (ofCoordinateSpace (fromLoadedCoord u)))) i.succ := by
  simp [loadedRestrictedField, toLoadedCoord, boundComplexAt,
    restrictedFieldEuclid, restrictedField, toCoordinateSpace,
    ofCoordinateSpace, chart, loadedLevel, unChart]
  ring

/-- Relaxation preserves the slow field in the same fixed loaded chart. -/
theorem loadedRestrictedField_relax_slow {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n) (ε : ℝ) :
    (loadedRestrictedField ET FT ST (relaxRates k ε) u).1 i =
      (loadedRestrictedField ET FT ST k u).1 i := by
  rw [loadedRestrictedField_slow, loadedRestrictedField_slow]
  exact relaxRates_loadedLevel_field k _ i.succ ε

/-- Both complex blocks of the loaded class field scale exactly by `ε⁻¹`. -/
theorem loadedRestrictedField_relax_C {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n)
    {ε : ℝ} (hε : ε ≠ 0) :
    (loadedRestrictedField ET FT ST (relaxRates k ε) u).2.1 i =
      (loadedRestrictedField ET FT ST k u).2.1 i / ε := by
  exact relaxRates_field_C k _ i hε

theorem loadedRestrictedField_relax_D {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n)
    {ε : ℝ} (hε : ε ≠ 0) :
    (loadedRestrictedField ET FT ST (relaxRates k ε) u).2.2 i =
      (loadedRestrictedField ET FT ST k u).2.2 i / ε := by
  exact relaxRates_field_D k _ i hε

/-- The slow derivative is unchanged by relaxation in loaded coordinates. -/
theorem loadedSlowFderiv_relax {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (ε : ℝ) :
    fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST (relaxRates k ε) v).1) u =
    fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).1) u := by
  have h : (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST (relaxRates k ε) v).1) =
      (fun v : CoordinateSpace n =>
        (loadedRestrictedField ET FT ST k v).1) := by
    funext v
    funext i
    exact loadedRestrictedField_relax_slow ET FT ST k v i ε
  rw [h]

/-- The kinase-complex derivative scales by the inverse relaxation parameter. -/
theorem loadedCFderiv_relax {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) {ε : ℝ} (hε : ε ≠ 0) :
    fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST (relaxRates k ε) v).2.1) u =
    ε⁻¹ • fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).2.1) u := by
  have h : (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST (relaxRates k ε) v).2.1) =
      (fun v : CoordinateSpace n =>
        ε⁻¹ • (loadedRestrictedField ET FT ST k v).2.1) := by
    funext v
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [loadedRestrictedField_relax_C ET FT ST k v i hε]
    ring
  rw [h]
  change fderiv ℝ
      (ε⁻¹ • (fun v : CoordinateSpace n =>
        (loadedRestrictedField ET FT ST k v).2.1)) u = _
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).2.1) (ε⁻¹)) u

/-- The phosphatase-complex derivative has the same exact scaling. -/
theorem loadedDFderiv_relax {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) {ε : ℝ} (hε : ε ≠ 0) :
    fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST (relaxRates k ε) v).2.2) u =
    ε⁻¹ • fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).2.2) u := by
  have h : (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST (relaxRates k ε) v).2.2) =
      (fun v : CoordinateSpace n =>
        ε⁻¹ • (loadedRestrictedField ET FT ST k v).2.2) := by
    funext v
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [loadedRestrictedField_relax_D ET FT ST k v i hε]
    ring
  rw [h]
  change fderiv ℝ
      (ε⁻¹ • (fun v : CoordinateSpace n =>
        (loadedRestrictedField ET FT ST k v).2.2)) u = _
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).2.2) (ε⁻¹)) u

end
end PhosphorylationStableCapacity
