module
/-
Copyright (c) 2026 Michael Mislan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This module is compiled in the separately authorized Lean 4.35 degree
environment. It is not part of the frozen Lean 4.30 project.
-/

public import proofs.PhosphorylationStableCapacity.ClosedBallAmbientDegree435
public import proofs.PhosphorylationStableCapacity.ClosedBallCoordinateChart435

@[expose] public section

set_option autoImplicit false

namespace PhosphorylationStableCapacity.Topology435

noncomputable section

open Set Metric

/-- The exact three-field degree interface needed by P079, stated in
the isolated 4.35 environment without importing the 4.30 model chain. -/
structure CoordinateClosedBallDegree435 (n : ℕ)
    (a : CoordinateSpace435 n) (r : ℝ) where
  degree : (closedBall a r → CoordinateSpace435 n) → ℤ
  homotopy_invariant :
    ∀ (H : ℝ → closedBall a r → CoordinateSpace435 n),
      ContinuousOn (fun p : ℝ × closedBall a r => H p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ univ) →
      (∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        ∀ y : closedBall a r, dist y.val a = r → H t y ≠ 0) →
      degree (H 0) = degree (H 1)
  center_normalization :
    degree (fun y : closedBall a r => y.val - a) = 1
  regular_zero_sum :
    ∀ (g : CoordinateSpace435 n → CoordinateSpace435 n)
      (_hg : Differentiable ℝ g)
      (Z : Finset (closedBall a r)),
      (∀ y : closedBall a r, g y.val = 0 ↔ y ∈ Z) →
      (∀ y : closedBall a r, dist y.val a = r → g y.val ≠ 0) →
      (∀ y ∈ Z,
        LinearMap.det (fderiv ℝ g y.val).toLinearMap ≠ 0) →
      degree (fun y : closedBall a r => g y.val) =
        ∑ y ∈ Z,
          if 0 < LinearMap.det (fderiv ℝ g y.val).toLinearMap
          then (1 : ℤ) else -1

/-- Positive-site P079 coordinate balls satisfy the exact degree
interface by radial extension to a Euclidean enclosing ball. -/
theorem coordinateClosedBallDegree435_exists
    (n : ℕ) (hn : 0 < n)
    (a : CoordinateSpace435 n) (r : ℝ) (hr : 0 < r) :
    Nonempty (CoordinateClosedBallDegree435 n a r) := by
  obtain ⟨d, A, R, hR, hcover⟩ :=
    exists_coordinate_enclosure n hn a r hr
  refine ⟨{
    degree := totalAmbientDegree hr hR A hcover
    homotopy_invariant := ?_
    center_normalization := ?_
    regular_zero_sum := ?_ }⟩
  · intro H hcont hb
    exact totalAmbientDegree_homotopy_Icc hr hR A hcover H hcont hb
  · exact totalAmbientDegree_center hr hR A hcover
  · intro g hg Z hZ hb hdet
    exact totalAmbientDegree_regular_zero_sum hr hR A hcover
      g hg Z hZ hb hdet

def coordinateClosedBallDegree435_zero
    (a : CoordinateSpace435 0) (r : ℝ) (hr : 0 < r) :
    CoordinateClosedBallDegree435 0 a r := by
  classical
  letI : Subsingleton (CoordinateSpace435 0) := inferInstance
  let y₀ : closedBall a r := ⟨a, mem_closedBall_self hr.le⟩
  refine {
    degree := fun _ => 1
    homotopy_invariant := by intros; rfl
    center_normalization := rfl
    regular_zero_sum := ?_ }
  intro g _ Z hZ _ _
  have hzero : g y₀.val = 0 := Subsingleton.elim _ _
  have hy₀ : y₀ ∈ Z := (hZ y₀).mp hzero
  have hZeq : Z = {y₀} := by
    ext y
    have heq : y = y₀ := Subtype.ext (Subsingleton.elim _ _)
    simpa [heq] using hy₀
  rw [hZeq]
  simp [LinearMap.det_eq_one_of_subsingleton]

/-- The isolated 4.35 construction covers the exact all-size
coordinate-ball degree interface, including the singleton case. -/
theorem coordinateClosedBallDegree435_all_exists
    (n : ℕ) (a : CoordinateSpace435 n) (r : ℝ) (hr : 0 < r) :
    Nonempty (CoordinateClosedBallDegree435 n a r) := by
  cases n with
  | zero => exact ⟨coordinateClosedBallDegree435_zero a r hr⟩
  | succ n =>
      exact coordinateClosedBallDegree435_exists (n + 1) (Nat.succ_pos n) a r hr

end

end PhosphorylationStableCapacity.Topology435
