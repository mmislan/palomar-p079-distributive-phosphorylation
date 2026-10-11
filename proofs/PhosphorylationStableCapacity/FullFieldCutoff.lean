module
public import proofs.PhosphorylationStableCapacity.BoundedLipschitzGlobalCurve
public import proofs.PhosphorylationStableCapacity.FullDerivative
public import proofs.PhosphorylationStableCapacity.ClassBoundaryInward

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open scoped NNReal

noncomputable section

/-- One real concentration clamped to the nonnegative box. -/
def clampSpecies (B : ℝ) (x : ℝ) : ℝ :=
  max 0 (min B x)

theorem clampSpecies_lipschitz (B : ℝ) :
    LipschitzWith 1 (clampSpecies B) :=
  ((LipschitzWith.id (α := ℝ)).const_min B).const_max 0

theorem clampSpecies_abs_le (B : ℝ) (hB : 0 ≤ B) (x : ℝ) :
    |clampSpecies B x| ≤ B := by
  rw [abs_le]
  exact ⟨(neg_nonpos.mpr hB).trans (le_max_left _ _),
    max_le hB (min_le_left B x)⟩

theorem clampSpecies_nonneg (B x : ℝ) :
    0 ≤ clampSpecies B x := le_max_left _ _

theorem clampSpecies_eq_zero_of_neg (B x : ℝ)
    (hB : 0 ≤ B) (hx : x < 0) :
    clampSpecies B x = 0 := by
  rw [clampSpecies, min_eq_right (by linarith : x ≤ B),
    max_eq_left hx.le]

theorem clampSpecies_eq_of_bounds (B x : ℝ)
    (hx0 : 0 ≤ x) (hxB : x ≤ B) :
    clampSpecies B x = x := by
  rw [clampSpecies, min_eq_right hxB,
    max_eq_right hx0]

def clampSpeciesBlock {ι : Type*} [Fintype ι]
    (B : ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => clampSpecies B (x i)

theorem clampSpeciesBlock_lipschitz {ι : Type*} [Fintype ι]
    (B : ℝ) :
    LipschitzWith 1 (clampSpeciesBlock (ι := ι) B) := by
  have hcl := clampSpecies_lipschitz B
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
  intro i
  refine (hcl.dist_le_mul (x i) (y i)).trans ?_
  rw [NNReal.coe_one, one_mul]
  exact dist_le_pi_dist x y i

theorem clampSpeciesBlock_norm_le {ι : Type*} [Fintype ι]
    (B : ℝ) (hB : 0 ≤ B) (x : ι → ℝ) :
    ‖clampSpeciesBlock B x‖ ≤ B := by
  apply (pi_norm_le_iff_of_nonneg hB).2
  intro i
  simpa [Real.norm_eq_abs, clampSpeciesBlock] using
    clampSpecies_abs_le B hB (x i)

theorem clampSpeciesBlock_eq_of_norm_le {ι : Type*} [Fintype ι]
    (B : ℝ) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx : ‖x‖ ≤ B) :
    clampSpeciesBlock B x = x := by
  funext i
  exact clampSpecies_eq_of_bounds B (x i) (hx0 i)
    (le_abs_self _ |>.trans ((norm_le_pi_norm x i).trans hx))

/-- Species-wise clamp of all `3n+3` physical concentrations. -/
def clampFullSpace {n : ℕ} (B : ℝ)
    (x : FullSpace n) : FullSpace n :=
  (clampSpeciesBlock B x.1,
    (clampSpecies B x.2.1.1, clampSpecies B x.2.1.2),
    (clampSpeciesBlock B x.2.2.1,
      clampSpeciesBlock B x.2.2.2))

theorem clampFullSpace_nonnegative {n : ℕ} (B : ℝ)
    (x : FullSpace n) :
    NonnegativeState (ofFullSpace (clampFullSpace B x)) := by
  refine ⟨fun i => clampSpecies_nonneg B (x.1 i),
    clampSpecies_nonneg B x.2.1.1,
    clampSpecies_nonneg B x.2.1.2,
    fun i => clampSpecies_nonneg B (x.2.2.1 i),
    fun i => clampSpecies_nonneg B (x.2.2.2 i)⟩

theorem clampFullSpace_lipschitz {n : ℕ} (B : ℝ) :
    LipschitzWith 1 (clampFullSpace (n := n) B) := by
  change LipschitzWith 1 (fun x : FullSpace n =>
    (clampSpeciesBlock B x.1,
      (clampSpecies B x.2.1.1, clampSpecies B x.2.1.2),
      (clampSpeciesBlock B x.2.2.1, clampSpeciesBlock B x.2.2.2)))
  have hs : LipschitzWith 1
      (fun x : FullSpace n => clampSpeciesBlock B x.1) := by
    simpa only [one_mul, Function.comp_def] using
      (clampSpeciesBlock_lipschitz (ι := Fin (n+1)) B).comp (LipschitzWith.prod_fst
        (α := Fin (n+1) → ℝ)
        (β := (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))))
  have he : LipschitzWith 1
      (fun x : FullSpace n => clampSpecies B x.2.1.1) := by
    simpa only [one_mul, Function.comp_def] using
      (clampSpecies_lipschitz B).comp
        ((LipschitzWith.prod_fst (α := ℝ) (β := ℝ)).comp
          ((LipschitzWith.prod_fst (α := ℝ × ℝ)
            (β := (Fin n → ℝ) × (Fin n → ℝ))).comp
              (LipschitzWith.prod_snd
                (α := Fin (n+1) → ℝ)
                (β := (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))))))
  have hf : LipschitzWith 1
      (fun x : FullSpace n => clampSpecies B x.2.1.2) := by
    simpa only [one_mul, Function.comp_def] using
      (clampSpecies_lipschitz B).comp
        ((LipschitzWith.prod_snd (α := ℝ) (β := ℝ)).comp
          ((LipschitzWith.prod_fst (α := ℝ × ℝ)
            (β := (Fin n → ℝ) × (Fin n → ℝ))).comp
              (LipschitzWith.prod_snd
                (α := Fin (n+1) → ℝ)
                (β := (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))))))
  have hc : LipschitzWith 1
      (fun x : FullSpace n => clampSpeciesBlock B x.2.2.1) := by
    simpa only [one_mul, Function.comp_def] using
      (clampSpeciesBlock_lipschitz (ι := Fin n) B).comp
        ((LipschitzWith.prod_fst (α := Fin n → ℝ)
          (β := Fin n → ℝ)).comp
          ((LipschitzWith.prod_snd (α := ℝ × ℝ)
            (β := (Fin n → ℝ) × (Fin n → ℝ))).comp
              (LipschitzWith.prod_snd
                (α := Fin (n+1) → ℝ)
                (β := (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))))))
  have hd : LipschitzWith 1
      (fun x : FullSpace n => clampSpeciesBlock B x.2.2.2) := by
    simpa only [one_mul, Function.comp_def] using
      (clampSpeciesBlock_lipschitz (ι := Fin n) B).comp
        ((LipschitzWith.prod_snd (α := Fin n → ℝ)
          (β := Fin n → ℝ)).comp
          ((LipschitzWith.prod_snd (α := ℝ × ℝ)
            (β := (Fin n → ℝ) × (Fin n → ℝ))).comp
              (LipschitzWith.prod_snd
                (α := Fin (n+1) → ℝ)
                (β := (ℝ × ℝ) × ((Fin n → ℝ) × (Fin n → ℝ))))))
  simpa only [max_self] using
    hs.prodMk ((he.prodMk hf).prodMk (hc.prodMk hd))

theorem clampFullSpace_norm_le {n : ℕ} (B : ℝ)
    (hB : 0 ≤ B) (x : FullSpace n) :
    ‖clampFullSpace B x‖ ≤ B := by
  change ‖(clampSpeciesBlock B x.1,
    (clampSpecies B x.2.1.1, clampSpecies B x.2.1.2),
    (clampSpeciesBlock B x.2.2.1, clampSpeciesBlock B x.2.2.2))‖ ≤ B
  rw [norm_prod_le_iff]
  refine ⟨clampSpeciesBlock_norm_le B hB x.1, ?_⟩
  rw [norm_prod_le_iff]
  constructor
  · rw [norm_prod_le_iff]
    exact ⟨by simpa [Real.norm_eq_abs] using
        clampSpecies_abs_le B hB x.2.1.1,
      by simpa [Real.norm_eq_abs] using
        clampSpecies_abs_le B hB x.2.1.2⟩
  · rw [norm_prod_le_iff]
    exact ⟨clampSpeciesBlock_norm_le B hB x.2.2.1,
      clampSpeciesBlock_norm_le B hB x.2.2.2⟩

theorem clampFullSpace_eq_of_norm_le {n : ℕ} (B : ℝ)
    (x : FullSpace n)
    (hx0 : NonnegativeState (ofFullSpace x))
    (hx : ‖x‖ ≤ B) :
    clampFullSpace B x = x := by
  have hS : ‖x.1‖ ≤ B := (norm_fst_le x).trans hx
  have hEF : ‖x.2.1‖ ≤ B :=
    (norm_fst_le x.2).trans ((norm_snd_le x).trans hx)
  have hCD : ‖x.2.2‖ ≤ B :=
    (norm_snd_le x.2).trans ((norm_snd_le x).trans hx)
  have hE : |x.2.1.1| ≤ B :=
    (norm_fst_le x.2.1).trans hEF
  have hF : |x.2.1.2| ≤ B :=
    (norm_snd_le x.2.1).trans hEF
  simp only [clampFullSpace,
    clampSpeciesBlock_eq_of_norm_le B x.1 hx0.1 hS,
    clampSpecies_eq_of_bounds B x.2.1.1 hx0.2.1
      (le_abs_self _ |>.trans hE),
    clampSpecies_eq_of_bounds B x.2.1.2 hx0.2.2.1
      (le_abs_self _ |>.trans hF),
    clampSpeciesBlock_eq_of_norm_le B x.2.2.1 hx0.2.2.2.1
      ((norm_fst_le x.2.2).trans hCD),
    clampSpeciesBlock_eq_of_norm_le B x.2.2.2 hx0.2.2.2.2
      ((norm_snd_le x.2.2).trans hCD)]

@[fun_prop] private theorem contDiff_ite_fixed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : Prop) [Decidable p] {f g : E → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun x => if p then f x else g x) := by
  by_cases hp : p <;> simp [hp, hf, hg]

theorem contDiff_fullFieldEuclid {n : ℕ} (k : Rates n) :
    ContDiff ℝ 1 (fullFieldEuclid k) := by
  classical
  unfold fullFieldEuclid toFullSpace ofFullSpace field
    kinaseNet phosphataseNet
  dsimp
  fun_prop

/-- Species-wise clamping gives a bounded globally Lipschitz field
that equals the literal full mass-action field inside the box. -/
theorem fullFieldEuclid_cutoff_bounds {n : ℕ}
    (k : Rates n) (B : ℝ) (hB : 0 ≤ B) :
    ∃ (K M : ℝ≥0),
      LipschitzWith K
        (fun x : FullSpace n =>
          fullFieldEuclid k (clampFullSpace B x)) ∧
      (∀ x : FullSpace n,
        ‖fullFieldEuclid k (clampFullSpace B x)‖ ≤ M) := by
  let f := fullFieldEuclid k
  have hmap : ∀ x : FullSpace n,
      clampFullSpace B x ∈ Metric.closedBall (0 : FullSpace n) B := by
    intro x
    simpa [Metric.mem_closedBall, dist_zero_right] using
      clampFullSpace_norm_le B hB x
  obtain ⟨K, hK⟩ :=
    (contDiff_fullFieldEuclid k).contDiffOn.exists_lipschitzOnWith
      (by norm_num) (convex_closedBall 0 B)
      (isCompact_closedBall 0 B)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : FullSpace n) B).exists_bound_of_continuousOn
      (contDiff_fullFieldEuclid k).continuous.continuousOn
  refine ⟨K, Real.toNNReal C, ?_, ?_⟩
  · intro x y
    calc
      edist (f (clampFullSpace B x)) (f (clampFullSpace B y))
          ≤ K * edist (clampFullSpace B x) (clampFullSpace B y) :=
            hK (hmap x) (hmap y)
      _ ≤ K * edist x y := by
        gcongr
        have h := clampFullSpace_lipschitz (n := n) B x y
        rwa [ENNReal.coe_one, one_mul] at h
  · intro x
    calc
      ‖f (clampFullSpace B x)‖ ≤ C := hC _ (hmap x)
      _ ≤ (Real.toNNReal C : ℝ) := by
        rw [Real.coe_toNNReal']
        exact le_max_left _ _

/-- A global curve for the species-wise cutoff of the full literal
mass-action field, at an arbitrary initial species vector. -/
theorem fullFieldEuclid_cutoff_global_curve {n : ℕ}
    (k : Rates n) (B : ℝ) (hB : 0 ≤ B)
    (x₀ : FullSpace n) :
    ∃ γ : ℝ → FullSpace n,
      γ 0 = x₀ ∧
      ∀ t : ℝ,
        HasDerivAt γ
          (fullFieldEuclid k (clampFullSpace B (γ t))) t := by
  obtain ⟨K, M, hLip, hBound⟩ :=
    fullFieldEuclid_cutoff_bounds k B hB
  exact BoundedODE.exists_isIntegralCurve hLip hBound x₀

end
end PhosphorylationStableCapacity
