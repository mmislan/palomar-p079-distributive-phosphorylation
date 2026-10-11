module
public import proofs.PhosphorylationStableCapacity.RatioEnzymeResidual

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal state on the one-variable equilibrium profile,
before any conserved totals are imposed. -/
def ratioProfileState {n : ℕ} (k : Rates n)
    (u s f : ℝ) : State n where
  S j := equilibriumWeight k j.val * u^j.val * s
  E := u*f
  F := f
  C i := f*s*kinaseBindingRatio k i *
    equilibriumWeight k i.val * u^(i.val+1)
  D i := f*s*phosphataseBindingRatio k i *
    equilibriumWeight k (i.val+1) * u^(i.val+1)

theorem ratioProfileState_positive {n : ℕ}
    (k : Rates n) (hk : k.Positive)
    (u s f : ℝ) (hu : 0 < u) (hs : 0 < s) (hf : 0 < f) :
    (ratioProfileState k u s f).Positive := by
  refine ⟨?_, mul_pos hu hf, hf, ?_, ?_⟩
  · intro j
    dsimp [ratioProfileState]
    exact mul_pos (mul_pos (equilibriumWeight_pos k hk j.val)
      (pow_pos hu _)) hs
  · intro i
    dsimp [ratioProfileState]
    have hw := equilibriumWeight_pos k hk i.val
    have hp := kinaseBindingRatio_pos k hk i
    positivity
  · intro i
    dsimp [ratioProfileState]
    have hw := equilibriumWeight_pos k hk (i.val+1)
    have hp := phosphataseBindingRatio_pos k hk i
    positivity

private theorem ratioProfile_catalytic_factor {n : ℕ}
    (k : Rates n) (hk : k.Positive) (i : Fin n) :
    k.c i * kinaseBindingRatio k i =
      k.gamma i * phosphataseBindingRatio k i *
        equilibriumRatioFactor k i := by
  have hbc : k.b i + k.c i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
  have hbg : k.beta i + k.gamma i ≠ 0 :=
    ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
  have ha : k.alpha i ≠ 0 := ne_of_gt (hk i).2.2.2.1
  have hg : k.gamma i ≠ 0 := ne_of_gt (hk i).2.2.2.2.2
  dsimp [kinaseBindingRatio, phosphataseBindingRatio,
    equilibriumRatioFactor]
  field_simp [hbc, hbg, ha, hg]

/-- Every positive point on the all-size profile is a literal
mass-action equilibrium; the three totals are free parameters. -/
theorem ratioProfileState_equilibrium {n : ℕ}
    (k : Rates n) (hk : k.Positive)
    (u s f : ℝ) : Equilibrium k (ratioProfileState k u s f) := by
  apply equilibrium_of_currents
  · intro i
    have hbc : k.b i + k.c i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.1 (hk i).2.2.1)
    dsimp [kinaseNet, ratioProfileState, kinaseBindingRatio]
    rw [pow_succ]
    field_simp [hbc]
    ring
  · intro i
    have hbg : k.beta i + k.gamma i ≠ 0 :=
      ne_of_gt (add_pos (hk i).2.2.2.2.1 (hk i).2.2.2.2.2)
    dsimp [phosphataseNet, ratioProfileState,
      phosphataseBindingRatio]
    field_simp [hbg]
    ring
  · intro i
    have hfactor := ratioProfile_catalytic_factor k hk i
    dsimp [ratioProfileState]
    rw [equilibriumWeight_succ]
    calc
      k.c i * (f*s*kinaseBindingRatio k i *
        equilibriumWeight k i.val * u^(i.val+1)) =
          f*s*equilibriumWeight k i.val*u^(i.val+1) *
            (k.c i * kinaseBindingRatio k i) := by ring
      _ = f*s*equilibriumWeight k i.val*u^(i.val+1) *
            (k.gamma i * phosphataseBindingRatio k i *
              equilibriumRatioFactor k i) := by rw [hfactor]
      _ = k.gamma i *
            (f*s*phosphataseBindingRatio k i *
              (equilibriumWeight k i.val *
                equilibriumRatioFactor k i) * u^(i.val+1)) := by ring

end
end PhosphorylationStableCapacity
