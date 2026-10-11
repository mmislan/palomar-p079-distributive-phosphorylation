module
public import proofs.PhosphorylationStableCapacity.OperationalSinkOutcome
public import proofs.PhosphorylationStableCapacity.OperationalPhysicalSpectrum
public import proofs.PhosphorylationStableCapacity.OperationalLiteralPhysicalRecovery
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalNominalBridge
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalAssemblyZero
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalAssemblyTwo
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalAssemblyFour

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The same relative box permits independent changes of all21 rates and totals. -/
def InOperationalParameterBox (θ : Fin 21 → ℝ) : Prop :=
  ∀ i, |θ i-benchmarkThreeSiteOperationalNominal i| ≤
    (1/671088640000 : ℝ)*benchmarkThreeSiteOperationalNominal i

/-- Physical class hyperbolicity belongs to the same shifted witness as the
printed recovery and readout certificate. -/
def operationalPhysicalRestrictedSink (q s : Fin 9 → ℚ)
    (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  IsHurwitz (restrictedJacobianMatrix
    (operationalPhysicalParameters θ 18) (operationalPhysicalParameters θ 19)
    (operationalPhysicalParameters θ 20)
    (operationalParameterRates (operationalPhysicalParameters θ))
    (operationalUnpack (fun i => ((q i / 10 : ℚ) : ℝ)) +
      operationalLift (fun i => ((s i / 10 : ℚ) : ℝ)) e))


def operationalZeroFullOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  OperationalNominalLyapunovData operationalZeroIntervalCoordinates operationalZeroIntervalScales
    (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i))
    operationalZeroP.realMatrix operationalZeroQ.realMatrix operationalZeroQInverse.realMatrix
    (operationalZeroDecayMargin : ℝ) (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℝ) ∧
  OperationalSinkOutcome
    (fun i => (operationalZeroIntervalCoordinates i : ℝ))
    (fun i => (operationalZeroIntervalScales i : ℝ)) θ operationalZeroP.realMatrix
    (1/8192000) (1/16384000000) (1/100) (operationalZeroDecayMargin : ℝ)
    (operationalZeroPRowBound : ℝ) (357000) (23797/10000000) (437971/100000000) e

def operationalZeroPrintedOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  OperationalPrintedSinkOutcome operationalZeroIntervalCoordinates operationalZeroIntervalScales
    (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i)) θ operationalZeroP.realMatrix
    (1/8192000) (1/16384000000) (1/100) (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ)
    (357000) (23797/10000000) (437971/100000000) (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℝ) e ∧
  operationalPhysicalRestrictedSink operationalZeroIntervalCoordinates operationalZeroIntervalScales θ e ∧
  OperationalLiteralPhysicalRecovery
    (fun i => (operationalZeroIntervalCoordinates i : ℝ))
    (fun i => (operationalZeroIntervalScales i : ℝ)) θ operationalZeroP.realMatrix
    (1/8192000) (1/16384000000) (1/100) (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ) (357000) e

theorem operationalZero_printed_of_full {θ : Fin 21 → ℝ} {e : Fin 9 → ℝ}
    (h : operationalZeroFullOutcome θ e) : operationalZeroPrintedOutcome θ e := by
  have hp : OperationalPrintedSinkOutcome operationalZeroIntervalCoordinates operationalZeroIntervalScales
      (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i)) θ operationalZeroP.realMatrix
      (1/8192000) (1/16384000000) (1/100) (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ)
      (357000) (23797/10000000) (437971/100000000) (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℝ) e :=
    ⟨operationalZeroQ.realMatrix, operationalZeroQInverse.realMatrix, h.1, h.2⟩
  exact ⟨hp, hp.physical_restricted_hurwitz
    (fun i => (Rat.cast_pos.mpr (operationalZero_scales_positive i)).ne'),
    h.2.literal_physical_recovery
      (fun i => (Rat.cast_pos.mpr (operationalZero_scales_positive i)).ne')⟩

theorem operationalZero_full_outcome (θ : Fin 21 → ℝ) (hθ : InOperationalParameterBox θ) :
    ∃ e : Fin 9 → ℝ, operationalZeroFullOutcome θ e := by
  have hbox : ∀ i : Fin 21,
      |θ i-(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ) := by
    simpa only [InOperationalParameterBox, benchmarkThreeSiteOperationalNominal_zero] using hθ
  obtain ⟨e, hshift, _hpositive, hequilibrium, hunique⟩ :=
    operationalZero_positive_equilibrium_persistence θ hbox
  have hs : ∀ i, (operationalZeroIntervalScales i : ℝ) ≠ 0 :=
    fun i => (Rat.cast_pos.mpr (operationalZero_scales_positive i)).ne'
  have heq : operationalWeightedField
      (fun i => (operationalZeroIntervalCoordinates i : ℝ))
      (fun i => (operationalZeroIntervalScales i : ℝ)) θ e = 0 :=
    (operationalWeightedField_zero_iff_equilibrium _ _ hs θ e).mpr hequilibrium
  have heNorm : ‖e‖ ≤ (1/8192000 : ℝ) := by linarith only [hshift]
  have hspecies : ∀ i, 0 < operationalSpecies
      (fun j => (operationalZeroIntervalCoordinates j : ℝ))
      (fun j => (operationalZeroIntervalScales j : ℝ)) θ e i := by
    apply operational_actual_species_positive operationalZeroIntervalCoordinates
      operationalZeroIntervalScales operationalZeroIntervalDomain operationalZeroInterval_positive_species θ e
    rw [operationalZero_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ e
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact heNorm)
  have hparameters : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i))
    (1/671088640000) θ operationalZero_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
  refine ⟨e, operationalZero_nominal_lyapunov_data, {
    physical_parameters_positive := operationalPhysicalParameters_positive θ hparameters,
    physical_species_positive_in_box := ?_,
    positive_definite := operationalZeroP_posDef,
    rational_matrix := ?_, operator_norm := operationalZero_P_operator_norm_exact,
    lower_constant_positive := by norm_num,
    decay_positive := Rat.cast_pos.mpr operationalZero_decay_margin_positive,
    quadratic_lower := operationalZero_P_printed_lower, quadratic_upper := operationalZero_P_upper,
    actual_uniform_dissipation := ?_, shift := hshift, zero := heq,
    positive := operationalPhysicalState_positive _ _ θ e hspecies,
    physical_equilibrium := operationalPhysicalState_equilibrium _ _ hs θ e heq,
    physical_class := operationalPhysicalState_inClass _ _ θ e,
    unique_in_box := hunique, measured_readout := ?_,
    inner_recovery := ?_, closed_ellipsoid_recovery := ?_ }⟩
  · intro w hw
    apply operationalPhysicalState_positive _ _ θ w
    apply operational_actual_species_positive operationalZeroIntervalCoordinates
      operationalZeroIntervalScales operationalZeroIntervalDomain operationalZeroInterval_positive_species θ w
    rw [operationalZero_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  · intro i j
    refine ⟨operationalZeroP.rationalMatrix i j, ?_⟩
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    rfl
  · intro w hw v
    rw [operationalReactionJacobian_action operationalZeroIntervalCoordinates operationalZeroIntervalScales θ w v]
    exact operationalZero_actual_uniform_dissipation θ hbox w hw v
  · intro measurement hm
    exact operationalZero_measured_readout_interval θ e measurement hshift hm
  · intro initial hinit
    exact operationalZero_physical_forward_recovery θ hbox e initial hshift heq hinit
  · intro initial hinit
    exact operationalZero_physical_closed_ellipsoid θ hbox e initial hshift heq hinit


def operationalTwoFullOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  OperationalNominalLyapunovData operationalTwoIntervalCoordinates operationalTwoIntervalScales
    (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i))
    operationalTwoP.realMatrix operationalTwoQ.realMatrix operationalTwoQInverse.realMatrix
    (operationalTwoDecayMargin : ℝ) (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℝ) ∧
  OperationalSinkOutcome
    (fun i => (operationalTwoIntervalCoordinates i : ℝ))
    (fun i => (operationalTwoIntervalScales i : ℝ)) θ operationalTwoP.realMatrix
    (1/16384000) (1/327680000000) (1/100) (operationalTwoDecayMargin : ℝ)
    (operationalTwoPRowBound : ℝ) (32918000) (1439001/20000000) (3697503/50000000) e

def operationalTwoPrintedOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  OperationalPrintedSinkOutcome operationalTwoIntervalCoordinates operationalTwoIntervalScales
    (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i)) θ operationalTwoP.realMatrix
    (1/16384000) (1/327680000000) (1/100) (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ)
    (32918000) (1439001/20000000) (3697503/50000000) (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℝ) e ∧
  operationalPhysicalRestrictedSink operationalTwoIntervalCoordinates operationalTwoIntervalScales θ e ∧
  OperationalLiteralPhysicalRecovery
    (fun i => (operationalTwoIntervalCoordinates i : ℝ))
    (fun i => (operationalTwoIntervalScales i : ℝ)) θ operationalTwoP.realMatrix
    (1/16384000) (1/327680000000) (1/100) (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ) (32918000) e

theorem operationalTwo_printed_of_full {θ : Fin 21 → ℝ} {e : Fin 9 → ℝ}
    (h : operationalTwoFullOutcome θ e) : operationalTwoPrintedOutcome θ e := by
  have hp : OperationalPrintedSinkOutcome operationalTwoIntervalCoordinates operationalTwoIntervalScales
      (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i)) θ operationalTwoP.realMatrix
      (1/16384000) (1/327680000000) (1/100) (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ)
      (32918000) (1439001/20000000) (3697503/50000000) (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℝ) e :=
    ⟨operationalTwoQ.realMatrix, operationalTwoQInverse.realMatrix, h.1, h.2⟩
  exact ⟨hp, hp.physical_restricted_hurwitz
    (fun i => (Rat.cast_pos.mpr (operationalTwo_scales_positive i)).ne'),
    h.2.literal_physical_recovery
      (fun i => (Rat.cast_pos.mpr (operationalTwo_scales_positive i)).ne')⟩

theorem operationalTwo_full_outcome (θ : Fin 21 → ℝ) (hθ : InOperationalParameterBox θ) :
    ∃ e : Fin 9 → ℝ, operationalTwoFullOutcome θ e := by
  have hbox : ∀ i : Fin 21,
      |θ i-(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ) := by
    simpa only [InOperationalParameterBox, benchmarkThreeSiteOperationalNominal_two] using hθ
  obtain ⟨e, hshift, _hpositive, hequilibrium, hunique⟩ :=
    operationalTwo_positive_equilibrium_persistence θ hbox
  have hs : ∀ i, (operationalTwoIntervalScales i : ℝ) ≠ 0 :=
    fun i => (Rat.cast_pos.mpr (operationalTwo_scales_positive i)).ne'
  have heq : operationalWeightedField
      (fun i => (operationalTwoIntervalCoordinates i : ℝ))
      (fun i => (operationalTwoIntervalScales i : ℝ)) θ e = 0 :=
    (operationalWeightedField_zero_iff_equilibrium _ _ hs θ e).mpr hequilibrium
  have heNorm : ‖e‖ ≤ (1/16384000 : ℝ) := by linarith only [hshift]
  have hspecies : ∀ i, 0 < operationalSpecies
      (fun j => (operationalTwoIntervalCoordinates j : ℝ))
      (fun j => (operationalTwoIntervalScales j : ℝ)) θ e i := by
    apply operational_actual_species_positive operationalTwoIntervalCoordinates
      operationalTwoIntervalScales operationalTwoIntervalDomain operationalTwoInterval_positive_species θ e
    rw [operationalTwo_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ e
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact heNorm)
  have hparameters : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i))
    (1/671088640000) θ operationalTwo_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
  refine ⟨e, operationalTwo_nominal_lyapunov_data, {
    physical_parameters_positive := operationalPhysicalParameters_positive θ hparameters,
    physical_species_positive_in_box := ?_,
    positive_definite := operationalTwoP_posDef,
    rational_matrix := ?_, operator_norm := operationalTwo_P_operator_norm_exact,
    lower_constant_positive := by norm_num,
    decay_positive := Rat.cast_pos.mpr operationalTwo_decay_margin_positive,
    quadratic_lower := operationalTwo_P_printed_lower, quadratic_upper := operationalTwo_P_upper,
    actual_uniform_dissipation := ?_, shift := hshift, zero := heq,
    positive := operationalPhysicalState_positive _ _ θ e hspecies,
    physical_equilibrium := operationalPhysicalState_equilibrium _ _ hs θ e heq,
    physical_class := operationalPhysicalState_inClass _ _ θ e,
    unique_in_box := hunique, measured_readout := ?_,
    inner_recovery := ?_, closed_ellipsoid_recovery := ?_ }⟩
  · intro w hw
    apply operationalPhysicalState_positive _ _ θ w
    apply operational_actual_species_positive operationalTwoIntervalCoordinates
      operationalTwoIntervalScales operationalTwoIntervalDomain operationalTwoInterval_positive_species θ w
    rw [operationalTwo_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  · intro i j
    refine ⟨operationalTwoP.rationalMatrix i j, ?_⟩
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    rfl
  · intro w hw v
    rw [operationalReactionJacobian_action operationalTwoIntervalCoordinates operationalTwoIntervalScales θ w v]
    exact operationalTwo_actual_uniform_dissipation θ hbox w hw v
  · intro measurement hm
    exact operationalTwo_measured_readout_interval θ e measurement hshift hm
  · intro initial hinit
    exact operationalTwo_physical_forward_recovery θ hbox e initial hshift heq hinit
  · intro initial hinit
    exact operationalTwo_physical_closed_ellipsoid θ hbox e initial hshift heq hinit


def operationalFourFullOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  OperationalNominalLyapunovData operationalFourIntervalCoordinates operationalFourIntervalScales
    (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i))
    operationalFourP.realMatrix operationalFourQ.realMatrix operationalFourQInverse.realMatrix
    (operationalFourDecayMargin : ℝ) (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℝ) ∧
  OperationalSinkOutcome
    (fun i => (operationalFourIntervalCoordinates i : ℝ))
    (fun i => (operationalFourIntervalScales i : ℝ)) θ operationalFourP.realMatrix
    (1/2048000) (1/40960000000) (1/100) (operationalFourDecayMargin : ℝ)
    (operationalFourPRowBound : ℝ) (23433000) (10757833/50000000) (2714459/12500000) e

def operationalFourPrintedOutcome (θ : Fin 21 → ℝ) (e : Fin 9 → ℝ) : Prop :=
  OperationalPrintedSinkOutcome operationalFourIntervalCoordinates operationalFourIntervalScales
    (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i)) θ operationalFourP.realMatrix
    (1/2048000) (1/40960000000) (1/100) (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ)
    (23433000) (10757833/50000000) (2714459/12500000) (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℝ) e ∧
  operationalPhysicalRestrictedSink operationalFourIntervalCoordinates operationalFourIntervalScales θ e ∧
  OperationalLiteralPhysicalRecovery
    (fun i => (operationalFourIntervalCoordinates i : ℝ))
    (fun i => (operationalFourIntervalScales i : ℝ)) θ operationalFourP.realMatrix
    (1/2048000) (1/40960000000) (1/100) (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ) (23433000) e

theorem operationalFour_printed_of_full {θ : Fin 21 → ℝ} {e : Fin 9 → ℝ}
    (h : operationalFourFullOutcome θ e) : operationalFourPrintedOutcome θ e := by
  have hp : OperationalPrintedSinkOutcome operationalFourIntervalCoordinates operationalFourIntervalScales
      (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i)) θ operationalFourP.realMatrix
      (1/2048000) (1/40960000000) (1/100) (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ)
      (23433000) (10757833/50000000) (2714459/12500000) (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℝ) e :=
    ⟨operationalFourQ.realMatrix, operationalFourQInverse.realMatrix, h.1, h.2⟩
  exact ⟨hp, hp.physical_restricted_hurwitz
    (fun i => (Rat.cast_pos.mpr (operationalFour_scales_positive i)).ne'),
    h.2.literal_physical_recovery
      (fun i => (Rat.cast_pos.mpr (operationalFour_scales_positive i)).ne')⟩

theorem operationalFour_full_outcome (θ : Fin 21 → ℝ) (hθ : InOperationalParameterBox θ) :
    ∃ e : Fin 9 → ℝ, operationalFourFullOutcome θ e := by
  have hbox : ∀ i : Fin 21,
      |θ i-(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ) := by
    simpa only [InOperationalParameterBox, benchmarkThreeSiteOperationalNominal_four] using hθ
  obtain ⟨e, hshift, _hpositive, hequilibrium, hunique⟩ :=
    operationalFour_positive_equilibrium_persistence θ hbox
  have hs : ∀ i, (operationalFourIntervalScales i : ℝ) ≠ 0 :=
    fun i => (Rat.cast_pos.mpr (operationalFour_scales_positive i)).ne'
  have heq : operationalWeightedField
      (fun i => (operationalFourIntervalCoordinates i : ℝ))
      (fun i => (operationalFourIntervalScales i : ℝ)) θ e = 0 :=
    (operationalWeightedField_zero_iff_equilibrium _ _ hs θ e).mpr hequilibrium
  have heNorm : ‖e‖ ≤ (1/2048000 : ℝ) := by linarith only [hshift]
  have hspecies : ∀ i, 0 < operationalSpecies
      (fun j => (operationalFourIntervalCoordinates j : ℝ))
      (fun j => (operationalFourIntervalScales j : ℝ)) θ e i := by
    apply operational_actual_species_positive operationalFourIntervalCoordinates
      operationalFourIntervalScales operationalFourIntervalDomain operationalFourInterval_positive_species θ e
    rw [operationalFour_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ e
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact heNorm)
  have hparameters : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i))
    (1/671088640000) θ operationalFour_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
  refine ⟨e, operationalFour_nominal_lyapunov_data, {
    physical_parameters_positive := operationalPhysicalParameters_positive θ hparameters,
    physical_species_positive_in_box := ?_,
    positive_definite := operationalFourP_posDef,
    rational_matrix := ?_, operator_norm := operationalFour_P_operator_norm_exact,
    lower_constant_positive := by norm_num,
    decay_positive := Rat.cast_pos.mpr operationalFour_decay_margin_positive,
    quadratic_lower := operationalFour_P_printed_lower, quadratic_upper := operationalFour_P_upper,
    actual_uniform_dissipation := ?_, shift := hshift, zero := heq,
    positive := operationalPhysicalState_positive _ _ θ e hspecies,
    physical_equilibrium := operationalPhysicalState_equilibrium _ _ hs θ e heq,
    physical_class := operationalPhysicalState_inClass _ _ θ e,
    unique_in_box := hunique, measured_readout := ?_,
    inner_recovery := ?_, closed_ellipsoid_recovery := ?_ }⟩
  · intro w hw
    apply operationalPhysicalState_positive _ _ θ w
    apply operational_actual_species_positive operationalFourIntervalCoordinates
      operationalFourIntervalScales operationalFourIntervalDomain operationalFourInterval_positive_species θ w
    rw [operationalFour_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hbox)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  · intro i j
    refine ⟨operationalFourP.rationalMatrix i j, ?_⟩
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    rfl
  · intro w hw v
    rw [operationalReactionJacobian_action operationalFourIntervalCoordinates operationalFourIntervalScales θ w v]
    exact operationalFour_actual_uniform_dissipation θ hbox w hw v
  · intro measurement hm
    exact operationalFour_measured_readout_interval θ e measurement hshift hm
  · intro initial hinit
    exact operationalFour_physical_forward_recovery θ hbox e initial hshift heq hinit
  · intro initial hinit
    exact operationalFour_physical_closed_ellipsoid θ hbox e initial hshift heq hinit


/-- All three complete operational certificates hold simultaneously for one
common independently perturbed physical system. The physical equilibria are
pairwise distinct, as certified by the disjoint printed readout intervals. -/
theorem three_site_simultaneous_operational_certificates
    (θ : Fin 21 → ℝ) (hθ : InOperationalParameterBox θ) :
    ∃ e0 e2 e4 : Fin 9 → ℝ,
      operationalZeroFullOutcome θ e0 ∧ operationalTwoFullOutcome θ e2 ∧
      operationalFourFullOutcome θ e4 ∧
      operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠
      operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ∧
      operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ≠
      operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧
      operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠
      operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 := by
  obtain ⟨e0, h0⟩ := operationalZero_full_outcome θ hθ
  obtain ⟨e2, h2⟩ := operationalTwo_full_outcome θ hθ
  obtain ⟨e4, h4⟩ := operationalFour_full_outcome θ hθ
  refine ⟨e0, e2, e4, h0, h2, h4, ?_, ?_, ?_⟩
  · exact OperationalSinkOutcome.physical_state_ne h0.2 h2.2 (by norm_num)
  · exact OperationalSinkOutcome.physical_state_ne h2.2 h4.2 (by norm_num)
  · exact OperationalSinkOutcome.physical_state_ne h0.2 h4.2 (by norm_num)

/-- The invertible unit conversion also gives the certificate directly for
every21-coordinate physical parameter vector in the printed relative box. -/
theorem three_site_operational_certificates_for_physical_parameters
    (φ : Fin 21 → ℝ)
    (hφ : ∀ i, |φ i-operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i| ≤
      (1/671088640000 : ℝ)*operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i) :
    ∃ θ : Fin 21 → ℝ, operationalPhysicalParameters θ = φ ∧
      InOperationalParameterBox θ ∧
      ∃ e0 e2 e4 : Fin 9 → ℝ,
        operationalZeroFullOutcome θ e0 ∧ operationalTwoFullOutcome θ e2 ∧
        operationalFourFullOutcome θ e4 := by
  let θ := operationalModelParameters φ
  have hconvert : operationalPhysicalParameters θ = φ :=
    operationalPhysicalParameters_model φ
  have hbox : InOperationalParameterBox θ := by
    apply (operational_physical_relative_box_iff
      benchmarkThreeSiteOperationalNominal θ (1/671088640000)).mp
    simpa only [hconvert] using hφ
  obtain ⟨e0, e2, e4, h0, h2, h4, _h02, _h24, _h04⟩ :=
    three_site_simultaneous_operational_certificates θ hbox
  exact ⟨θ, hconvert, hbox, e0, e2, e4, h0, h2, h4⟩

theorem three_site_printed_operational_submission
    (φ : Fin 21 → ℝ)
    (hφ : ∀ i, |φ i-operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i| ≤
      (1/671088640000 : ℝ)*operationalPhysicalParameters benchmarkThreeSiteOperationalNominal i) :
    ∃ θ : Fin 21 → ℝ, operationalPhysicalParameters θ = φ ∧
      InOperationalParameterBox θ ∧
      ∃ e0 e2 e4 : Fin 9 → ℝ,
        operationalZeroPrintedOutcome θ e0 ∧ operationalTwoPrintedOutcome θ e2 ∧
        operationalFourPrintedOutcome θ e4 ∧
        operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ))
          (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠
        operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ))
          (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ∧
        operationalPhysicalState (fun i => (operationalTwoIntervalCoordinates i : ℝ))
          (fun i => (operationalTwoIntervalScales i : ℝ)) θ e2 ≠
        operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ))
          (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 ∧
        operationalPhysicalState (fun i => (operationalZeroIntervalCoordinates i : ℝ))
          (fun i => (operationalZeroIntervalScales i : ℝ)) θ e0 ≠
        operationalPhysicalState (fun i => (operationalFourIntervalCoordinates i : ℝ))
          (fun i => (operationalFourIntervalScales i : ℝ)) θ e4 := by
  let θ := operationalModelParameters φ
  have hconvert : operationalPhysicalParameters θ = φ := operationalPhysicalParameters_model φ
  have hbox : InOperationalParameterBox θ := by
    apply (operational_physical_relative_box_iff
      benchmarkThreeSiteOperationalNominal θ (1/671088640000)).mp
    simpa only [hconvert] using hφ
  obtain ⟨e0, e2, e4, h0, h2, h4, h02, h24, h04⟩ :=
    three_site_simultaneous_operational_certificates θ hbox
  exact ⟨θ, hconvert, hbox, e0, e2, e4,
    operationalZero_printed_of_full h0, operationalTwo_printed_of_full h2,
    operationalFour_printed_of_full h4, h02, h24, h04⟩

end
end PhosphorylationStableCapacity
