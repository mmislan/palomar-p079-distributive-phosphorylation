module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalPositivityTwo
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixRowBound
public import proofs.PhosphorylationStableCapacity.SymmetricMatrixRowQuadraticBounds

@[expose] public section
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators
def operationalTwoPRowBound : ℚ := (267554942803/500000 : ℚ)
theorem operationalTwoP_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalTwoP.entries i j|) * (500000 : ℤ) ≤
      (267554942803 : ℤ) * (operationalTwoP.denominator : ℤ) := by
  decide +kernel
theorem operationalTwoP_absolute_rows (i : Fin 9) :
    (∑ j, |operationalTwoP.realMatrix i j|) ≤ (operationalTwoPRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalTwoP (by decide)
    (267554942803 : ℤ) 500000 (by decide) operationalTwoP_integer_rows i using 1
  norm_num [operationalTwoPRowBound]
def operationalTwoPInverseRowBound : ℚ := (3125035980433657243505775502893595360125692336597000000/133226763032165069727253435929914233689647876191037057 : ℚ)
theorem operationalTwoPInverse_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalTwoPInverse.entries i j|) * (133226763032165069727253435929914233689647876191037057 : ℤ) ≤
      (3125035980433657243505775502893595360125692336597000000 : ℤ) * (operationalTwoPInverse.denominator : ℤ) := by
  decide +kernel
theorem operationalTwoPInverse_absolute_rows (i : Fin 9) :
    (∑ j, |operationalTwoPInverse.realMatrix i j|) ≤ (operationalTwoPInverseRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalTwoPInverse (by decide)
    (3125035980433657243505775502893595360125692336597000000 : ℤ) 133226763032165069727253435929914233689647876191037057 (by decide) operationalTwoPInverse_integer_rows i using 1
  norm_num [operationalTwoPInverseRowBound]
theorem operationalTwoPInverse_integer_symm : operationalTwoPInverse.entries.IsSymm := by decide
theorem operationalTwoPInverse_real_symm : operationalTwoPInverse.realMatrix.IsSymm := by
  ext i j
  change (operationalTwoPInverse.denominator : ℝ)⁻¹ * (operationalTwoPInverse.entries j i : ℝ) =
    (operationalTwoPInverse.denominator : ℝ)⁻¹ * (operationalTwoPInverse.entries i j : ℝ)
  rw [operationalTwoPInverse_integer_symm.apply i j]
def operationalTwoQInverseRowBound : ℚ := (1916331617607692731195436835517346930855870263982226379902736014009449191481413053242053436977839350823669753869670560342257298304034737499861751750337646592798004362106106830694392483085502367970845761858530579434865586214691270517024080115709594634845319300708575820743198296856928419874849977924130118250000/1916195757857176538809122632898915826093941847713815161057011623291677199810457205567830902465117881543118196237889036556745520656694840154408666241837994938646423815880725544696240546190931118465548852069537695371185334087463335881430446986124385705785355462539663236960752408261233730705034346873073312281401 : ℚ)
theorem operationalTwoQInverse_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalTwoQInverse.entries i j|) * (1916195757857176538809122632898915826093941847713815161057011623291677199810457205567830902465117881543118196237889036556745520656694840154408666241837994938646423815880725544696240546190931118465548852069537695371185334087463335881430446986124385705785355462539663236960752408261233730705034346873073312281401 : ℤ) ≤
      (1916331617607692731195436835517346930855870263982226379902736014009449191481413053242053436977839350823669753869670560342257298304034737499861751750337646592798004362106106830694392483085502367970845761858530579434865586214691270517024080115709594634845319300708575820743198296856928419874849977924130118250000 : ℤ) * (operationalTwoQInverse.denominator : ℤ) := by
  decide +kernel
theorem operationalTwoQInverse_absolute_rows (i : Fin 9) :
    (∑ j, |operationalTwoQInverse.realMatrix i j|) ≤ (operationalTwoQInverseRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalTwoQInverse (by decide)
    (1916331617607692731195436835517346930855870263982226379902736014009449191481413053242053436977839350823669753869670560342257298304034737499861751750337646592798004362106106830694392483085502367970845761858530579434865586214691270517024080115709594634845319300708575820743198296856928419874849977924130118250000 : ℤ) 1916195757857176538809122632898915826093941847713815161057011623291677199810457205567830902465117881543118196237889036556745520656694840154408666241837994938646423815880725544696240546190931118465548852069537695371185334087463335881430446986124385705785355462539663236960752408261233730705034346873073312281401 (by decide) operationalTwoQInverse_integer_rows i using 1
  norm_num [operationalTwoQInverseRowBound]
theorem operationalTwoQInverse_integer_symm : operationalTwoQInverse.entries.IsSymm := by decide
theorem operationalTwoQInverse_real_symm : operationalTwoQInverse.realMatrix.IsSymm := by
  ext i j
  change (operationalTwoQInverse.denominator : ℝ)⁻¹ * (operationalTwoQInverse.entries j i : ℝ) =
    (operationalTwoQInverse.denominator : ℝ)⁻¹ * (operationalTwoQInverse.entries i j : ℝ)
  rw [operationalTwoQInverse_integer_symm.apply i j]
def operationalTwoDecayMargin : ℚ := (2313420339089540192561208978756556878652132333783377953977603237309733852100519015643643880949575727617939337589710945882233864690643091334453384923329461471309539060259439463862583634237265311178207991671970124297000712496016409172492231098762644568365016468017855760446206638257993793024276551843986844268013585858308908996828547066676913655720639507834006074512307335229863958871689631417751859416013479/2371834886972293759807356663340487578848094772830564478699949075620927899269630752084563379314149251945105737883692422216313142888340473333639154054712602729861383804113812612901146974517873148383968023918225436596139463664037998797598263048494918468334179369652401438989145016876614416422302191863415327731624349350418221107831806668042560930943823284832902024714881512569532020809741107200000000000000000 : ℚ)
theorem operationalTwo_decay_margin_positive : 0 < operationalTwoDecayMargin := by decide +kernel
theorem operationalTwo_initial_energy_margin :
    operationalTwoPRowBound * (1/327680000000 : ℚ)^2 < (1/100 : ℚ) * ((1/16384000 : ℚ)/2)^2 := by decide +kernel
theorem operationalTwo_physical_recovery_time :
    6 * (10/1 : ℚ) * operationalTwoPRowBound / operationalTwoDecayMargin ≤ (32918000/1 : ℚ) := by decide +kernel
theorem operationalTwo_P_lower_constant : (1/100 : ℚ) ≤ 1/operationalTwoPInverseRowBound := by decide +kernel
theorem operationalTwo_readout_lower : (1439001/20000000 : ℚ) ≤ (145088256/1988871157 : ℚ) - (509151582943/509151016192000 : ℚ) := by decide +kernel
theorem operationalTwo_readout_upper : (145088256/1988871157 : ℚ) + (509151582943/509151016192000 : ℚ) ≤ (3697503/50000000 : ℚ) := by decide +kernel
theorem operationalTwo_P_upper (v : Fin 9 → ℝ) :
    v ⬝ᵥ (operationalTwoP.realMatrix *ᵥ v) ≤ (operationalTwoPRowBound : ℝ)*(∑ i, v i^2) :=
  symmetric_quadratic_le_of_rowBound _ operationalTwoP_posDef.isHermitian.isSymm
    _ operationalTwoP_absolute_rows v
theorem operationalTwo_P_inverse_coercivity (v : Fin 9 → ℝ) :
    (∑ i, v i^2)/(operationalTwoPInverseRowBound : ℝ) ≤ v ⬝ᵥ (operationalTwoP.realMatrix *ᵥ v) :=
  posDef_quadratic_lower_of_inverse_rowBound _ _ operationalTwoP_posDef
    operationalTwoPInverse_real_symm operationalTwoP_real_inverse _
    (by norm_num [operationalTwoPInverseRowBound]) operationalTwoPInverse_absolute_rows v
theorem operationalTwo_Q_inverse_coercivity (v : Fin 9 → ℝ) :
    (∑ i, v i^2)/(operationalTwoQInverseRowBound : ℝ) ≤ v ⬝ᵥ (operationalTwoQ.realMatrix *ᵥ v) :=
  posDef_quadratic_lower_of_inverse_rowBound _ _ operationalTwoQ_posDef
    operationalTwoQInverse_real_symm operationalTwoQ_real_inverse _
    (by norm_num [operationalTwoQInverseRowBound]) operationalTwoQInverse_absolute_rows v
end
end PhosphorylationStableCapacity
