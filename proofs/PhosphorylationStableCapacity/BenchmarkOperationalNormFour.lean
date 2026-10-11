module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalPositivityFour
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixRowBound
public import proofs.PhosphorylationStableCapacity.SymmetricMatrixRowQuadraticBounds

@[expose] public section
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators
def operationalFourPRowBound : ℚ := (383168493033/1000000 : ℚ)
theorem operationalFourP_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalFourP.entries i j|) * (1000000 : ℤ) ≤
      (383168493033 : ℤ) * (operationalFourP.denominator : ℤ) := by
  decide +kernel
theorem operationalFourP_absolute_rows (i : Fin 9) :
    (∑ j, |operationalFourP.realMatrix i j|) ≤ (operationalFourPRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalFourP (by decide)
    (383168493033 : ℤ) 1000000 (by decide) operationalFourP_integer_rows i using 1
  norm_num [operationalFourPRowBound]
def operationalFourPInverseRowBound : ℚ := (1167281599789005576951180580597285027309051527027682000000/39347838858762456545654326653279173876744413868067024811 : ℚ)
theorem operationalFourPInverse_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalFourPInverse.entries i j|) * (39347838858762456545654326653279173876744413868067024811 : ℤ) ≤
      (1167281599789005576951180580597285027309051527027682000000 : ℤ) * (operationalFourPInverse.denominator : ℤ) := by
  decide +kernel
theorem operationalFourPInverse_absolute_rows (i : Fin 9) :
    (∑ j, |operationalFourPInverse.realMatrix i j|) ≤ (operationalFourPInverseRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalFourPInverse (by decide)
    (1167281599789005576951180580597285027309051527027682000000 : ℤ) 39347838858762456545654326653279173876744413868067024811 (by decide) operationalFourPInverse_integer_rows i using 1
  norm_num [operationalFourPInverseRowBound]
theorem operationalFourPInverse_integer_symm : operationalFourPInverse.entries.IsSymm := by decide
theorem operationalFourPInverse_real_symm : operationalFourPInverse.realMatrix.IsSymm := by
  ext i j
  change (operationalFourPInverse.denominator : ℝ)⁻¹ * (operationalFourPInverse.entries j i : ℝ) =
    (operationalFourPInverse.denominator : ℝ)⁻¹ * (operationalFourPInverse.entries i j : ℝ)
  rw [operationalFourPInverse_integer_symm.apply i j]
def operationalFourQInverseRowBound : ℚ := (871158019853679249320108067183476477321238412470157625381183898096178131523161542609251580449329353978763404440201419519429599951331051534756168263580783039350422104715119990475642483488155780951287852809909098654530982915685409572665382305035639821169629728694839662348816165876868348602470533209996325000000/871043166174478968925009865970497200908546828336957027005472574786100273253003416147125667564747065327837992567594410558973200263831695644529623335845537466575682967718319914331345843772278221761669011536684725109665499017028177798055035901386109881593982212743820692324287920755080262875810428582250294443917 : ℚ)
theorem operationalFourQInverse_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalFourQInverse.entries i j|) * (871043166174478968925009865970497200908546828336957027005472574786100273253003416147125667564747065327837992567594410558973200263831695644529623335845537466575682967718319914331345843772278221761669011536684725109665499017028177798055035901386109881593982212743820692324287920755080262875810428582250294443917 : ℤ) ≤
      (871158019853679249320108067183476477321238412470157625381183898096178131523161542609251580449329353978763404440201419519429599951331051534756168263580783039350422104715119990475642483488155780951287852809909098654530982915685409572665382305035639821169629728694839662348816165876868348602470533209996325000000 : ℤ) * (operationalFourQInverse.denominator : ℤ) := by
  decide +kernel
theorem operationalFourQInverse_absolute_rows (i : Fin 9) :
    (∑ j, |operationalFourQInverse.realMatrix i j|) ≤ (operationalFourQInverseRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalFourQInverse (by decide)
    (871158019853679249320108067183476477321238412470157625381183898096178131523161542609251580449329353978763404440201419519429599951331051534756168263580783039350422104715119990475642483488155780951287852809909098654530982915685409572665382305035639821169629728694839662348816165876868348602470533209996325000000 : ℤ) 871043166174478968925009865970497200908546828336957027005472574786100273253003416147125667564747065327837992567594410558973200263831695644529623335845537466575682967718319914331345843772278221761669011536684725109665499017028177798055035901386109881593982212743820692324287920755080262875810428582250294443917 (by decide) operationalFourQInverse_integer_rows i using 1
  norm_num [operationalFourQInverseRowBound]
theorem operationalFourQInverse_integer_symm : operationalFourQInverse.entries.IsSymm := by decide
theorem operationalFourQInverse_real_symm : operationalFourQInverse.realMatrix.IsSymm := by
  ext i j
  change (operationalFourQInverse.denominator : ℝ)⁻¹ * (operationalFourQInverse.entries j i : ℝ) =
    (operationalFourQInverse.denominator : ℝ)⁻¹ * (operationalFourQInverse.entries i j : ℝ)
  rw [operationalFourQInverse_integer_symm.apply i j]
def operationalFourDecayMargin : ℚ := (390391618960160560848407330506436102114539076028171632905800972471658874124172427557686801503784664104351904762226836122673373930778307533649171765975183222533224810177025240176172054706813283787235201336323362346879785134133858998951511585538531590850128524479152036179478524190177139141100505093626053667549304744618008693609886598680472583430200524459893820003559169405399541797046566680347643819/397905262913780449054944299661547063862403588391038724741018604082590549329007434883146588782394115748134894419481894824607627478457439971670653869033010226804262120084226044390136808097138614088760037713211328967275899787021273788293864738683900976805929970791949664238890281526317678471063484088179828894023803261912877092341144466099570260741641883465218500370410610597023029657600000000000000000 : ℚ)
theorem operationalFour_decay_margin_positive : 0 < operationalFourDecayMargin := by decide +kernel
theorem operationalFour_initial_energy_margin :
    operationalFourPRowBound * (1/40960000000 : ℚ)^2 < (1/100 : ℚ) * ((1/2048000 : ℚ)/2)^2 := by decide +kernel
theorem operationalFour_physical_recovery_time :
    6 * (10/1 : ℚ) * operationalFourPRowBound / operationalFourDecayMargin ≤ (23433000/1 : ℚ) := by decide +kernel
theorem operationalFour_P_lower_constant : (1/100 : ℚ) ≤ 1/operationalFourPInverseRowBound := by decide +kernel
theorem operationalFour_readout_lower : (10757833/50000000 : ℚ) ≤ (11901771/55060850 : ℚ) - (451070384971/451058483200000 : ℚ) := by decide +kernel
theorem operationalFour_readout_upper : (11901771/55060850 : ℚ) + (451070384971/451058483200000 : ℚ) ≤ (2714459/12500000 : ℚ) := by decide +kernel
theorem operationalFour_P_upper (v : Fin 9 → ℝ) :
    v ⬝ᵥ (operationalFourP.realMatrix *ᵥ v) ≤ (operationalFourPRowBound : ℝ)*(∑ i, v i^2) :=
  symmetric_quadratic_le_of_rowBound _ operationalFourP_posDef.isHermitian.isSymm
    _ operationalFourP_absolute_rows v
theorem operationalFour_P_inverse_coercivity (v : Fin 9 → ℝ) :
    (∑ i, v i^2)/(operationalFourPInverseRowBound : ℝ) ≤ v ⬝ᵥ (operationalFourP.realMatrix *ᵥ v) :=
  posDef_quadratic_lower_of_inverse_rowBound _ _ operationalFourP_posDef
    operationalFourPInverse_real_symm operationalFourP_real_inverse _
    (by norm_num [operationalFourPInverseRowBound]) operationalFourPInverse_absolute_rows v
theorem operationalFour_Q_inverse_coercivity (v : Fin 9 → ℝ) :
    (∑ i, v i^2)/(operationalFourQInverseRowBound : ℝ) ≤ v ⬝ᵥ (operationalFourQ.realMatrix *ᵥ v) :=
  posDef_quadratic_lower_of_inverse_rowBound _ _ operationalFourQ_posDef
    operationalFourQInverse_real_symm operationalFourQ_real_inverse _
    (by norm_num [operationalFourQInverseRowBound]) operationalFourQInverse_absolute_rows v
end
end PhosphorylationStableCapacity
