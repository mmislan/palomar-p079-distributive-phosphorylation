module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalPositivityZero
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixRowBound
public import proofs.PhosphorylationStableCapacity.SymmetricMatrixRowQuadraticBounds

@[expose] public section
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators
def operationalZeroPRowBound : ℚ := (1461527851/250000 : ℚ)
theorem operationalZeroP_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalZeroP.entries i j|) * (250000 : ℤ) ≤
      (1461527851 : ℤ) * (operationalZeroP.denominator : ℤ) := by
  decide +kernel
theorem operationalZeroP_absolute_rows (i : Fin 9) :
    (∑ j, |operationalZeroP.realMatrix i j|) ≤ (operationalZeroPRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalZeroP (by decide)
    (1461527851 : ℤ) 250000 (by decide) operationalZeroP_integer_rows i using 1
  norm_num [operationalZeroPRowBound]
def operationalZeroPInverseRowBound : ℚ := (48187036296019197604470853490468205525696414280793000000/3224195589555720247210320956702385931783305169318213997 : ℚ)
theorem operationalZeroPInverse_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalZeroPInverse.entries i j|) * (3224195589555720247210320956702385931783305169318213997 : ℤ) ≤
      (48187036296019197604470853490468205525696414280793000000 : ℤ) * (operationalZeroPInverse.denominator : ℤ) := by
  decide +kernel
theorem operationalZeroPInverse_absolute_rows (i : Fin 9) :
    (∑ j, |operationalZeroPInverse.realMatrix i j|) ≤ (operationalZeroPInverseRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalZeroPInverse (by decide)
    (48187036296019197604470853490468205525696414280793000000 : ℤ) 3224195589555720247210320956702385931783305169318213997 (by decide) operationalZeroPInverse_integer_rows i using 1
  norm_num [operationalZeroPInverseRowBound]
theorem operationalZeroPInverse_integer_symm : operationalZeroPInverse.entries.IsSymm := by decide
theorem operationalZeroPInverse_real_symm : operationalZeroPInverse.realMatrix.IsSymm := by
  ext i j
  change (operationalZeroPInverse.denominator : ℝ)⁻¹ * (operationalZeroPInverse.entries j i : ℝ) =
    (operationalZeroPInverse.denominator : ℝ)⁻¹ * (operationalZeroPInverse.entries i j : ℝ)
  rw [operationalZeroPInverse_integer_symm.apply i j]
def operationalZeroQInverseRowBound : ℚ := (214293678973578852400330352952665342669177040720012863566849958051485669864098879122109912393266380270682903085541285378613840342819244787910593174676206816055127430885299633501649628997150916906427275454318532278362000704769020231815753019864305682116122063162601336775770588336570077453952369441585381000000/214283337914526053652120080250768071668269602701315783620477753746566027240047001509399608876062015428789688954616816846813582995358979983204837027906528659535892347391103616969348125685066880886362001725713128652320914002108627354553838264471296314140857614201760450325176244193601880475367940417461533790363 : ℚ)
theorem operationalZeroQInverse_integer_rows :
    ∀ i : Fin 9, (∑ j, |operationalZeroQInverse.entries i j|) * (214283337914526053652120080250768071668269602701315783620477753746566027240047001509399608876062015428789688954616816846813582995358979983204837027906528659535892347391103616969348125685066880886362001725713128652320914002108627354553838264471296314140857614201760450325176244193601880475367940417461533790363 : ℤ) ≤
      (214293678973578852400330352952665342669177040720012863566849958051485669864098879122109912393266380270682903085541285378613840342819244787910593174676206816055127430885299633501649628997150916906427275454318532278362000704769020231815753019864305682116122063162601336775770588336570077453952369441585381000000 : ℤ) * (operationalZeroQInverse.denominator : ℤ) := by
  decide +kernel
theorem operationalZeroQInverse_absolute_rows (i : Fin 9) :
    (∑ j, |operationalZeroQInverse.realMatrix i j|) ≤ (operationalZeroQInverseRowBound : ℝ) := by
  convert ScaledIntegerMatrix.absolute_row_bound operationalZeroQInverse (by decide)
    (214293678973578852400330352952665342669177040720012863566849958051485669864098879122109912393266380270682903085541285378613840342819244787910593174676206816055127430885299633501649628997150916906427275454318532278362000704769020231815753019864305682116122063162601336775770588336570077453952369441585381000000 : ℤ) 214283337914526053652120080250768071668269602701315783620477753746566027240047001509399608876062015428789688954616816846813582995358979983204837027906528659535892347391103616969348125685066880886362001725713128652320914002108627354553838264471296314140857614201760450325176244193601880475367940417461533790363 (by decide) operationalZeroQInverse_integer_rows i using 1
  norm_num [operationalZeroQInverseRowBound]
theorem operationalZeroQInverse_integer_symm : operationalZeroQInverse.entries.IsSymm := by decide
theorem operationalZeroQInverse_real_symm : operationalZeroQInverse.realMatrix.IsSymm := by
  ext i j
  change (operationalZeroQInverse.denominator : ℝ)⁻¹ * (operationalZeroQInverse.entries j i : ℝ) =
    (operationalZeroQInverse.denominator : ℝ)⁻¹ * (operationalZeroQInverse.entries i j : ℝ)
  rw [operationalZeroQInverse_integer_symm.apply i j]
def operationalZeroDecayMargin : ℚ := (145328706557919795738200856652951977017906713348296860215415578415070659372549966905706916126497068518796501570986655871171030380578575525468020010699522030388281656686731039503788471774227646587932242542009158882939856627805511725142898028807245900895900601403855446869234183163639600499077498724723533291287783039058223737167908907669692425427927980479981305315509520136641719800106586798633287/147518187717985264629029662871450618248297804654867439360424533064196965264232620940555528919100246603253139536304228791805554875655870391721042474498140050757606931496157285101009613438702403145840099756586334344176951797052448987570758761747296683351880455610313709240839881864807535774833312099179458870266117962264125303783964746002232474758026570409199588515600429133437337600000000000000000 : ℚ)
theorem operationalZero_decay_margin_positive : 0 < operationalZeroDecayMargin := by decide +kernel
theorem operationalZero_initial_energy_margin :
    operationalZeroPRowBound * (1/16384000000 : ℚ)^2 < (1/100 : ℚ) * ((1/8192000 : ℚ)/2)^2 := by decide +kernel
theorem operationalZero_physical_recovery_time :
    6 * (10/1 : ℚ) * operationalZeroPRowBound / operationalZeroDecayMargin ≤ (357000/1 : ℚ) := by decide +kernel
theorem operationalZero_P_lower_constant : (1/100 : ℚ) ≤ 1/operationalZeroPInverseRowBound := by decide +kernel
theorem operationalZero_readout_lower : (23797/10000000 : ℚ) ≤ (566751/167692250 : ℚ) - (5494940214751/5494939648000000 : ℚ) := by decide +kernel
theorem operationalZero_readout_upper : (566751/167692250 : ℚ) + (5494940214751/5494939648000000 : ℚ) ≤ (437971/100000000 : ℚ) := by decide +kernel
theorem operationalZero_P_upper (v : Fin 9 → ℝ) :
    v ⬝ᵥ (operationalZeroP.realMatrix *ᵥ v) ≤ (operationalZeroPRowBound : ℝ)*(∑ i, v i^2) :=
  symmetric_quadratic_le_of_rowBound _ operationalZeroP_posDef.isHermitian.isSymm
    _ operationalZeroP_absolute_rows v
theorem operationalZero_P_inverse_coercivity (v : Fin 9 → ℝ) :
    (∑ i, v i^2)/(operationalZeroPInverseRowBound : ℝ) ≤ v ⬝ᵥ (operationalZeroP.realMatrix *ᵥ v) :=
  posDef_quadratic_lower_of_inverse_rowBound _ _ operationalZeroP_posDef
    operationalZeroPInverse_real_symm operationalZeroP_real_inverse _
    (by norm_num [operationalZeroPInverseRowBound]) operationalZeroPInverse_absolute_rows v
theorem operationalZero_Q_inverse_coercivity (v : Fin 9 → ℝ) :
    (∑ i, v i^2)/(operationalZeroQInverseRowBound : ℝ) ≤ v ⬝ᵥ (operationalZeroQ.realMatrix *ᵥ v) :=
  posDef_quadratic_lower_of_inverse_rowBound _ _ operationalZeroQ_posDef
    operationalZeroQInverse_real_symm operationalZeroQ_real_inverse _
    (by norm_num [operationalZeroQInverseRowBound]) operationalZeroQInverse_absolute_rows v
end
end PhosphorylationStableCapacity
