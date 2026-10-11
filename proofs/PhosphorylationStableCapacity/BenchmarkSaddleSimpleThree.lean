module
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleBoundsThree
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainSimpleSpectrum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The right-half-plane spectral point of the second three-site saddle
certificate, if present, has algebraic multiplicity one. -/
theorem benchmarkSaddleThree_simple_right (z : ℂ)
    (hz : 0 ≤ z.re) (hroot : benchmarkSaddleThreeBC.charpoly.eval z = 0) :
    benchmarkSaddleThreeBC.charpoly.derivative.eval z ≠ 0 := by
  exact block_spectrum_simple_right benchmarkSaddleThreeBC
    (1 / 20) (1 / 500) (1 / 20) (1 / 400)
    (by norm_num) benchmarkSaddleThree_row_bound
    benchmarkSaddleThree_col_bound (by norm_num) (by norm_num)
    benchmarkSaddleThree_feedback_bound (by norm_num)
    z hz hroot

end
end PhosphorylationStableCapacity
