module
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleBoundsOne
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainSimpleSpectrum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The right-half-plane spectral point of the first three-site saddle
certificate, if present, has algebraic multiplicity one. -/
theorem benchmarkSaddleOne_simple_right (z : ℂ)
    (hz : 0 ≤ z.re) (hroot : benchmarkSaddleOneBC.charpoly.eval z = 0) :
    benchmarkSaddleOneBC.charpoly.derivative.eval z ≠ 0 := by
  exact block_spectrum_simple_right benchmarkSaddleOneBC
    (1 / 5) (1 / 1000) (1 / 100) (1 / 500)
    (by norm_num) benchmarkSaddleOne_row_bound
    benchmarkSaddleOne_col_bound (by norm_num) (by norm_num)
    benchmarkSaddleOne_feedback_bound (by norm_num)
    z hz hroot

end
end PhosphorylationStableCapacity
