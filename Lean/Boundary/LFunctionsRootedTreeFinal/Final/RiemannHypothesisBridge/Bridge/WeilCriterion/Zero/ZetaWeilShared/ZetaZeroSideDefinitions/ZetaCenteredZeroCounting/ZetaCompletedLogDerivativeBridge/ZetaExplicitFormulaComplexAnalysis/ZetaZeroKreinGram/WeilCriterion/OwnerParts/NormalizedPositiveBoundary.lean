import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner

/-!
# Normalized positive completed boundary
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The positive boundary scalar in the same `2 pi` normalization as the
contour-derived completed boundary. -/
noncomputable def zetaCompletedNormalizedPositiveBoundaryScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeDefectKernelPositiveChannel f +
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f)

/-- The real Cauchy normalization is positive. -/
theorem explicitFormula_realTwoPi_pos : 0 < 2 * Real.pi :=
  mul_pos zero_lt_two Real.pi_pos

/-- The normalized positive boundary scalar is nonnegative. -/
theorem zetaCompletedNormalizedPositiveBoundaryScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedNormalizedPositiveBoundaryScalar f :=
  let hprime : 0 ≤ completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeDefectKernelPositiveChannel_nonnegative f
  let harch :
      0 ≤ ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram_nonnegative
      (zetaCompletedHermitianBoundaryDefect f)
  add_nonneg hprime harch

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
