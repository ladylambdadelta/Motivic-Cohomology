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
        (zetaCompletedHermitianBoundaryDefect f) /
      (2 * Real.pi)

/-- The real Cauchy normalization is positive. -/
theorem explicitFormula_realTwoPi_pos : 0 < 2 * Real.pi := by
  exact mul_pos zero_lt_two Real.pi_pos

/-- The normalized positive boundary scalar is nonnegative. -/
theorem zetaCompletedNormalizedPositiveBoundaryScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedNormalizedPositiveBoundaryScalar f := by
  unfold zetaCompletedNormalizedPositiveBoundaryScalar
  have hprime : 0 ≤ completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeDefectKernelPositiveChannel_nonnegative f
  have harch :
      0 ≤ ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram_nonnegative
      (zetaCompletedHermitianBoundaryDefect f)
  have hdenominator : 0 ≤ 2 * Real.pi :=
    le_of_lt explicitFormula_realTwoPi_pos
  exact add_nonneg hprime (div_nonneg harch hdenominator)

/-- The normalized archimedean boundary channel is the normalized
archimedean packet Gram on an autocorrelation probe. -/
theorem archimedeanBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (archimedeanBoundaryChannel (convolutionAutocorrelation f)) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) /
        (2 * Real.pi) := by
  let gram : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  have hcontribution :
      zetaCompletedExplicitFormulaArchimedeanContribution
          (convolutionAutocorrelation f) = (gram : ℂ) := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_paired_owner
        f)
      (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram
        f)
  have hquotient :
      zetaCompletedExplicitFormulaArchimedeanContribution
            (convolutionAutocorrelation f) /
          (2 * (Real.pi : ℂ)) =
        ((gram / (2 * Real.pi) : ℝ) : ℂ) := by
    exact Eq.trans
      (congrArg
        (fun numerator : ℂ => numerator / (2 * (Real.pi : ℂ)))
        hcontribution)
      (Complex.ofReal_div gram (2 * Real.pi)).symm
  exact Eq.trans
    (congrArg Complex.re
      (Eq.trans
        (archimedeanBoundaryChannel_unfold (convolutionAutocorrelation f))
        hquotient))
    (Complex.ofReal_re (gram / (2 * Real.pi)))

/-- Once the normalized prime channel is identified with its positive defect
kernel, the entire corrected completed boundary is the normalized positive
scalar. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedPositiveScalar_of_prime
    (f : ZetaAdmissibleFunction)
    (hprime :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedPrimeDefectKernelPositiveChannel f) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      zetaCompletedNormalizedPositiveBoundaryScalar f := by
  have hboundary :
      completedBoundaryChannel (convolutionAutocorrelation f) =
        primeBoundaryChannel (convolutionAutocorrelation f) +
          archimedeanBoundaryChannel (convolutionAutocorrelation f) := by
    calc
      completedBoundaryChannel (convolutionAutocorrelation f) =
          primeBoundaryChannel (convolutionAutocorrelation f) +
            archimedeanBoundaryChannel (convolutionAutocorrelation f) +
            poleBoundaryChannel (convolutionAutocorrelation f) +
            completionBoundaryChannel (convolutionAutocorrelation f) :=
        completedBoundaryChannel_eq_prime_add_archimedean_add_pole_add_completion
          (convolutionAutocorrelation f)
      _ = primeBoundaryChannel (convolutionAutocorrelation f) +
            archimedeanBoundaryChannel (convolutionAutocorrelation f) + 0 + 0 := by
        exact congrArg₂ HAdd.hAdd
          (congrArg₂ HAdd.hAdd Eq.refl
            (poleBoundaryChannel_unfold (convolutionAutocorrelation f)))
          (completionBoundaryChannel_unfold (convolutionAutocorrelation f))
      _ = primeBoundaryChannel (convolutionAutocorrelation f) +
            archimedeanBoundaryChannel (convolutionAutocorrelation f) := by
        exact Eq.trans
          (add_zero
            (primeBoundaryChannel (convolutionAutocorrelation f) +
              archimedeanBoundaryChannel (convolutionAutocorrelation f) + 0))
          (add_zero
            (primeBoundaryChannel (convolutionAutocorrelation f) +
              archimedeanBoundaryChannel (convolutionAutocorrelation f)))
  have harch :=
    archimedeanBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedPacketGram f
  calc
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        Complex.re
          (primeBoundaryChannel (convolutionAutocorrelation f) +
            archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
      exact congrArg Complex.re hboundary
    _ = Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) +
          Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
      exact Complex.add_re
        (primeBoundaryChannel (convolutionAutocorrelation f))
        (archimedeanBoundaryChannel (convolutionAutocorrelation f))
    _ = completedPrimeDefectKernelPositiveChannel f +
          Complex.re (archimedeanBoundaryChannel (convolutionAutocorrelation f)) := by
      exact congrArg
        (fun value : ℝ =>
          value + Complex.re
            (archimedeanBoundaryChannel (convolutionAutocorrelation f)))
        hprime
    _ = completedPrimeDefectKernelPositiveChannel f +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) /
            (2 * Real.pi) := by
      exact congrArg
        (fun value : ℝ => completedPrimeDefectKernelPositiveChannel f + value)
        harch
    _ = zetaCompletedNormalizedPositiveBoundaryScalar f := by
      exact Eq.refl _

/-- The corrected completed boundary is nonnegative once its normalized prime
channel has been reconstructed. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_normalizedPrime
    (f : ZetaAdmissibleFunction)
    (hprime :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedPrimeDefectKernelPositiveChannel f) :
    0 ≤ Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedBoundaryChannel_convolutionAutocorrelation_re_eq_normalizedPositiveScalar_of_prime
      f hprime).symm
    (zetaCompletedNormalizedPositiveBoundaryScalar_nonnegative f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
