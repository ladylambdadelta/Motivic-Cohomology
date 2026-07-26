import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompressionSource

/-!
# Endpoint positive Bessel kernel source

This file owns the finite endpoint Bessel estimate against the full completed
positive GNS presentation.  This is the endpoint compression theorem used by
physical absorption; it does not collapse the positive packet to only the
centered archimedean and correction coordinates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The full positive endpoint Bessel kernel Gram. -/
noncomputable def completedEndpointPositiveBesselKernelGram
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedGNSPositiveBoundaryPresentationScalar f

/-- The full positive endpoint Bessel Schur remainder. -/
noncomputable def completedEndpointPositiveBesselSchurRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedEndpointPositiveBesselKernelGram f -
    (completedWeilEndpointTraceFiber f).gram

/-- The full positive endpoint Bessel kernel Gram unfolds to the completed
positive GNS presentation scalar. -/
theorem completedEndpointPositiveBesselKernelGram_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointPositiveBesselKernelGram f =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  rfl

/-- The full positive endpoint Bessel Schur remainder unfolds to kernel Gram
minus endpoint trace Gram. -/
theorem completedEndpointPositiveBesselSchurRemainder_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointPositiveBesselSchurRemainder f =
      completedEndpointPositiveBesselKernelGram f -
        (completedWeilEndpointTraceFiber f).gram := by
  rfl

/-- The full positive endpoint Bessel Schur remainder is the
positive-presentation endpoint compression remainder. -/
theorem completedEndpointPositiveBesselSchurRemainder_eq_positivePresentationRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointPositiveBesselSchurRemainder f =
      completedEndpointFiberPositivePresentationRemainder f := by
  rfl

/-- Finite-Bessel nonnegativity of the full positive endpoint Bessel Schur
remainder after physical-boundary-to-positive-presentation transport. -/
theorem completedEndpointPositiveBesselSchurRemainder_nonnegative_source_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤ completedEndpointPositiveBesselSchurRemainder f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointPositiveBesselSchurRemainder_eq_positivePresentationRemainder
      f).symm
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_traceCompression_of_finiteBessel
      f D hnonPrime boundary_eq_positive)

/-- Finite-Bessel domination of the endpoint trace fiber by the full positive
Bessel kernel Gram after scalar transport. -/
theorem completedWeilEndpointTraceFiber_gram_le_positiveBesselKernelGram_source_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      completedEndpointPositiveBesselKernelGram f :=
  let hsub :
      0 ≤
        completedEndpointPositiveBesselKernelGram f -
          (completedWeilEndpointTraceFiber f).gram :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointPositiveBesselSchurRemainder_eq f)
      (completedEndpointPositiveBesselSchurRemainder_nonnegative_source_of_finiteBessel
        f D hnonPrime boundary_eq_positive)
  sub_nonneg.mp hsub

/-- Finite-Bessel domination of the endpoint trace fiber by the completed
positive GNS presentation scalar after scalar transport. -/
theorem completedWeilEndpointTraceFiber_gram_le_positivePresentation_source_besselKernel_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  Eq.subst
    (motive := fun value : ℝ =>
      (completedWeilEndpointTraceFiber f).gram ≤ value)
    (completedEndpointPositiveBesselKernelGram_eq f)
    (completedWeilEndpointTraceFiber_gram_le_positiveBesselKernelGram_source_of_finiteBessel
      f D hnonPrime boundary_eq_positive)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
