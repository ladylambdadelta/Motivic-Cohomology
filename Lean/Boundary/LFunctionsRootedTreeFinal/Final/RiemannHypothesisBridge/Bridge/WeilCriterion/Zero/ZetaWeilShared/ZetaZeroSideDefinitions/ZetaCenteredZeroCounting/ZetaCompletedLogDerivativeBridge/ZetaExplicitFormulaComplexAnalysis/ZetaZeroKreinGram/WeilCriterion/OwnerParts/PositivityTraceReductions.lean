import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointAbsorptionAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceKernelSplit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.EndpointTraceReconstruction

/-!
# Trace-comparison reductions for completed Weil positivity

This owner part contains the final trace-comparison wrappers that reduce
completed Weil positivity to endpoint trace remainders and Hilbert-source
domination statements.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Completed Weil positivity in the standard completed-boundary coordinate
used by contour assembly.  The reduction below deliberately exposes only the
boundary identification and endpoint absorption certificate; the trace and
prime reductions state their own genuine hypotheses separately.  This keeps
the unconditional boundary transport distinct from the analytic transport
that actually consumes those estimates. -/
theorem zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_completedBoundary_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (endpointAbsorption :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤ ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar f) :
    ZetaWeilQuadraticPositivity :=
  fun f =>
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (boundaryIdentification f).symm
      (completedBoundaryChannel_convolutionAutocorrelation_re_nonnegative_of_endpointAbsorbedPhysical_owner
        f (endpointAbsorption f))

/-- Completed Weil positivity follows from a trace reconstruction that splits
the physical boundary into endpoint diagonal debt plus a nonnegative remainder. -/
theorem zetaWeilQuadraticPositivity_of_endpointTraceRemainder_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (endpointRemainder :
      ∀ f : ZetaAdmissibleFunction,
        ∃ remainder : ℝ,
          Complex.re
              (ZetaAdmissibleFunction.completedBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
            (ZetaAdmissibleFunction.zetaCompletedEndpointCorrectionPacket f).diagonalDebt +
              remainder ∧
          0 ≤ remainder) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_owner
    boundaryIdentification
    (fun f =>
      Exists.elim (endpointRemainder f)
        (fun remainder remainderSpec =>
          ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_boundary_eq_diagonalDebt_add_nonnegativeRemainder
            f remainder remainderSpec.1 remainderSpec.2))

/-- Completed Weil positivity follows from nonnegativity of the named endpoint
trace-compression remainder. -/
theorem zetaWeilQuadraticPositivity_of_endpointTraceCompression_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (endpointTraceRemainderNonnegative :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤ ZetaAdmissibleFunction.completedWeilEndpointTraceRemainder f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_owner
    boundaryIdentification
    (fun f =>
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceRemainder
        f (endpointTraceRemainderNonnegative f))

/-- Completed Weil positivity follows from prime-channel comparison and
endpoint-fiber domination of the positive GNS presentation. -/
theorem zetaWeilQuadraticPositivity_of_primeComparison_endpointFiberDomination_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (primeComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.primeBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f)
    (endpointFiberDomination :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.completedWeilEndpointTraceFiber f).gram ≤
          ZetaAdmissibleFunction.zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointTraceCompression_owner
    boundaryIdentification
    (fun f =>
      ZetaAdmissibleFunction.completedWeilEndpointTraceRemainder_nonnegative_of_primeComparison_endpointFiberDomination
        f (primeComparison f) (endpointFiberDomination f))

/-- Completed Weil positivity follows from prime-channel comparison and
nonnegativity of the positive-presentation endpoint compression remainder. -/
theorem zetaWeilQuadraticPositivity_of_primeComparison_positivePresentationRemainder_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (primeComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.primeBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f)
    (positivePresentationRemainderNonnegative :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedEndpointFiberPositivePresentationRemainder f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointTraceCompression_owner
    boundaryIdentification
    (fun f =>
      ZetaAdmissibleFunction.completedWeilEndpointTraceRemainder_nonnegative_of_primeComparison_positivePresentationRemainder
        f (primeComparison f) (positivePresentationRemainderNonnegative f))

/-- Completed Weil positivity follows from prime-channel comparison and the
canonical Hilbert-source endpoint trace-compression remainder. -/
theorem zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointCompression_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (primeComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.primeBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f)
    (sourceEndpointCompressionNonnegative :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointCompressionRemainder
            (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_primeComparison_positivePresentationRemainder_owner
    boundaryIdentification
    primeComparison
    (fun f =>
      ZetaAdmissibleFunction.completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointCompressionRemainder
        f (sourceEndpointCompressionNonnegative f))

/-- Completed Weil positivity follows from prime-channel comparison and
ordered-heart domination of the canonical endpoint trace fiber. -/
theorem zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointTraceDomination_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (primeComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.primeBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f)
    (sourceEndpointTraceDomination :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointTraceFiber
            (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)).gram ≤
          ZetaAdmissibleFunction.completedOrderedHeartScalar
            (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointCompression_owner
    boundaryIdentification
    primeComparison
    (fun f =>
      ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointGram_le_orderedHeart
        (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)
        (sourceEndpointTraceDomination f))

/-- Completed Weil positivity follows from prime-channel comparison and an
endpoint-kernel split of the canonical ordered-heart scalar. -/
theorem zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointKernelSplit_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (primeComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.primeBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f)
    (sourceEndpointKernelSplit :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelSplit
          (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointTraceDomination_owner
    boundaryIdentification
    primeComparison
    (fun f =>
      ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_endpointKernelSplitProp
        (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)
        (sourceEndpointKernelSplit f))

/-- Completed Weil positivity follows from prime-channel comparison and
nonnegativity of the concrete canonical endpoint kernel remainder. -/
theorem zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointKernelRemainder_owner
    (boundaryIdentification :
      ZetaWeilAutocorrelationCompletedBoundaryIdentification)
    (primeComparison :
      ∀ f : ZetaAdmissibleFunction,
        Complex.re
            (ZetaAdmissibleFunction.primeBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
          ZetaAdmissibleFunction.completedPrimeDefectKernelPositiveChannel f)
    (sourceEndpointKernelRemainderNonnegative :
      ∀ f : ZetaAdmissibleFunction,
        0 ≤
          ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelRemainder
            (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_primeComparison_sourceEndpointKernelSplit_owner
    boundaryIdentification
    primeComparison
    (fun f =>
      ZetaAdmissibleFunction.completedBoundaryHilbertSourceEndpointKernelSplit_of_endpointKernelRemainder_nonnegative
        (ZetaAdmissibleFunction.completedBoundaryHilbertSource f)
        (sourceEndpointKernelRemainderNonnegative f))

end

end LFunctions
end Boundary
