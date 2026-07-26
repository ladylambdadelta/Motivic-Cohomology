import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBoundParts.PrimeOffDiagonalZero

/-!
# Centered endpoint Riesz source kernel split

This file owns the algebraic passage from canonical Hilbert-source endpoint
compression to the physical positive-kernel endpoint trace split.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Projection-complement nonnegativity gives nonnegativity of the seed
positive-presentation endpoint compression remainder for the centered endpoint
Riesz lane. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceKernelSplit_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  fun hcomplement =>
    completedEndpointFiberPositivePresentationRemainder_nonnegative_of_positiveBesselSchurRemainder_centeredRiesz
      f
      (completedEndpointPositiveBesselSchurRemainder_nonnegative_centeredRiesz_of_projectionComplement
        f hcomplement)

/-- Projection-complement nonnegativity gives seed-level endpoint trace-fiber
domination by the positive GNS presentation for the centered endpoint Riesz
lane. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_sourceKernelSplit_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    f).mp
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceKernelSplit_of_projectionComplement
      f hcomplement)

/-- Projection-complement nonnegativity gives domination of the canonical
Hilbert-source endpoint trace fiber by the ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  fun hcomplement =>
  let sourceGram : ℝ :=
    (completedBoundaryHilbertSourceEndpointTraceFiber
      (completedBoundaryHilbertSource f)).gram
  let seedGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  let orderedScalar : ℝ :=
    completedOrderedHeartScalar (completedBoundaryHilbertSource f)
  let positiveScalar : ℝ :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar f
  let hsourceSeed : sourceGram = seedGram :=
    completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f
  let hseedPositive : seedGram ≤ positiveScalar :=
    completedEndpointTraceFiber_gram_le_positivePresentation_sourceKernelSplit_of_projectionComplement
      f hcomplement
  let hsourcePositive : sourceGram ≤ positiveScalar :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ positiveScalar)
      hsourceSeed.symm
      hseedPositive
  let hpositiveOrdered : positiveScalar = orderedScalar :=
    (completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar
      f).symm
  Eq.subst
    (motive := fun value : ℝ => sourceGram ≤ value)
    hpositiveOrdered
    hsourcePositive

/-- Projection-complement nonnegativity gives nonnegativity of the canonical
Hilbert-source endpoint compression remainder for the centered endpoint Riesz
lane. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
  fun hcomplement =>
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
      f)
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceKernelSplit_of_projectionComplement
      f hcomplement)

/-- Prime-boundary comparison for the centered endpoint Riesz source. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_centeredRiesz_source
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f := by
  have hboundary :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        completedPrimeOffDiagonalChannel f :=
    (completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f).symm
  have hoffZero :
      completedPrimeOffDiagonalChannel f = 0 :=
    completedPrimeOffDiagonalChannel_eq_zero_centeredRiesz_source
      f hcoordinateZero
  have hpositiveZero :
      0 = completedPrimeDefectKernelPositiveChannel f :=
    (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f).symm
  exact hboundary.trans (hoffZero.trans hpositiveZero)

/-- The canonical Hilbert source ordered-heart scalar splits into endpoint
fiber Gram plus the source endpoint compression remainder. -/
theorem completedOrderedHeartScalar_source_eq_endpointFiberGram_add_sourceCompressionRemainder
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
      (completedWeilEndpointTraceFiber f).gram +
        completedBoundaryHilbertSourceEndpointCompressionRemainder
          (completedBoundaryHilbertSource f) := by
  let source : CompletedBoundaryHilbertSource :=
    completedBoundaryHilbertSource f
  let sourceGram : ℝ :=
    (completedBoundaryHilbertSourceEndpointTraceFiber source).gram
  let seedGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  let remainder : ℝ :=
    completedBoundaryHilbertSourceEndpointCompressionRemainder source
  have hsplit :
      completedOrderedHeartScalar source = sourceGram + remainder := by
    unfold remainder
    exact
      endpointTraceDebt_add_sub_cancel
        (completedOrderedHeartScalar source)
        (completedBoundaryHilbertSourceEndpointTraceFiber source).gram
  have hgram : sourceGram = seedGram := by
    unfold sourceGram
    unfold seedGram
    unfold source
    exact completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f
  have htarget :
      sourceGram + remainder = seedGram + remainder :=
    congrArg (fun value : ℝ => value + remainder) hgram
  exact hsplit.trans htarget

/-- The positive GNS scalar splits into endpoint fiber Gram plus the source
endpoint compression remainder. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_endpointFiberGram_add_sourceCompressionRemainder
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      (completedWeilEndpointTraceFiber f).gram +
        completedBoundaryHilbertSourceEndpointCompressionRemainder
          (completedBoundaryHilbertSource f) := by
  have hordered :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
    (completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar
      f).symm
  exact hordered.trans
    (completedOrderedHeartScalar_source_eq_endpointFiberGram_add_sourceCompressionRemainder
      f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
