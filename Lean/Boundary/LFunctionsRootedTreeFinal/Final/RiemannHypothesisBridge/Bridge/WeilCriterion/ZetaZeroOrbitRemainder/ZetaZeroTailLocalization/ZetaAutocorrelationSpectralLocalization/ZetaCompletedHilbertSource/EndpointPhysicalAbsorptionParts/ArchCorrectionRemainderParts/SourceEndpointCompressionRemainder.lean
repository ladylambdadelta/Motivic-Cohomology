import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.SourceEndpointSchurProjection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompressionSource

/-!
# Source endpoint compression remainder

This file owns nonnegativity of the concrete canonical endpoint compression
remainder.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source finite Schur domination of the two endpoint evaluations by the
centered archimedean and correction packet Grams, after projection-complement
nonnegativity has been supplied. -/
theorem completedEndpointPhiNorms_le_centeredPacketGrams_source_forCompression_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
  fun hcomplement =>
    completedEndpointPhiNorms_le_centeredPacketGrams_sourceSchurProjection_of_projectionComplement
      f hcomplement

/-- The endpoint trace-fiber Gram unfolds to the two endpoint evaluation
norm-squares, in the source compression lane. -/
theorem completedEndpointTraceFiber_gram_eq_endpointPhiNorms_source_forCompression
    (f : ZetaAdmissibleFunction) :
    (completedWeilEndpointTraceFiber f).gram =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
  completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add f

/-- Source centered-packet domination of the endpoint trace fiber Gram, after
projection-complement nonnegativity has been supplied. -/
theorem completedEndpointTraceFiber_gram_le_centeredPacketGrams_source_forCompression_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
      ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
  fun hcomplement =>
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          ZetaHermitianPacketEnsemble.coordinateGram
              (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
            ZetaHermitianPacketEnsemble.coordinateGram
              ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
                zetaCompletedExplicitFormulaPhi f 0))
      (completedEndpointTraceFiber_gram_eq_endpointPhiNorms_source_forCompression
        f).symm
      (completedEndpointPhiNorms_le_centeredPacketGrams_source_forCompression_of_projectionComplement
        f hcomplement)

/-- The centered archimedean and correction packet Grams are the Hilbert-source
archimedean and correction packet Grams. -/
theorem completedEndpointCenteredPacketGrams_eq_archCorrectionPacketGrams_source_forCompression
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  let harch :
      ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    congrArg
      (fun value : ℝ =>
        value +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0))
      (zetaCompletedHermitianBoundaryDefect_archimedeanPacketGram_eq_centeredAmplitudeGram
        f).symm
  let hcorrection :
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    congrArg
      (fun value : ℝ =>
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          value)
      (zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_centeredPolePhiNormSq
        f).symm
  Eq.trans harch hcorrection

/-- Source endpoint trace-fiber domination by the centered archimedean and
correction packet Grams, after projection-complement nonnegativity has been
supplied. -/
theorem completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_source_forCompression_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) +
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) :=
  fun hcomplement =>
    Eq.subst
      (motive := fun value : ℝ =>
        (completedWeilEndpointTraceFiber f).gram ≤ value)
      (completedEndpointCenteredPacketGrams_eq_archCorrectionPacketGrams_source_forCompression
        f)
      (completedEndpointTraceFiber_gram_le_centeredPacketGrams_source_forCompression_of_projectionComplement
        f hcomplement)

/-- Source nonnegativity of the endpoint archimedean/correction absorption
remainder, after projection-complement nonnegativity has been supplied. -/
theorem completedEndpointFiberArchCorrectionRemainder_nonnegative_source_forCompression_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
  fun hcomplement =>
    completedEndpointFiberArchCorrectionRemainder_nonnegative_of_endpointFiberGram_le_arch_add_correction
      f
      (completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_source_forCompression_of_projectionComplement
        f hcomplement)

/-- Source nonnegativity of the endpoint positive-presentation compression
remainder, after projection-complement nonnegativity has been supplied. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_source_forCompression_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  fun hcomplement =>
    completedEndpointFiberPositivePresentationRemainder_nonnegative_of_archCorrectionRemainder
      f
      (completedEndpointFiberArchCorrectionRemainder_nonnegative_source_forCompression_of_projectionComplement
        f hcomplement)

/-- Source domination of the Weil endpoint trace fiber by the completed
positive GNS presentation, after projection-complement nonnegativity has been
supplied. -/
theorem completedWeilEndpointTraceFiber_gram_le_positivePresentation_source_primitive_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
    endpointFiberGram_le_positivePresentation_of_positivePresentationRemainder_nonnegative
      f
      (completedEndpointFiberPositivePresentationRemainder_nonnegative_source_forCompression_of_projectionComplement
        f hcomplement)

/-- Source domination of the canonical endpoint trace fiber by the completed
positive GNS presentation, after projection-complement nonnegativity has been
supplied. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_positivePresentation_source_primitive_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
  let sourceGram : ℝ :=
    (completedBoundaryHilbertSourceEndpointTraceFiber
      (completedBoundaryHilbertSource f)).gram
  let seedGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  let positiveScalar : ℝ :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar f
  let hseed :
      sourceGram = seedGram :=
    completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f
  let hpositive :
      seedGram ≤ positiveScalar :=
    completedWeilEndpointTraceFiber_gram_le_positivePresentation_source_primitive_of_projectionComplement
      f hcomplement
  Eq.subst
    (motive := fun value : ℝ => value ≤ positiveScalar)
    hseed.symm
    hpositive

/-- The completed positive GNS presentation is the ordered-heart scalar of
the canonical completed boundary Hilbert source. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_orderedHeart_source_primitive
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  let hgns :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        completedBoundaryHermitianGNSScalar
          (completedBoundaryHilbertSource f) :=
    (completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar
      f).symm
  let hordered :
      completedBoundaryHermitianGNSScalar
          (completedBoundaryHilbertSource f) =
        completedOrderedHeartScalar
          (completedBoundaryHilbertSource f) :=
    Eq.refl
      (completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f))
  Eq.trans hgns hordered

/-- Source domination of the canonical endpoint trace fiber by the completed
ordered-heart scalar, after projection-complement nonnegativity has been
supplied. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_source_primitive_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  fun hcomplement =>
  let hpositive :
      (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
    completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_positivePresentation_source_primitive_of_projectionComplement
      f hcomplement
  let hordered :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_orderedHeart_source_primitive
      f
  Eq.subst
    (motive := fun value : ℝ =>
      (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤ value)
    hordered
    hpositive

/-- Finite-Bessel nonnegativity of the concrete canonical endpoint compression
remainder after physical-boundary-to-ordered-heart transport. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_source_nonnegative_primitive_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    0 ≤
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_traceCompression_of_finiteBessel
    f D hnonPrime boundary_eq_ordered

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
