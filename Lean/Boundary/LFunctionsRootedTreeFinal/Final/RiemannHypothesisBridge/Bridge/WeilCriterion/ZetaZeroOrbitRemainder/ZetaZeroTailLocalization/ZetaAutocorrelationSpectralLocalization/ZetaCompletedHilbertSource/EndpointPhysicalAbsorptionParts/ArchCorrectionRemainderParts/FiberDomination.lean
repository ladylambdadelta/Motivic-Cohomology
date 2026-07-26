import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointSchurPrimitive

/-!
# Endpoint fiber domination source

This file owns the finite endpoint-fiber domination input by the centered
archimedean and correction packet Grams.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- When the completed prime positive channel vanishes, the positive GNS
presentation collapses to the archimedean and correction packet Grams. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_archCorrectionPacketGrams_source_primitive
    (f : ZetaAdmissibleFunction)
    (hprime :
      completedPrimeDefectKernelPositiveChannel f = 0) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  let H : ZetaHermitianPacketEnsemble :=
    zetaCompletedHermitianBoundaryDefect f
  let P : ℝ := completedPrimeDefectKernelPositiveChannel f
  let A : ℝ := ZetaHermitianPacketEnsemble.archimedeanPacketGram H
  let C : ℝ := ZetaHermitianPacketEnsemble.correctionPacketGram H
  let hscalar :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        P + A + C :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
      f
  let hP : P = 0 := hprime
  let hzero :
        P + A + C = 0 + A + C :=
      congrArg (fun value : ℝ => value + A + C) hP
  let hzeroAdd :
        0 + A + C = A + C :=
      congrArg (fun value : ℝ => value + C) (zero_add A)
  let hcollapse :
      P + A + C = A + C :=
    Eq.trans hzero hzeroAdd
  let htarget :
      A + C =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    Eq.refl (A + C)
  Eq.trans hscalar (Eq.trans hcollapse htarget)

/-- The centered packet Gram coordinates are the archimedean and correction
packet Grams of the completed Hermitian boundary defect. -/
theorem completedEndpointCenteredPacketGrams_eq_archCorrectionPacketGrams_source_primitive
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

/-- Source finite endpoint Bessel domination in explicit centered packet
coordinates, after projection-complement nonnegativity has been supplied. -/
theorem completedEndpointPhiNorms_le_centeredPacketGrams_source_primitive_of_projectionComplement
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
    completedEndpointPhiNorms_le_centeredPacketGrams_centeredEndpointSchurPrimitive_of_projectionComplement
      f hcomplement

/-- Projection-complement nonnegativity gives endpoint trace-fiber domination
by the centered archimedean and correction packet Grams. -/
theorem completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_source_primitive_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  fun hcomplement =>
    completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_centeredProjection_of_projectionComplement
      f hcomplement

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
