import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointProjection

/-!
# Centered endpoint Schur primitive

This file owns the centered endpoint Schur domination used before finite
endpoint Bessel compression is assembled.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Primitive centered endpoint Schur domination, after the endpoint projection
complement has been proved nonnegative. -/
theorem completedEndpointPhiNorms_le_centeredPacketGrams_centeredEndpointSchurPrimitive_of_projectionComplement
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
  let hfiber :
      (completedWeilEndpointTraceFiber f).gram ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_centeredProjection_of_projectionComplement
      f hcomplement
  let hendpoint :
      (completedWeilEndpointTraceFiber f).gram =
        Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
    completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add f
  let harchCoordinate :
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) :=
    zetaCompletedHermitianBoundaryDefect_archimedeanPacketGram_eq_centeredAmplitudeGram
      f
  let hcorrectionCoordinate :
      ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_centeredPolePhiNormSq
      f
  let harch :
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    congrArg₂ HAdd.hAdd harchCoordinate hcorrectionCoordinate
  let hendpointArch :
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f) +
            ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f))
      hendpoint
      hfiber
  Eq.subst
    (motive := fun value : ℝ =>
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤ value)
    harch
    hendpointArch

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
