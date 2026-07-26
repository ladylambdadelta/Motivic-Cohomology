import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointSchurPrimitive

/-!
# Direct centered endpoint Schur source

This file owns the acyclic centered endpoint Schur estimate used by endpoint
physical absorption.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The direct centered endpoint Schur remainder in visible coordinates. -/
noncomputable def completedEndpointCenteredSchurRemainder_directCentered
    (f : ZetaAdmissibleFunction) : ℝ :=
  (ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)) -
    (Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)))

/-- The direct centered endpoint Schur remainder unfolds to centered packet
Gram minus endpoint norm-square sum. -/
theorem completedEndpointCenteredSchurRemainder_directCentered_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointCenteredSchurRemainder_directCentered f =
      (ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0)) -
        (Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))) :=
  Eq.refl (completedEndpointCenteredSchurRemainder_directCentered f)

/-- Centered endpoint Schur-remainder nonnegativity transported from the
primitive centered endpoint Schur domination, after projection-complement
nonnegativity has been supplied. -/
theorem completedEndpointCenteredSchurRemainder_nonnegative_directCentered_source_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointCenteredSchurRemainder_directCentered f :=
  fun hcomplement =>
  let endpoint : ℝ :=
    Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
      Complex.normSq
        (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))
  let centered : ℝ :=
    ZetaHermitianPacketEnsemble.coordinateGram
        (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
      ZetaHermitianPacketEnsemble.coordinateGram
        ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
          zetaCompletedExplicitFormulaPhi f 0)
  let hendpointCentered : endpoint ≤ centered :=
    completedEndpointPhiNorms_le_centeredPacketGrams_centeredEndpointSchurPrimitive_of_projectionComplement
      f hcomplement
  let hsub : 0 ≤ centered - endpoint :=
    sub_nonneg.mpr hendpointCentered
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointCenteredSchurRemainder_directCentered_eq f).symm
    hsub

/-- Direct centered endpoint Schur domination in visible coordinates, after
projection-complement nonnegativity has been supplied.

This is the narrow source theorem: the two endpoint evaluations are a Schur
compression of the centered archimedean/correction coordinates. -/
theorem completedEndpointPhiNorms_le_centeredPacketGrams_directCentered_source_of_projectionComplement
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
  let hremainder :
      0 ≤
        (ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0)) -
          (Complex.normSq
              (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
            Complex.normSq
              (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))) :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointCenteredSchurRemainder_directCentered_eq f)
      (completedEndpointCenteredSchurRemainder_nonnegative_directCentered_source_of_projectionComplement
        f hcomplement)
  sub_nonneg.mp hremainder

/-- The centered packet Gram coordinates are the archimedean and correction
packet Grams of the completed Hermitian boundary defect. -/
theorem completedEndpointCenteredPacketGrams_eq_archCorrectionPacketGrams_directCentered_source
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

/-- Direct centered endpoint Schur domination transported to the
archimedean/correction packet Grams, after projection-complement nonnegativity
has been supplied. -/
theorem completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_directCentered_source_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  fun hcomplement =>
  let hendpoint :
      (completedWeilEndpointTraceFiber f).gram =
        Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
    completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add f
  let hcentered :
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    completedEndpointPhiNorms_le_centeredPacketGrams_directCentered_source_of_projectionComplement
      f hcomplement
  let hfiberCentered :
      (completedWeilEndpointTraceFiber f).gram ≤
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          ZetaHermitianPacketEnsemble.coordinateGram
              (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
            ZetaHermitianPacketEnsemble.coordinateGram
              ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
                zetaCompletedExplicitFormulaPhi f 0))
      hendpoint.symm
      hcentered
  Eq.subst
    (motive := fun value : ℝ =>
      (completedWeilEndpointTraceFiber f).gram ≤ value)
    (completedEndpointCenteredPacketGrams_eq_archCorrectionPacketGrams_directCentered_source
      f)
    hfiberCentered

/-- Collapse of the positive GNS presentation to the centered
archimedean/correction packet when the completed prime positive channel
vanishes. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_archCorrectionPacketGrams_directCentered_source
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

/-- Direct centered endpoint Schur domination transported to the completed
positive GNS presentation, after projection-complement nonnegativity has been
supplied. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_directCentered_source_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
  let hcentered :
      (completedWeilEndpointTraceFiber f).gram ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_directCentered_source_of_projectionComplement
      f hcomplement
  let hprime :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  let hpresentation :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_archCorrectionPacketGrams_directCentered_source
      f hprime
  Eq.subst
    (motive := fun value : ℝ =>
      (completedWeilEndpointTraceFiber f).gram ≤ value)
    hpresentation.symm
    hcentered

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
