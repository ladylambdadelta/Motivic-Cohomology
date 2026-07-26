import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainder

/-!
# Source endpoint Schur projection

This file owns the finite endpoint Schur projection estimate used by the
endpoint compression assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two endpoint evaluation norm-squares used by the finite Schur
projection. -/
noncomputable def completedEndpointSchurEndpointNormSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.normSq
      (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
    Complex.normSq
      (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))

/-- The centered archimedean/correction packet Gram sum used by the finite
Schur projection. -/
noncomputable def completedEndpointSchurPacketGramSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)

/-- The finite endpoint Schur remainder. -/
noncomputable def completedEndpointSchurRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedEndpointSchurPacketGramSum f -
    completedEndpointSchurEndpointNormSum f

/-- The centered endpoint Schur control scalar. -/
noncomputable def completedEndpointSchurCenteredControl
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedEndpointSchurPacketGramSum f

/-- The endpoint Schur endpoint norm sum unfolds to the two endpoint
evaluation norm-squares. -/
theorem completedEndpointSchurEndpointNormSum_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointSchurEndpointNormSum f =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
  Eq.refl (completedEndpointSchurEndpointNormSum f)

/-- The endpoint Schur packet Gram sum unfolds to the centered
archimedean/correction packet Grams. -/
theorem completedEndpointSchurPacketGramSum_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointSchurPacketGramSum f =
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
  Eq.refl (completedEndpointSchurPacketGramSum f)

/-- The endpoint Schur remainder unfolds to packet Gram sum minus endpoint
norm sum. -/
theorem completedEndpointSchurRemainder_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointSchurRemainder f =
      completedEndpointSchurPacketGramSum f -
        completedEndpointSchurEndpointNormSum f :=
  Eq.refl (completedEndpointSchurRemainder f)

/-- The centered endpoint Schur control unfolds to the packet Gram sum. -/
theorem completedEndpointSchurCenteredControl_eq_packetGramSum
    (f : ZetaAdmissibleFunction) :
    completedEndpointSchurCenteredControl f =
      completedEndpointSchurPacketGramSum f :=
  Eq.refl (completedEndpointSchurCenteredControl f)

/-- The finite endpoint Schur remainder is the archimedean/correction
endpoint residual in centered coordinates. -/
theorem completedEndpointSchurRemainder_eq_archCorrectionRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointSchurRemainder f =
      completedEndpointFiberArchCorrectionRemainder f :=
  (completedEndpointFiberArchCorrectionRemainder_eq_centeredPacketGrams_sub_endpointPhiNorms
    f).symm

/-- Source endpoint trace-fiber domination by the centered archimedean and
correction packet Grams, after projection-complement nonnegativity has been
supplied. -/
theorem completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  fun hcomplement =>
    completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_source_owner_of_projectionComplement
      f hcomplement

/-- Source nonnegativity of the endpoint archimedean/correction Schur
residual in centered coordinates, after projection-complement nonnegativity has
been supplied. -/
theorem completedEndpointFiberArchCorrectionRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
  fun hcomplement =>
    completedEndpointFiberArchCorrectionRemainder_nonnegative_of_endpointFiberGram_le_arch_add_correction
      f
      (completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_sourceSchurProjection_of_projectionComplement
        f hcomplement)

/-- Source nonnegativity of the finite endpoint Schur remainder, after
projection-complement nonnegativity has been supplied. -/
theorem completedEndpointSchurRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointSchurRemainder f :=
  fun hcomplement =>
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointSchurRemainder_eq_archCorrectionRemainder f).symm
      (completedEndpointFiberArchCorrectionRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
        f hcomplement)

/-- Source analytic endpoint control: the two endpoint fibers are dominated by
the centered Schur control, after projection-complement nonnegativity has been
supplied. -/
theorem completedEndpointSchurEndpointNormSum_le_centeredControl_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    completedEndpointSchurEndpointNormSum f ≤
      completedEndpointSchurCenteredControl f :=
  fun hcomplement =>
  let hsub :
      0 ≤
        completedEndpointSchurPacketGramSum f -
          completedEndpointSchurEndpointNormSum f :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointSchurRemainder_eq f)
      (completedEndpointSchurRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
        f hcomplement)
  let hpacket :
      completedEndpointSchurEndpointNormSum f ≤
        completedEndpointSchurPacketGramSum f :=
    sub_nonneg.mp hsub
  Eq.subst
    (motive := fun value : ℝ =>
      completedEndpointSchurEndpointNormSum f ≤ value)
    (completedEndpointSchurCenteredControl_eq_packetGramSum f).symm
    hpacket

/-- Source finite Schur domination in named endpoint Schur coordinates, after
projection-complement nonnegativity has been supplied. -/
theorem completedEndpointSchurEndpointNormSum_le_packetGramSum_sourceSchurProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    completedEndpointSchurEndpointNormSum f ≤
      completedEndpointSchurPacketGramSum f :=
  fun hcomplement =>
  let hnonnegative :
      0 ≤
        completedEndpointSchurPacketGramSum f -
          completedEndpointSchurEndpointNormSum f :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedEndpointSchurRemainder_eq f)
      (completedEndpointSchurRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
        f hcomplement)
  sub_nonneg.mp hnonnegative

/-- Source finite Schur domination of the two endpoint evaluations by the
centered archimedean and correction packet Grams, after projection-complement
nonnegativity has been supplied. -/
theorem completedEndpointPhiNorms_le_centeredPacketGrams_sourceSchurProjection_of_projectionComplement
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
    Eq.subst
      (motive := fun leftValue : ℝ =>
        leftValue ≤
          ZetaHermitianPacketEnsemble.coordinateGram
              (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
            ZetaHermitianPacketEnsemble.coordinateGram
              ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
                zetaCompletedExplicitFormulaPhi f 0))
      (completedEndpointSchurEndpointNormSum_eq f)
      (Eq.subst
        (motive := fun rightValue : ℝ =>
          completedEndpointSchurEndpointNormSum f ≤ rightValue)
        (completedEndpointSchurPacketGramSum_eq f)
        (completedEndpointSchurEndpointNormSum_le_packetGramSum_sourceSchurProjection_of_projectionComplement
          f hcomplement))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
