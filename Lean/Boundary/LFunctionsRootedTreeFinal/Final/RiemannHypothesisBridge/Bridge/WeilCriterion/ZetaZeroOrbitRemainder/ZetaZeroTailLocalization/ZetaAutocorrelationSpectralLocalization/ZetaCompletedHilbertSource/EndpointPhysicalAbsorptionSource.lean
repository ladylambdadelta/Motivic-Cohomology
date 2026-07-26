import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionPrimitive
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceReconstruction

/-!
# Endpoint physical absorption source

This file owns the analytic endpoint absorption input: after the endpoint
diagonal fibers are removed from the physical completed boundary trace, the
remaining trace kernel is nonnegative.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two endpoint evaluation norm-squares as one named scalar. -/
noncomputable def completedEndpointPhiNormSquareSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.normSq
      (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
    Complex.normSq
      (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))

/-- The centered archimedean and correction packet Gram sum. -/
noncomputable def completedEndpointCenteredPacketGramSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)

/-- The named endpoint norm-square sum unfolds to the two endpoint
evaluations. -/
theorem completedEndpointPhiNormSquareSum_eq_endpointPhiNorms
    (f : ZetaAdmissibleFunction) :
    completedEndpointPhiNormSquareSum f =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
  Eq.refl (completedEndpointPhiNormSquareSum f)

/-- The named centered packet Gram sum unfolds to the centered archimedean and
correction Grams. -/
theorem completedEndpointCenteredPacketGramSum_eq_centeredPacketGrams
    (f : ZetaAdmissibleFunction) :
    completedEndpointCenteredPacketGramSum f =
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
  Eq.refl (completedEndpointCenteredPacketGramSum f)

/-- Centered-packet domination of the two completed endpoint evaluations. -/
def CompletedEndpointCenteredPacketDomination
    (f : ZetaAdmissibleFunction) : Prop :=
  completedEndpointPhiNormSquareSum f ≤
    completedEndpointCenteredPacketGramSum f

/-- The finite centered endpoint Schur remainder: centered packet Gram minus
the two endpoint evaluation norm-squares. -/
noncomputable def completedEndpointCenteredPacketSchurRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedEndpointCenteredPacketGramSum f -
    completedEndpointPhiNormSquareSum f

/-- The centered endpoint Schur remainder unfolds to packet Gram minus
endpoint norm-square sum. -/
theorem completedEndpointCenteredPacketSchurRemainder_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointCenteredPacketSchurRemainder f =
      completedEndpointCenteredPacketGramSum f -
        completedEndpointPhiNormSquareSum f :=
  Eq.refl (completedEndpointCenteredPacketSchurRemainder f)

/-- The prime boundary comparison used by source endpoint physical
absorption. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_sourcePhysicalAbsorption
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f :=
  primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_sourcePhysicalPrimitive
    f D

/-- Source nonnegativity of the endpoint trace-reconstruction remainder. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_sourcePhysicalAbsorption
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointTraceRemainder f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeilEndpointTraceRemainder_eq_absorbedPhysicalScalar f).symm
    (completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_sourcePhysicalPrimitive
      f D hnonPrime)

/-- Source physical endpoint absorption: after removing the completed endpoint
diagonal squares, the physical boundary trace remainder is nonnegative. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_sourcePhysicalPrimitive
    f D hnonPrime

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
