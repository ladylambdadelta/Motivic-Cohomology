import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointSchurPrimitive

/-!
# Endpoint Riesz bound

This file owns the two-endpoint Riesz domination needed by finite
renormalized trace exhaustion.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two endpoint evaluations as one finite vector. -/
noncomputable def completedEndpointRieszEvaluationVector
    (f : ZetaAdmissibleFunction) : ℂ × ℂ :=
  (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)),
    zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))

/-- The squared norm of the two endpoint evaluations. -/
noncomputable def completedEndpointRieszEvaluationNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.normSq (completedEndpointRieszEvaluationVector f).1 +
    Complex.normSq (completedEndpointRieszEvaluationVector f).2

/-- The archimedean/correction packet control norm-square. -/
noncomputable def completedEndpointRieszControlNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)

/-- The endpoint Riesz evaluation norm unfolds to the two endpoint Phi
norm-squares. -/
theorem completedEndpointRieszEvaluationNormSq_eq_endpointPhiNorms
    (f : ZetaAdmissibleFunction) :
    completedEndpointRieszEvaluationNormSq f =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
  Eq.refl (completedEndpointRieszEvaluationNormSq f)

/-- The endpoint Riesz control norm unfolds to the archimedean/correction
packet Gram sum. -/
theorem completedEndpointRieszControlNormSq_eq_centeredPacketGrams
    (f : ZetaAdmissibleFunction) :
    completedEndpointRieszControlNormSq f =
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
  Eq.refl (completedEndpointRieszControlNormSq f)

/-- Source two-endpoint Riesz domination in endpoint/control norm form, after
projection-complement nonnegativity has been supplied. -/
theorem completedEndpointRieszEvaluationNormSq_le_controlNormSq_source_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    completedEndpointRieszEvaluationNormSq f ≤
      completedEndpointRieszControlNormSq f :=
  fun hcomplement =>
  let hconcrete :
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    completedEndpointPhiNorms_le_centeredPacketGrams_centeredEndpointSchurPrimitive_of_projectionComplement
      f hcomplement
  let hevaluation :
      completedEndpointRieszEvaluationNormSq f =
        Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
    completedEndpointRieszEvaluationNormSq_eq_endpointPhiNorms f
  let hcontrol :
      completedEndpointRieszControlNormSq f =
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    completedEndpointRieszControlNormSq_eq_centeredPacketGrams f
  Eq.subst
    (motive := fun leftValue : ℝ =>
      leftValue ≤ completedEndpointRieszControlNormSq f)
    hevaluation.symm
    (Eq.subst
      (motive := fun rightValue : ℝ =>
        Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤ rightValue)
      hcontrol.symm
      hconcrete)

/-- Source two-endpoint Riesz domination by the archimedean/correction packet
Grams, after projection-complement nonnegativity has been supplied. -/
theorem completedEndpointPhiNorms_le_centeredPacketGrams_traceExhaustion_source_of_projectionComplement
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
  let endpointNorm : ℝ := completedEndpointRieszEvaluationNormSq f
  let controlNorm : ℝ := completedEndpointRieszControlNormSq f
  let hsource : endpointNorm ≤ controlNorm :=
    completedEndpointRieszEvaluationNormSq_le_controlNormSq_source_of_projectionComplement
      f hcomplement
  let hendpoint :
      endpointNorm =
        Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
          Complex.normSq
            (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
    completedEndpointRieszEvaluationNormSq_eq_endpointPhiNorms f
  let hcontrol :
      controlNorm =
        ZetaHermitianPacketEnsemble.coordinateGram
            (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
          ZetaHermitianPacketEnsemble.coordinateGram
            ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
              zetaCompletedExplicitFormulaPhi f 0) :=
    completedEndpointRieszControlNormSq_eq_centeredPacketGrams f
  let hconcreteLeft :
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
        controlNorm :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ controlNorm)
      hendpoint
      hsource
  Eq.subst
    (motive := fun value : ℝ =>
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤ value)
    hcontrol
    hconcreteLeft

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
