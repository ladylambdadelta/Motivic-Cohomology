import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBoundParts.SchurRemainder

/-!
# Centered endpoint Riesz bound

This file owns the analytic two-endpoint Riesz bound for the completed
Paley-Wiener evaluation map.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two completed endpoint evaluations as a finite vector. -/
noncomputable def completedCenteredEndpointEvaluationVector
    (f : ZetaAdmissibleFunction) : ℂ × ℂ :=
  completedCenteredEndpointRieszEvaluationVector f

/-- The squared Euclidean norm of the two completed endpoint evaluations. -/
noncomputable def completedCenteredEndpointEvaluationNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedCenteredEndpointRieszEvaluationNormSq f

/-- The centered packet energy controlling the two endpoint evaluations. -/
noncomputable def completedCenteredEndpointControlNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedCenteredEndpointRieszControlNormSq f

/-- The endpoint evaluation norm unfolds to the two endpoint Phi squares. -/
theorem completedCenteredEndpointEvaluationNormSq_eq_endpointPhiNorms
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointEvaluationNormSq f =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) := by
  exact completedCenteredEndpointRieszEvaluationNormSq_eq_endpointPhiNorms f

/-- The centered endpoint control norm unfolds to the archimedean/correction
packet Gram sum. -/
theorem completedCenteredEndpointControlNormSq_eq_archCorrectionPacketGrams
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointControlNormSq f =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  exact completedCenteredEndpointRieszControlNormSq_eq_archCorrectionPacketGrams f

/-- Projection-complement nonnegativity gives the analytic Riesz bound for the
completed two-endpoint evaluation map. -/
theorem completedCenteredEndpointEvaluationNormSq_le_controlNormSq_riesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    completedCenteredEndpointEvaluationNormSq f ≤
      completedCenteredEndpointControlNormSq f :=
  fun hcomplement =>
    completedCenteredEndpointRieszEvaluationNormSq_le_controlNormSq_of_schurRemainder_nonnegative
      f
      (completedCenteredEndpointRieszSchurRemainder_nonnegative_of_projectionComplement
        f hcomplement)

/-- Projection-complement nonnegativity gives the analytic Riesz bound in
endpoint-fiber Gram coordinates. -/
theorem completedWeilEndpointTraceFiber_gram_le_controlNormSq_riesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      completedCenteredEndpointControlNormSq f :=
  fun hcomplement =>
  let hfiber :
      (completedWeilEndpointTraceFiber f).gram =
        completedCenteredEndpointEvaluationNormSq f :=
    completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add f
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ completedCenteredEndpointControlNormSq f)
    hfiber.symm
    (completedCenteredEndpointEvaluationNormSq_le_controlNormSq_riesz_of_projectionComplement
      f hcomplement)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
