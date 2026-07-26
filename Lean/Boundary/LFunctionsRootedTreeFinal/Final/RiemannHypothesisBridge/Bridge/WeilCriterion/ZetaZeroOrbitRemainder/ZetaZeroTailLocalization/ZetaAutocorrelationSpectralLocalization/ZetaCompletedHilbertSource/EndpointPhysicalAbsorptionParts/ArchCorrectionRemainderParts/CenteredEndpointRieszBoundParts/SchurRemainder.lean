import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBoundParts.SourceKernelSplit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionSource

/-!
# Centered endpoint Riesz Schur remainder

This file owns the Schur-remainder form of the centered two-endpoint Riesz
bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The two completed endpoint evaluations as a finite vector. -/
noncomputable def completedCenteredEndpointRieszEvaluationVector
    (f : ZetaAdmissibleFunction) : ℂ × ℂ :=
  (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)),
    zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))

/-- The squared Euclidean norm of the two completed endpoint evaluations. -/
noncomputable def completedCenteredEndpointRieszEvaluationNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.normSq (completedCenteredEndpointRieszEvaluationVector f).1 +
    Complex.normSq (completedCenteredEndpointRieszEvaluationVector f).2

/-- The centered packet energy controlling the two endpoint evaluations. -/
noncomputable def completedCenteredEndpointRieszControlNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) +
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)

/-- The centered endpoint Riesz Schur remainder. -/
noncomputable def completedCenteredEndpointRieszSchurRemainder
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedCenteredEndpointRieszControlNormSq f -
    completedCenteredEndpointRieszEvaluationNormSq f

/-- The endpoint Riesz evaluation norm unfolds to the two endpoint Phi
squares. -/
theorem completedCenteredEndpointRieszEvaluationNormSq_eq_endpointPhiNorms
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointRieszEvaluationNormSq f =
      Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq
          (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) := by
  rfl

/-- The centered endpoint Riesz control norm unfolds to the
archimedean/correction packet Gram sum. -/
theorem completedCenteredEndpointRieszControlNormSq_eq_archCorrectionPacketGrams
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointRieszControlNormSq f =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  rfl

/-- The centered endpoint Riesz Schur remainder unfolds to control minus
evaluation. -/
theorem completedCenteredEndpointRieszSchurRemainder_eq_control_sub_evaluation
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointRieszSchurRemainder f =
      completedCenteredEndpointRieszControlNormSq f -
        completedCenteredEndpointRieszEvaluationNormSq f := by
  rfl

/-- The centered endpoint Riesz Schur remainder is the
archimedean/correction endpoint residual. -/
theorem completedCenteredEndpointRieszSchurRemainder_eq_archCorrectionRemainder
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointRieszSchurRemainder f =
      completedEndpointFiberArchCorrectionRemainder f := by
  have hschur :
      completedCenteredEndpointRieszSchurRemainder f =
        completedCenteredEndpointRieszControlNormSq f -
          completedCenteredEndpointRieszEvaluationNormSq f :=
    completedCenteredEndpointRieszSchurRemainder_eq_control_sub_evaluation f
  have hcontrol :
      completedCenteredEndpointRieszControlNormSq f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedCenteredEndpointRieszControlNormSq_eq_archCorrectionPacketGrams f
  have hevaluation :
      completedCenteredEndpointRieszEvaluationNormSq f =
        (completedWeilEndpointTraceFiber f).gram := by
    have hleft :
        completedCenteredEndpointRieszEvaluationNormSq f =
          Complex.normSq
              (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
            Complex.normSq
              (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
      completedCenteredEndpointRieszEvaluationNormSq_eq_endpointPhiNorms f
    have hright :
        (completedWeilEndpointTraceFiber f).gram =
          Complex.normSq
              (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
            Complex.normSq
              (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
      completedWeilEndpointTraceFiber_gram_eq_endpointPhi_normSq_add f
    exact hleft.trans hright.symm
  have hconcrete :
      completedCenteredEndpointRieszControlNormSq f -
          completedCenteredEndpointRieszEvaluationNormSq f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) -
          (completedWeilEndpointTraceFiber f).gram :=
    congrArg₂ HSub.hSub hcontrol hevaluation
  have hresidual :
      completedEndpointFiberArchCorrectionRemainder f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) -
          (completedWeilEndpointTraceFiber f).gram :=
    completedEndpointFiberArchCorrectionRemainder_eq_arch_add_correction_sub_endpointFiberGram
      f
  exact hschur.trans (hconcrete.trans hresidual.symm)

/-- Analytic source nonnegativity of the endpoint trace remainder. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_centeredRiesz_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointTraceRemainder f :=
  completedWeilEndpointTraceRemainder_nonnegative_sourcePhysicalAbsorption
    f D hnonPrime

/-- Analytic source nonnegativity of the endpoint trace remainder after the
non-prime residual is supplied by the source residual theorem and
projection-complement nonnegativity. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_centeredRiesz_source_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedWeilEndpointTraceRemainder f :=
  fun hcomplement =>
  let hpositive :
      0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
    completedEndpointFiberPositivePresentationRemainder_nonnegative_sourceKernelSplit_of_projectionComplement
      f hcomplement
  let hsplit :
      completedEndpointFiberPositivePresentationRemainder f =
        completedPrimeDefectKernelPositiveChannel f +
          completedEndpointFiberArchCorrectionRemainder f :=
    completedEndpointFiberPositivePresentationRemainder_eq_primePositive_add_archCorrectionRemainder
      f
  let hprime :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  let hcollapse :
      completedPrimeDefectKernelPositiveChannel f +
          completedEndpointFiberArchCorrectionRemainder f =
        completedEndpointFiberArchCorrectionRemainder f :=
    Eq.trans
      (congrArg
        (fun value : ℝ =>
          value + completedEndpointFiberArchCorrectionRemainder f)
        hprime)
      (zero_add (completedEndpointFiberArchCorrectionRemainder f))
  let hpositiveArch :
      completedEndpointFiberPositivePresentationRemainder f =
        completedEndpointFiberArchCorrectionRemainder f :=
    hsplit.trans hcollapse
  let harch :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      hpositiveArch
      hpositive
  let hnonPrime :
      CompletedEndpointNonPrimeTraceResidualNonnegative f :=
    completedEndpointNonPrimeTraceResidualNonnegative_of_archCorrectionRemainder_nonnegative
      f harch
  completedWeilEndpointTraceRemainder_nonnegative_centeredRiesz_source
    f D hnonPrime

/-- Analytic source nonnegativity of the absorbed physical endpoint scalar. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_centeredRiesz_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceRemainder
    f
    (completedWeilEndpointTraceRemainder_nonnegative_centeredRiesz_source
      f D hnonPrime)

/-- Analytic source nonnegativity of the absorbed physical endpoint scalar after
the non-prime residual is supplied by the source residual theorem and
projection-complement nonnegativity. -/
theorem completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_centeredRiesz_source_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedWeilEndpointAbsorbedPhysicalScalar f :=
  fun hcomplement =>
    completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_of_traceRemainder
      f
      (completedWeilEndpointTraceRemainder_nonnegative_centeredRiesz_source_owner_of_projectionComplement
        f D hcomplement)

/-- Projection-complement nonnegativity gives domination of the endpoint trace
fiber by the positive GNS presentation. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  fun hcomplement =>
    completedEndpointTraceFiber_gram_le_positivePresentation_sourceKernelSplit_of_projectionComplement
      f hcomplement

/-- Projection-complement nonnegativity gives nonnegativity of the endpoint
positive-presentation compression remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  fun hcomplement =>
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
      f).mpr
      (completedEndpointTraceFiber_gram_le_positivePresentation_centeredRiesz_of_projectionComplement
        f hcomplement)

/-- The completed positive-presentation compression remainder equals the
archimedean/correction Riesz residual. -/
theorem completedEndpointFiberPositivePresentationRemainder_eq_archCorrectionRemainder_centeredRiesz
    (f : ZetaAdmissibleFunction) :
    completedEndpointFiberPositivePresentationRemainder f =
      completedEndpointFiberArchCorrectionRemainder f := by
  have hsplit :
      completedEndpointFiberPositivePresentationRemainder f =
        completedPrimeDefectKernelPositiveChannel f +
          completedEndpointFiberArchCorrectionRemainder f :=
    completedEndpointFiberPositivePresentationRemainder_eq_primePositive_add_archCorrectionRemainder
      f
  have hprime :
      completedPrimeDefectKernelPositiveChannel f = 0 :=
    completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f
  have hcollapse :
      completedPrimeDefectKernelPositiveChannel f +
          completedEndpointFiberArchCorrectionRemainder f =
        completedEndpointFiberArchCorrectionRemainder f :=
    Eq.trans
      (congrArg
        (fun value : ℝ =>
          value + completedEndpointFiberArchCorrectionRemainder f)
        hprime)
      (zero_add (completedEndpointFiberArchCorrectionRemainder f))
  exact hsplit.trans hcollapse

/-- Projection-complement nonnegativity gives nonnegativity of the endpoint
archimedean/correction Riesz residual. -/
theorem completedEndpointFiberArchCorrectionRemainder_nonnegative_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
  fun hcomplement =>
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointFiberPositivePresentationRemainder_eq_archCorrectionRemainder_centeredRiesz
      f)
    (completedEndpointFiberPositivePresentationRemainder_nonnegative_centeredRiesz_of_projectionComplement
      f hcomplement)

/-- Projection-complement nonnegativity gives nonnegativity of the centered
endpoint Riesz Schur remainder. -/
theorem completedCenteredEndpointRieszSchurRemainder_nonnegative_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedCenteredEndpointRieszSchurRemainder f :=
  fun hcomplement =>
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedCenteredEndpointRieszSchurRemainder_eq_archCorrectionRemainder
      f).symm
    (completedEndpointFiberArchCorrectionRemainder_nonnegative_centeredRiesz_of_projectionComplement
      f hcomplement)

/-- Schur-remainder nonnegativity gives the centered two-endpoint Riesz
domination. -/
theorem completedCenteredEndpointRieszEvaluationNormSq_le_controlNormSq_of_schurRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (hschur : 0 ≤ completedCenteredEndpointRieszSchurRemainder f) :
    completedCenteredEndpointRieszEvaluationNormSq f ≤
      completedCenteredEndpointRieszControlNormSq f := by
  have hsub :
      0 ≤
        completedCenteredEndpointRieszControlNormSq f -
          completedCenteredEndpointRieszEvaluationNormSq f :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedCenteredEndpointRieszSchurRemainder_eq_control_sub_evaluation
        f)
      hschur
  exact sub_nonneg.mp hsub

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
