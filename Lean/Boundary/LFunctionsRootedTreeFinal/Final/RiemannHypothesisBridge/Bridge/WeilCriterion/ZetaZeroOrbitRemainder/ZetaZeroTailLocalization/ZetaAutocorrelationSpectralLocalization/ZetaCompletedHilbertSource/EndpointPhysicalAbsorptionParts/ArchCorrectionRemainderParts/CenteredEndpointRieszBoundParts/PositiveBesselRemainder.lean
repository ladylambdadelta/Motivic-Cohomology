import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBoundParts.PositiveProjectionContractive

/-!
# Centered endpoint positive Bessel remainder

This file owns the full positive endpoint Bessel Schur remainder used by the
centered endpoint Riesz lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The full positive endpoint Bessel kernel Gram. -/
noncomputable def completedEndpointPositiveBesselKernelGram_centeredRiesz
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedGNSPositiveBoundaryPresentationScalar f

/-- The full positive endpoint Bessel Schur remainder. -/
noncomputable def completedEndpointPositiveBesselSchurRemainder_centeredRiesz
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedEndpointPositiveBesselKernelGram_centeredRiesz f -
    (completedWeilEndpointTraceFiber f).gram

/-- The full positive endpoint Bessel kernel Gram unfolds to the completed
positive GNS presentation scalar. -/
theorem completedEndpointPositiveBesselKernelGram_centeredRiesz_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointPositiveBesselKernelGram_centeredRiesz f =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  rfl

/-- The full positive endpoint Bessel Schur remainder unfolds to kernel Gram
minus endpoint trace Gram. -/
theorem completedEndpointPositiveBesselSchurRemainder_centeredRiesz_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointPositiveBesselSchurRemainder_centeredRiesz f =
      completedEndpointPositiveBesselKernelGram_centeredRiesz f -
        (completedWeilEndpointTraceFiber f).gram := by
  rfl

/-- The full positive endpoint Bessel Schur remainder is the
positive-presentation endpoint compression remainder. -/
theorem completedEndpointPositiveBesselSchurRemainder_centeredRiesz_eq_positivePresentationRemainder
    (f : ZetaAdmissibleFunction) :
    completedEndpointPositiveBesselSchurRemainder_centeredRiesz f =
      completedEndpointFiberPositivePresentationRemainder f := by
  rfl

/-- Projection-complement nonnegativity gives finite-dimensional Bessel
domination of the endpoint trace fiber by the full positive endpoint Bessel
kernel Gram. -/
theorem completedWeilEndpointTraceFiber_gram_le_positiveBesselKernelGram_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      completedEndpointPositiveBesselKernelGram_centeredRiesz f :=
  fun hcomplement =>
  let hpositive :
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
    completedWeilEndpointTraceFiber_gram_le_positivePresentation_of_projectionContractive_centeredRiesz
      f
      (completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_GNSScalar_centeredRiesz_of_projectionComplement
        f hcomplement)
  Eq.subst
    (motive := fun value : ℝ =>
      (completedWeilEndpointTraceFiber f).gram ≤ value)
    (completedEndpointPositiveBesselKernelGram_centeredRiesz_eq f).symm
    hpositive

/-- Projection-complement nonnegativity gives nonnegativity of the full
positive endpoint Bessel Schur remainder. -/
theorem completedEndpointPositiveBesselSchurRemainder_nonnegative_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedEndpointPositiveBesselSchurRemainder_centeredRiesz f :=
  fun hcomplement =>
  let hsub :
      0 ≤
        completedEndpointPositiveBesselKernelGram_centeredRiesz f -
          (completedWeilEndpointTraceFiber f).gram :=
    sub_nonneg.mpr
      (completedWeilEndpointTraceFiber_gram_le_positiveBesselKernelGram_centeredRiesz_of_projectionComplement
        f hcomplement)
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointPositiveBesselSchurRemainder_centeredRiesz_eq f).symm
    hsub

/-- Source nonnegativity of the seed positive-presentation endpoint
compression remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_positiveBesselSchurRemainder_centeredRiesz
    (f : ZetaAdmissibleFunction)
    (hschur :
      0 ≤ completedEndpointPositiveBesselSchurRemainder_centeredRiesz f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedEndpointPositiveBesselSchurRemainder_centeredRiesz_eq_positivePresentationRemainder
      f)
    hschur

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
