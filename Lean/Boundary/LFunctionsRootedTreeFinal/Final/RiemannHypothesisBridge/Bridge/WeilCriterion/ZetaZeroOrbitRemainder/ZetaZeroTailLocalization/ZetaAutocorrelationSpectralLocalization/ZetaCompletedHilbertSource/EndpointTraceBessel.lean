import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompressionFiniteBessel

/-!
# Endpoint trace Bessel projection

This file owns the finite endpoint projection energy and its Bessel domination
by the completed ordered-heart scalar.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The endpoint projection energy of a completed Hilbert source. -/
noncomputable def completedBoundaryHilbertSourceEndpointProjectionEnergy
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  (completedBoundaryHilbertSourceEndpointTraceFiber X).gram

/-- The endpoint projection energy unfolds to the endpoint trace-fiber Gram. -/
theorem completedBoundaryHilbertSourceEndpointProjectionEnergy_eq_endpointTraceGram
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointProjectionEnergy X =
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
  Eq.refl (completedBoundaryHilbertSourceEndpointProjectionEnergy X)

/-- On canonical sources, endpoint projection energy is the seed endpoint fiber
Gram. -/
theorem completedBoundaryHilbertSourceEndpointProjectionEnergy_source_eq_endpointFiberGram
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourceEndpointProjectionEnergy
        (completedBoundaryHilbertSource f) =
      (completedWeilEndpointTraceFiber f).gram :=
  Eq.trans
    (completedBoundaryHilbertSourceEndpointProjectionEnergy_eq_endpointTraceGram
      (completedBoundaryHilbertSource f))
    (completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f)

/-- The endpoint projection complement energy of a completed Hilbert source. -/
noncomputable def completedBoundaryHilbertSourceEndpointProjectionComplementEnergy
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedOrderedHeartScalar X -
    completedBoundaryHilbertSourceEndpointProjectionEnergy X

/-- The positive kernel remainder left after removing the finite endpoint
projection energy from the completed ordered-heart scalar. -/
noncomputable def completedBoundaryHilbertSourceEndpointPositiveKernelRemainder
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedOrderedHeartScalar X -
    completedBoundaryHilbertSourceEndpointProjectionEnergy X

/-- The endpoint projection complement energy unfolds to ordered heart minus
endpoint projection energy. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_orderedHeart_sub_projectionEnergy
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointProjectionComplementEnergy X =
      completedOrderedHeartScalar X -
        completedBoundaryHilbertSourceEndpointProjectionEnergy X :=
  Eq.refl (completedBoundaryHilbertSourceEndpointProjectionComplementEnergy X)

/-- The endpoint positive-kernel remainder unfolds to ordered heart minus
endpoint projection energy. -/
theorem completedBoundaryHilbertSourceEndpointPositiveKernelRemainder_eq_orderedHeart_sub_projectionEnergy
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X =
      completedOrderedHeartScalar X -
        completedBoundaryHilbertSourceEndpointProjectionEnergy X :=
  Eq.refl (completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X)

/-- The endpoint projection complement energy is the endpoint positive-kernel
remainder. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_positiveKernelRemainder
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointProjectionComplementEnergy X =
      completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X :=
  Eq.trans
    (completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_orderedHeart_sub_projectionEnergy
      X)
    (completedBoundaryHilbertSourceEndpointPositiveKernelRemainder_eq_orderedHeart_sub_projectionEnergy
      X).symm

/-- The endpoint projection complement energy is the endpoint compression
remainder. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_compressionRemainder
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointProjectionComplementEnergy X =
      completedBoundaryHilbertSourceEndpointCompressionRemainder X :=
  let hprojection :
      completedBoundaryHilbertSourceEndpointProjectionEnergy X =
        (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
    completedBoundaryHilbertSourceEndpointProjectionEnergy_eq_endpointTraceGram X
  Eq.trans
    (completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_orderedHeart_sub_projectionEnergy
      X)
    (Eq.trans
      (congrArg
        (fun value : ℝ => completedOrderedHeartScalar X - value)
        hprojection)
      (completedBoundaryHilbertSourceEndpointCompressionRemainder_eq_orderedHeart_sub_endpointGram
        X).symm)

/-- On canonical sources, endpoint projection complement energy is the
positive-presentation endpoint compression remainder. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_source_eq_positivePresentationRemainder
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourceEndpointProjectionComplementEnergy
        (completedBoundaryHilbertSource f) =
      completedEndpointFiberPositivePresentationRemainder f :=
  Eq.trans
    (completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_compressionRemainder
      (completedBoundaryHilbertSource f))
    (completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
      f).symm

/-- Endpoint Bessel domination for a completed Hilbert source. -/
def CompletedBoundaryHilbertSourceEndpointBesselBound
    (X : CompletedBoundaryHilbertSource) : Prop :=
  completedBoundaryHilbertSourceEndpointProjectionEnergy X ≤
    completedOrderedHeartScalar X

/-- Endpoint positive-kernel split for a completed Hilbert source. -/
def CompletedBoundaryHilbertSourceEndpointPositiveKernelSplit
    (X : CompletedBoundaryHilbertSource) : Prop :=
  completedOrderedHeartScalar X =
      completedBoundaryHilbertSourceEndpointProjectionEnergy X +
        completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X ∧
    0 ≤ completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X

/-- The ordered-heart scalar splits into endpoint projection energy plus the
endpoint positive-kernel remainder. -/
theorem completedOrderedHeartScalar_eq_endpointProjectionEnergy_add_positiveKernelRemainder
    (X : CompletedBoundaryHilbertSource) :
    completedOrderedHeartScalar X =
      completedBoundaryHilbertSourceEndpointProjectionEnergy X +
        completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X :=
  let ordered : ℝ := completedOrderedHeartScalar X
  let endpointEnergy : ℝ :=
    completedBoundaryHilbertSourceEndpointProjectionEnergy X
  let hsplit :
      ordered = endpointEnergy + (ordered - endpointEnergy) :=
    endpointTraceDebt_add_sub_cancel ordered endpointEnergy
  let hkernel :
      completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X =
        ordered - endpointEnergy :=
    Eq.refl (completedBoundaryHilbertSourceEndpointPositiveKernelRemainder X)
  hsplit.trans
    (congrArg
      (fun value : ℝ => endpointEnergy + value)
      hkernel.symm)

/-- Endpoint Bessel domination gives nonnegativity of the projection complement
energy. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_nonnegative_of_besselBound
    (X : CompletedBoundaryHilbertSource)
    (hbound : CompletedBoundaryHilbertSourceEndpointBesselBound X) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplementEnergy X :=
  let hsub :
      0 ≤
        completedOrderedHeartScalar X -
          completedBoundaryHilbertSourceEndpointProjectionEnergy X :=
    sub_nonneg.mpr hbound
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_orderedHeart_sub_projectionEnergy
      X).symm
    hsub

/-- Projection complement energy and positive-kernel remainder are the same
nonnegative scalar on a canonical source. -/
theorem completedBoundaryHilbertSourceEndpointPositiveKernelRemainder_nonnegative_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤
        completedBoundaryHilbertSourceEndpointProjectionComplementEnergy
          (completedBoundaryHilbertSource f)) :
    0 ≤
      completedBoundaryHilbertSourceEndpointPositiveKernelRemainder
        (completedBoundaryHilbertSource f) :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_eq_positiveKernelRemainder
      (completedBoundaryHilbertSource f)).symm
    hcomplement

/-- Endpoint trace-fiber domination by the ordered-heart scalar gives
canonical-source endpoint projection domination by the ordered-heart scalar. -/
theorem completedBoundaryHilbertSourceEndpointProjectionEnergy_source_le_orderedHeart_of_traceFiber
    (f : ZetaAdmissibleFunction)
    (htrace :
      (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram ≤
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    completedBoundaryHilbertSourceEndpointProjectionEnergy
        (completedBoundaryHilbertSource f) ≤
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  let hprojection :
      completedBoundaryHilbertSourceEndpointProjectionEnergy
          (completedBoundaryHilbertSource f) =
        (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram :=
    completedBoundaryHilbertSourceEndpointProjectionEnergy_eq_endpointTraceGram
      (completedBoundaryHilbertSource f)
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ completedOrderedHeartScalar (completedBoundaryHilbertSource f))
    hprojection.symm
    htrace

/-- A source endpoint Bessel bound gives the source endpoint positive-kernel
split. -/
theorem completedBoundaryHilbertSourceEndpointPositiveKernelSplit_source_of_besselBound
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryHilbertSourceEndpointBesselBound
        (completedBoundaryHilbertSource f) →
      CompletedBoundaryHilbertSourceEndpointPositiveKernelSplit
        (completedBoundaryHilbertSource f) :=
  fun hbound =>
  let hsplit :
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
        completedBoundaryHilbertSourceEndpointProjectionEnergy
            (completedBoundaryHilbertSource f) +
          completedBoundaryHilbertSourceEndpointPositiveKernelRemainder
            (completedBoundaryHilbertSource f) :=
    completedOrderedHeartScalar_eq_endpointProjectionEnergy_add_positiveKernelRemainder
      (completedBoundaryHilbertSource f)
  let hcomplement :
      0 ≤
        completedBoundaryHilbertSourceEndpointProjectionComplementEnergy
          (completedBoundaryHilbertSource f) :=
    completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_nonnegative_of_besselBound
      (completedBoundaryHilbertSource f)
      hbound
  let hkernel :
      0 ≤
        completedBoundaryHilbertSourceEndpointPositiveKernelRemainder
          (completedBoundaryHilbertSource f) :=
    completedBoundaryHilbertSourceEndpointPositiveKernelRemainder_nonnegative_of_projectionComplement
      f hcomplement
  And.intro hsplit hkernel

/-- Finite Bessel plus physical-boundary-to-ordered-heart transport gives the
canonical source endpoint Bessel bound. -/
theorem completedBoundaryHilbertSourceEndpointBesselBound_source_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    CompletedBoundaryHilbertSourceEndpointBesselBound
      (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointProjectionEnergy_source_le_orderedHeart_of_traceFiber
    f
    (completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_finiteBessel
      f D hnonPrime boundary_eq_ordered)

/-- Finite Bessel plus physical-boundary-to-ordered-heart transport gives
nonnegativity of the canonical endpoint projection complement energy. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_nonnegative_source_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    0 ≤
      completedBoundaryHilbertSourceEndpointProjectionComplementEnergy
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointProjectionComplementEnergy_nonnegative_of_besselBound
    (completedBoundaryHilbertSource f)
    (completedBoundaryHilbertSourceEndpointBesselBound_source_of_finiteBessel
      f D hnonPrime boundary_eq_ordered)

/-- Finite Bessel plus physical-boundary-to-ordered-heart transport gives the
canonical source endpoint positive-kernel split. -/
theorem completedBoundaryHilbertSourceEndpointPositiveKernelSplit_source_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    CompletedBoundaryHilbertSourceEndpointPositiveKernelSplit
      (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointPositiveKernelSplit_source_of_besselBound
    f
    (completedBoundaryHilbertSourceEndpointBesselBound_source_of_finiteBessel
      f D hnonPrime boundary_eq_ordered)

/-- Finite Bessel plus physical-boundary-to-ordered-heart transport gives
nonnegativity of the canonical endpoint compression remainder. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_source_of_finiteBessel
    (f : ZetaAdmissibleFunction) :
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) →
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) →
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) →
    0 ≤
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
  fun D hnonPrime boundary_eq_ordered =>
    completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_finiteBessel
      f D hnonPrime boundary_eq_ordered

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
