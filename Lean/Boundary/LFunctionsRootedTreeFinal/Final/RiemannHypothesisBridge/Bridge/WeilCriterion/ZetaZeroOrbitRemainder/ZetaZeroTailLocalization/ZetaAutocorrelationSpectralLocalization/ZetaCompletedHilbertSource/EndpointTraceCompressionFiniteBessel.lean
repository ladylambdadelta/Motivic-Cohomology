import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointFiniteBessel

/-!
# Endpoint trace compression from finite Bessel

This file owns the non-cyclic endpoint compression bridge supplied by the
finite Bessel theorem.  It deliberately stops at the physical boundary scalar;
the boundary-to-ordered-heart identification belongs to the later GNS boundary
owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite Bessel domination transports from the seed endpoint trace fiber to
the canonical Hilbert-source endpoint trace fiber. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_boundaryChannel_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
  let seedBound :
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedEndpointTraceFiber_gram_le_boundaryChannel_finiteBessel_source
      f D hnonPrime
  let sourceSeed :
      (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram =
        (completedWeilEndpointTraceFiber f).gram :=
    completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))
    sourceSeed.symm
    seedBound

/-- A physical boundary-to-ordered-heart identification converts the
finite-Bessel boundary domination into canonical ordered-heart domination. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  let boundaryBound :
      (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_boundaryChannel_of_finiteBessel
      f D hnonPrime
  Eq.subst
    (motive := fun value : ℝ =>
      (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram ≤ value)
    boundary_eq_ordered
    boundaryBound

/-- A physical boundary-to-positive-presentation identification converts the
finite-Bessel boundary domination into seed endpoint domination by the completed
positive GNS presentation. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  let boundaryBound :
      (completedWeilEndpointTraceFiber f).gram ≤
        Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) :=
    completedEndpointTraceFiber_gram_le_boundaryChannel_finiteBessel_source
      f D hnonPrime
  Eq.subst
    (motive := fun value : ℝ =>
      (completedWeilEndpointTraceFiber f).gram ≤ value)
    boundary_eq_positive
    boundaryBound

/-- The finite-Bessel bridge yields nonnegativity of the seed
positive-presentation endpoint compression remainder after the physical
boundary scalar has been identified with the positive GNS presentation. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_positive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    f).mpr
    (completedEndpointTraceFiber_gram_le_positivePresentation_of_finiteBessel
      f D hnonPrime boundary_eq_positive)

/-- The finite-Bessel bridge yields nonnegativity of the canonical
Hilbert-source endpoint compression remainder after the boundary scalar has
been identified with the ordered heart. -/
theorem completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_finiteBessel
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f)
    (boundary_eq_ordered :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        completedOrderedHeartScalar (completedBoundaryHilbertSource f)) :
    0 ≤
      completedBoundaryHilbertSourceEndpointCompressionRemainder
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointGram_le_orderedHeart
    (completedBoundaryHilbertSource f)
    (completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_orderedHeart_of_finiteBessel
      f D hnonPrime boundary_eq_ordered)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
