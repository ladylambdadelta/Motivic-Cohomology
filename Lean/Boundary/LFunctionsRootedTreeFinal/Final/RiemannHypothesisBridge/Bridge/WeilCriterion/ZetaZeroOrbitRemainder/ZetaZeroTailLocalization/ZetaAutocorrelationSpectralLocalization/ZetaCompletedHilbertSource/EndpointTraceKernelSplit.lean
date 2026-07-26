import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorption

/-!
# Endpoint trace kernel split

This file peels the endpoint-compression sink from an existential split to a
concrete kernel-remainder scalar.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The concrete endpoint kernel remainder after removing the finite endpoint
trace fiber from the completed ordered-heart scalar. -/
noncomputable def completedBoundaryHilbertSourceEndpointKernelRemainder
    (X : CompletedBoundaryHilbertSource) : ℝ :=
  completedBoundaryHilbertSourceEndpointCompressionRemainder X

/-- The concrete endpoint kernel remainder is the endpoint compression
remainder. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_eq_compressionRemainder
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointKernelRemainder X =
      completedBoundaryHilbertSourceEndpointCompressionRemainder X :=
  Eq.refl (completedBoundaryHilbertSourceEndpointKernelRemainder X)

/-- The concrete endpoint kernel remainder unfolds to ordered heart minus
endpoint trace Gram. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_eq_orderedHeart_sub_endpointGram
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointKernelRemainder X =
      completedOrderedHeartScalar X -
        (completedBoundaryHilbertSourceEndpointTraceFiber X).gram :=
  Eq.trans
    (completedBoundaryHilbertSourceEndpointKernelRemainder_eq_compressionRemainder
      X)
    (completedBoundaryHilbertSourceEndpointCompressionRemainder_eq_orderedHeart_sub_endpointGram
      X)

/-- If the concrete endpoint-kernel remainder is ordered heart minus endpoint
Gram, then the ordered heart splits as endpoint Gram plus that remainder. -/
theorem completedOrderedHeartScalar_eq_endpointTraceGram_add_of_kernel_eq_sub
    (ordered : ℝ)
    (endpointGram : ℝ)
    (kernel : ℝ)
    (hkernel : kernel = ordered - endpointGram) :
    ordered = endpointGram + kernel :=
  (endpointTraceDebt_add_sub_cancel ordered endpointGram).trans
    (congrArg (fun value : ℝ => endpointGram + value) hkernel.symm)

/-- The ordered-heart scalar splits as endpoint trace Gram plus the concrete
endpoint kernel remainder. -/
theorem completedOrderedHeartScalar_eq_endpointTraceGram_add_endpointKernelRemainder
    (X : CompletedBoundaryHilbertSource) :
    completedOrderedHeartScalar X =
      (completedBoundaryHilbertSourceEndpointTraceFiber X).gram +
        completedBoundaryHilbertSourceEndpointKernelRemainder X :=
  completedOrderedHeartScalar_eq_endpointTraceGram_add_of_kernel_eq_sub
    (completedOrderedHeartScalar X)
    ((completedBoundaryHilbertSourceEndpointTraceFiber X).gram)
    (completedBoundaryHilbertSourceEndpointKernelRemainder X)
    (completedBoundaryHilbertSourceEndpointKernelRemainder_eq_orderedHeart_sub_endpointGram
      X)

/-- Nonnegativity of the concrete endpoint kernel remainder gives the named
endpoint-kernel split. -/
theorem completedBoundaryHilbertSourceEndpointKernelSplit_of_endpointKernelRemainder_nonnegative
    (X : CompletedBoundaryHilbertSource)
    (hkernel :
      0 ≤ completedBoundaryHilbertSourceEndpointKernelRemainder X) :
    completedBoundaryHilbertSourceEndpointKernelSplit X :=
  ⟨completedBoundaryHilbertSourceEndpointKernelRemainder X,
    completedOrderedHeartScalar_eq_endpointTraceGram_add_endpointKernelRemainder
      X,
    hkernel⟩

/-- The named endpoint-kernel split implies nonnegativity of the concrete
endpoint-kernel remainder. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_nonnegative_of_endpointKernelSplit
    (X : CompletedBoundaryHilbertSource)
    (hsplit : completedBoundaryHilbertSourceEndpointKernelSplit X) :
    0 ≤ completedBoundaryHilbertSourceEndpointKernelRemainder X :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedBoundaryHilbertSourceEndpointKernelRemainder_eq_compressionRemainder
      X).symm
    (completedBoundaryHilbertSourceEndpointCompressionRemainder_nonnegative_of_endpointKernelSplitProp
      X hsplit)

/-- The named endpoint-kernel split is equivalent to nonnegativity of the
concrete endpoint kernel remainder. -/
theorem completedBoundaryHilbertSourceEndpointKernelSplit_iff_endpointKernelRemainder_nonnegative
    (X : CompletedBoundaryHilbertSource) :
    completedBoundaryHilbertSourceEndpointKernelSplit X ↔
      0 ≤ completedBoundaryHilbertSourceEndpointKernelRemainder X :=
  ⟨completedBoundaryHilbertSourceEndpointKernelRemainder_nonnegative_of_endpointKernelSplit
      X,
    completedBoundaryHilbertSourceEndpointKernelSplit_of_endpointKernelRemainder_nonnegative
      X⟩

/-- Canonical-source endpoint kernel remainder nonnegativity gives seed-level
positive presentation compression nonnegativity. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointKernelRemainder
    (f : ZetaAdmissibleFunction)
    (hkernel :
      0 ≤
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f)) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  completedEndpointFiberPositivePresentationRemainder_nonnegative_of_sourceEndpointKernelSplitProp
    f
    (completedBoundaryHilbertSourceEndpointKernelSplit_of_endpointKernelRemainder_nonnegative
      (completedBoundaryHilbertSource f) hkernel)

/-- On canonical sources, the concrete endpoint-kernel remainder is exactly
the seed-level positive-presentation endpoint remainder. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_source_eq_positivePresentationRemainder
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourceEndpointKernelRemainder
        (completedBoundaryHilbertSource f) =
      completedEndpointFiberPositivePresentationRemainder f :=
  Eq.trans
    (completedBoundaryHilbertSourceEndpointKernelRemainder_eq_compressionRemainder
      (completedBoundaryHilbertSource f))
    (completedEndpointFiberPositivePresentationRemainder_eq_sourceEndpointCompressionRemainder
      f).symm

/-- Seed-level positive-presentation endpoint remainder nonnegativity gives
canonical-source endpoint-kernel remainder nonnegativity. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_positivePresentationRemainder
    (f : ZetaAdmissibleFunction)
    (hpositive :
      0 ≤ completedEndpointFiberPositivePresentationRemainder f) :
    0 ≤
      completedBoundaryHilbertSourceEndpointKernelRemainder
        (completedBoundaryHilbertSource f) :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedBoundaryHilbertSourceEndpointKernelRemainder_source_eq_positivePresentationRemainder
      f).symm
    hpositive

/-- Endpoint-fiber domination by the positive GNS presentation gives
canonical-source endpoint-kernel remainder nonnegativity. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointFiberGram_le_positivePresentation
    (f : ZetaAdmissibleFunction)
    (hdomination :
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    0 ≤
      completedBoundaryHilbertSourceEndpointKernelRemainder
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_positivePresentationRemainder
    f
    ((completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
      f).mpr hdomination)

/-- Canonical-source endpoint-kernel remainder nonnegativity gives endpoint
fiber domination by the positive presentation. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_of_sourceEndpointKernelRemainder_nonnegative
    (f : ZetaAdmissibleFunction)
    (hkernel :
      0 ≤
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f)) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    f).mp
    (Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedBoundaryHilbertSourceEndpointKernelRemainder_source_eq_positivePresentationRemainder
        f)
      hkernel)

/-- The canonical endpoint-kernel sink is exactly endpoint-fiber domination
by the positive GNS presentation. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_iff_endpointFiberGram_le_positivePresentation
    (f : ZetaAdmissibleFunction) :
    0 ≤
      completedBoundaryHilbertSourceEndpointKernelRemainder
        (completedBoundaryHilbertSource f) ↔
      (completedWeilEndpointTraceFiber f).gram ≤
        zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  ⟨completedEndpointTraceFiber_gram_le_positivePresentation_of_sourceEndpointKernelRemainder_nonnegative
      f,
    completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointFiberGram_le_positivePresentation
      f⟩

/-- On a canonical source, the positive presentation scalar is the ordered
heart scalar. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_sourceOrderedHeart
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) :=
  (completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar f).symm

/-- The canonical source ordered-heart scalar splits into the endpoint trace
fiber and the canonical endpoint-kernel remainder. -/
theorem completedOrderedHeartScalar_source_eq_endpointTraceGram_add_endpointKernelRemainder
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar (completedBoundaryHilbertSource f) =
      (completedWeilEndpointTraceFiber f).gram +
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f) :=
  (completedOrderedHeartScalar_eq_endpointTraceGram_add_endpointKernelRemainder
    (completedBoundaryHilbertSource f)).trans
    (congrArg
      (fun value : ℝ =>
        value +
          completedBoundaryHilbertSourceEndpointKernelRemainder
            (completedBoundaryHilbertSource f))
      (completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f))

/-- Boundary equality to the positive presentation transports the canonical
source ordered-heart split to the physical endpoint split scalar. -/
theorem completedBoundaryChannel_re_eq_endpointTraceGram_add_sourceKernelRemainder
    (f : ZetaAdmissibleFunction)
    (boundaryToPositive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
      (completedWeilEndpointTraceFiber f).gram +
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f) :=
  boundaryToPositive.trans
    ((zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_sourceOrderedHeart f).trans
      (completedOrderedHeartScalar_source_eq_endpointTraceGram_add_endpointKernelRemainder
        f))

/-- A physical-to-positive boundary identification and a nonnegative
source endpoint-kernel remainder give the physical positive-kernel endpoint
trace split. -/
theorem zetaCompletedEndpointTracePositiveKernelSplit_of_boundary_eq_positivePresentation_sourceEndpointKernelRemainder
    (f : ZetaAdmissibleFunction)
    (boundaryToPositive :
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f)
    (sourceKernelNonnegative :
      0 ≤
        completedBoundaryHilbertSourceEndpointKernelRemainder
          (completedBoundaryHilbertSource f)) :
    ZetaCompletedEndpointTracePositiveKernelSplit f :=
  ⟨completedBoundaryHilbertSourceEndpointKernelRemainder
      (completedBoundaryHilbertSource f),
    completedBoundaryChannel_re_eq_endpointTraceGram_add_sourceKernelRemainder
      f boundaryToPositive,
    sourceKernelNonnegative⟩

/-- Owner theorem for domination of the endpoint fiber by the positive GNS
presentation. -/
theorem completedEndpointTraceFiber_gram_le_positivePresentation_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f :=
  completedEndpointTraceFiber_gram_le_positivePresentation_ownerSchurProjection_of_projectionComplement
    f hcomplement

/-- Positive endpoint domination gives nonnegativity of the positive endpoint
presentation remainder. -/
theorem completedEndpointFiberPositivePresentationRemainder_nonnegative_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f) :
    0 ≤ completedEndpointFiberPositivePresentationRemainder f :=
  (completedEndpointFiberPositivePresentationRemainder_nonnegative_iff_endpointFiberGram_le_positivePresentation
    f).mpr
    (completedEndpointTraceFiber_gram_le_positivePresentation_owner_of_projectionComplement
      f hcomplement)

/-- Owner theorem for nonnegativity of the canonical source endpoint-kernel
remainder. -/
theorem completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f) :
    0 ≤
      completedBoundaryHilbertSourceEndpointKernelRemainder
        (completedBoundaryHilbertSource f) :=
  completedBoundaryHilbertSourceEndpointKernelRemainder_source_nonnegative_of_endpointFiberGram_le_positivePresentation
    f
    (completedEndpointTraceFiber_gram_le_positivePresentation_owner_of_projectionComplement
      f hcomplement)

/-- Owner theorem for the positive-kernel endpoint trace split.

This is the physical trace split: the completed boundary trace is the two
endpoint fibers plus a nonnegative kernel remainder. -/
theorem zetaCompletedEndpointTracePositiveKernelSplit_owner
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    ZetaCompletedEndpointTracePositiveKernelSplit f :=
  zetaCompletedEndpointTracePositiveKernelSplit_of_traceRemainder_nonnegative
    f
    (completedWeilEndpointTraceRemainder_nonnegative_sourcePhysicalAbsorption
      f D hnonPrime)

/-- Owner theorem for the endpoint trace-reconstruction remainder. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_owner
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hnonPrime : CompletedEndpointNonPrimeTraceResidualNonnegative f) :
    0 ≤ completedWeilEndpointTraceRemainder f :=
  completedWeilEndpointTraceRemainder_nonnegative_sourcePhysicalAbsorption
    f D hnonPrime

/-- Source theorem for the endpoint trace-reconstruction remainder after the
non-prime residual is supplied by the archimedean/correction owner theorem and
projection-complement nonnegativity. -/
theorem completedWeilEndpointTraceRemainder_nonnegative_source_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedWeilEndpointTraceRemainder f :=
  fun hcomplement =>
  let harch :
      0 ≤ completedEndpointFiberArchCorrectionRemainder f :=
    completedEndpointFiberArchCorrectionRemainder_nonnegative_sourceSchurProjection_of_projectionComplement
      f hcomplement
  let hnonPrime :
      CompletedEndpointNonPrimeTraceResidualNonnegative f :=
    completedEndpointNonPrimeTraceResidualNonnegative_of_archCorrectionRemainder_nonnegative
      f harch
  completedWeilEndpointTraceRemainder_nonnegative_sourcePhysicalAbsorption
    f D hnonPrime

/-- Source theorem for the positive-kernel endpoint trace split after the
non-prime residual is supplied by the archimedean/correction owner theorem and
projection-complement nonnegativity. -/
theorem zetaCompletedEndpointTracePositiveKernelSplit_source_owner_of_projectionComplement
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    ZetaCompletedEndpointTracePositiveKernelSplit f :=
  fun hcomplement =>
    zetaCompletedEndpointTracePositiveKernelSplit_of_traceRemainder_nonnegative
      f
      (completedWeilEndpointTraceRemainder_nonnegative_source_owner_of_projectionComplement
        f D hcomplement)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
