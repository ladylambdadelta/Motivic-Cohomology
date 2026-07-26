import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression

/-!
# Centered endpoint positive projection complement

This file owns the endpoint projection-complement energy inside the completed
positive GNS scalar.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The endpoint projection-complement energy in the canonical completed
positive GNS scalar. -/
noncomputable def completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) -
    (completedBoundaryHilbertSourceEndpointTraceFiber
      (completedBoundaryHilbertSource f)).gram

/-- The endpoint projection-complement energy unfolds to scalar minus endpoint
trace Gram. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz_eq
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f =
      completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) -
        (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram := by
  rfl

/-- Endpoint trace-fiber domination by the ordered-heart scalar transports to
domination by the completed positive GNS scalar of the same source. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_GNSScalar_of_orderedHeart
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedOrderedHeartScalar (completedBoundaryHilbertSource f) →
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f) :=
  fun hordered =>
  let source : CompletedBoundaryHilbertSource :=
    completedBoundaryHilbertSource f
  let hscalar :
      completedOrderedHeartScalar source =
        completedBoundaryHermitianGNSScalar source :=
    Eq.refl (completedOrderedHeartScalar source)
  let hdomination :
      (completedBoundaryHilbertSourceEndpointTraceFiber source).gram ≤
        completedBoundaryHermitianGNSScalar source :=
    Eq.subst
      (motive := fun value : ℝ =>
        (completedBoundaryHilbertSourceEndpointTraceFiber source).gram ≤
          value)
      hscalar
      hordered
  hdomination

/-- Endpoint trace-fiber domination by the completed positive GNS scalar gives
nonnegativity of the endpoint projection-complement energy. -/
theorem completedBoundaryHilbertSourceEndpointProjectionComplement_nonnegative_centeredRiesz_of_GNSScalar
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f) →
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f :=
  fun hdomination =>
  let source : CompletedBoundaryHilbertSource :=
    completedBoundaryHilbertSource f
  let endpointGram : ℝ :=
    (completedBoundaryHilbertSourceEndpointTraceFiber source).gram
  let sourceScalar : ℝ :=
    completedBoundaryHermitianGNSScalar source
  let hsub : 0 ≤ sourceScalar - endpointGram :=
    sub_nonneg.mpr hdomination
  let hcomplement :
      completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f =
        sourceScalar - endpointGram :=
    Eq.refl (completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f)
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hcomplement.symm
    hsub

/-- Nonnegativity of the endpoint projection-complement energy gives
contractivity of the endpoint trace projection. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_GNSScalar_of_projectionComplement_nonnegative_centeredRiesz
    (f : ZetaAdmissibleFunction)
    (hcomplement :
      0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz
        f) :
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f) := by
  have hsub :
      0 ≤
        completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) -
          (completedBoundaryHilbertSourceEndpointTraceFiber
            (completedBoundaryHilbertSource f)).gram :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      (completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz_eq
        f)
      hcomplement
  exact sub_nonneg.mp hsub

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
