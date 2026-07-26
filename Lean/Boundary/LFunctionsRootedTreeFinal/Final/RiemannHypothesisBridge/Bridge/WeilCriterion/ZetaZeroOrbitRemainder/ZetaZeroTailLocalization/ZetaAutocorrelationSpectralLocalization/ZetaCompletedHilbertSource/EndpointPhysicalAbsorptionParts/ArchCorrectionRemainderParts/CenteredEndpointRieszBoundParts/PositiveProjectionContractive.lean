import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBoundParts.PositiveProjectionComplement

/-!
# Centered endpoint positive projection contractivity

This file owns the Hilbert-source projection contractivity input behind the
full positive endpoint Bessel estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Projection-complement nonnegativity gives contractivity of the endpoint
trace projection inside the completed positive GNS scalar. -/
theorem completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_GNSScalar_centeredRiesz_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedBoundaryHilbertSourceEndpointTraceFiber
        (completedBoundaryHilbertSource f)).gram ≤
      completedBoundaryHermitianGNSScalar
        (completedBoundaryHilbertSource f) :=
  fun hcomplement =>
    completedBoundaryHilbertSourceEndpointTraceFiber_gram_le_GNSScalar_of_projectionComplement_nonnegative_centeredRiesz
      f
      hcomplement

/-- The Hilbert-source projection contractivity gives seed endpoint
domination by the positive presentation scalar. -/
theorem completedWeilEndpointTraceFiber_gram_le_positivePresentation_of_projectionContractive_centeredRiesz
    (f : ZetaAdmissibleFunction)
    (hprojection :
      (completedBoundaryHilbertSourceEndpointTraceFiber
          (completedBoundaryHilbertSource f)).gram ≤
        completedBoundaryHermitianGNSScalar
          (completedBoundaryHilbertSource f)) :
    (completedWeilEndpointTraceFiber f).gram ≤
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  let sourceGram : ℝ :=
    (completedBoundaryHilbertSourceEndpointTraceFiber
      (completedBoundaryHilbertSource f)).gram
  let seedGram : ℝ := (completedWeilEndpointTraceFiber f).gram
  let sourceScalar : ℝ :=
    completedBoundaryHermitianGNSScalar
      (completedBoundaryHilbertSource f)
  let positiveScalar : ℝ :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar f
  have hgram : sourceGram = seedGram := by
    unfold sourceGram
    unfold seedGram
    exact completedBoundaryHilbertSourceEndpointTraceFiber_source_gram_eq f
  have hscalar : sourceScalar = positiveScalar := by
    unfold sourceScalar
    unfold positiveScalar
    exact completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar
      f
  have hseedSource : seedGram ≤ sourceScalar :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ sourceScalar)
      hgram
      hprojection
  exact Eq.subst
    (motive := fun value : ℝ => seedGram ≤ value)
    hscalar
    hseedSource

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
