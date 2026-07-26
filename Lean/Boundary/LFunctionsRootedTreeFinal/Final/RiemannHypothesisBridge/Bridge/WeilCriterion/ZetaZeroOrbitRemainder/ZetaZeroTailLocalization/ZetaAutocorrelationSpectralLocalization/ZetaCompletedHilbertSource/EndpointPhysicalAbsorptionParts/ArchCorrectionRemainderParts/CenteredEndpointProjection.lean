import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorptionParts.ArchCorrectionRemainderParts.CenteredEndpointRieszBound

/-!
# Centered endpoint projection

This file owns the endpoint projection kernel before finite endpoint Bessel
compression is assembled.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The centered endpoint projection kernel: the non-prime centered packet
energy after removing the two endpoint trace fibers. -/
noncomputable def completedCenteredEndpointProjectionKernel
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) +
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) -
    (completedWeilEndpointTraceFiber f).gram

/-- The centered endpoint projection kernel unfolds to the
archimedean/correction endpoint residual. -/
theorem completedCenteredEndpointProjectionKernel_eq_archCorrectionRemainder
    (f : ZetaAdmissibleFunction) :
    completedCenteredEndpointProjectionKernel f =
      completedEndpointFiberArchCorrectionRemainder f := by
  rfl

/-- Projection-complement nonnegativity gives nonnegativity of the centered
endpoint projection kernel. -/
theorem completedCenteredEndpointProjectionKernel_nonnegative_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    0 ≤ completedCenteredEndpointProjectionKernel f :=
  fun hcomplement =>
  let hbound :
      (completedWeilEndpointTraceFiber f).gram ≤
        completedCenteredEndpointControlNormSq f :=
    completedWeilEndpointTraceFiber_gram_le_controlNormSq_riesz_of_projectionComplement
      f hcomplement
  let hcontrol :
      completedCenteredEndpointControlNormSq f =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedCenteredEndpointControlNormSq_eq_archCorrectionPacketGrams f
  let harch :
      (completedWeilEndpointTraceFiber f).gram ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    Eq.subst
      (motive := fun value : ℝ =>
        (completedWeilEndpointTraceFiber f).gram ≤ value)
      hcontrol
      hbound
  let hkernel :
      0 ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) -
          (completedWeilEndpointTraceFiber f).gram :=
    sub_nonneg.mpr harch
  hkernel

/-- Projection-complement nonnegativity gives domination of the endpoint trace
fiber by the archimedean/correction packet Grams. -/
theorem completedEndpointTraceFiber_gram_le_archCorrectionPacketGrams_centeredProjection_of_projectionComplement
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryHilbertSourceEndpointProjectionComplement_centeredRiesz f →
    (completedWeilEndpointTraceFiber f).gram ≤
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
  fun hcomplement =>
  let hkernel :
      0 ≤
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) -
          (completedWeilEndpointTraceFiber f).gram :=
    completedCenteredEndpointProjectionKernel_nonnegative_of_projectionComplement
      f hcomplement
  sub_nonneg.mp hkernel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
