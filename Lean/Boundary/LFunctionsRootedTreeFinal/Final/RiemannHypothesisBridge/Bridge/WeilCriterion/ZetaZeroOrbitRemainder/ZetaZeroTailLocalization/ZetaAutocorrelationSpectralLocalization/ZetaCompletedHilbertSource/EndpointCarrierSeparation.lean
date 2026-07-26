import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceCompression

/-!
# Endpoint carrier separation

This file owns the finite endpoint carrier-control scalar.  The completed
endpoint evaluations are not bounded by the centered zero-coordinate packet
alone; the carrier norm explicitly includes the endpoint fiber.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The visible two-endpoint carrier energy. -/
noncomputable def completedEndpointCarrierEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.normSq (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
    Complex.normSq (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ))

/-- The centered archimedean/correction packet energy. -/
noncomputable def completedEndpointCenteredPacketEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.coordinateGram
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
    ZetaHermitianPacketEnsemble.coordinateGram
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0)

/-- The quantitative carrier-control norm used before any projection-complement
or boundary-identification theorem is applied. -/
noncomputable def completedEndpointCarrierControlNormSq
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedEndpointCarrierEnergy f + completedEndpointCenteredPacketEnergy f

/-- The endpoint carrier energy unfolds to the two endpoint spectral squares. -/
theorem completedEndpointCarrierEnergy_eq_endpointPhiNorms
    (f : ZetaAdmissibleFunction) :
    completedEndpointCarrierEnergy f =
      Complex.normSq (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) :=
  Eq.refl (completedEndpointCarrierEnergy f)

/-- The centered packet energy unfolds to the visible centered packet squares. -/
theorem completedEndpointCenteredPacketEnergy_eq_centeredPacketGrams
    (f : ZetaAdmissibleFunction) :
    completedEndpointCenteredPacketEnergy f =
      ZetaHermitianPacketEnsemble.coordinateGram
          (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) +
        ZetaHermitianPacketEnsemble.coordinateGram
          ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
            zetaCompletedExplicitFormulaPhi f 0) :=
  Eq.refl (completedEndpointCenteredPacketEnergy f)

/-- The carrier-control norm unfolds to carrier energy plus centered packet
energy. -/
theorem completedEndpointCarrierControlNormSq_eq
    (f : ZetaAdmissibleFunction) :
    completedEndpointCarrierControlNormSq f =
      completedEndpointCarrierEnergy f + completedEndpointCenteredPacketEnergy f :=
  Eq.refl (completedEndpointCarrierControlNormSq f)

/-- The centered packet energy is nonnegative. -/
theorem completedEndpointCenteredPacketEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedEndpointCenteredPacketEnergy f :=
  add_nonneg
    (Complex.normSq_nonneg
      (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f))
    (Complex.normSq_nonneg
      ((Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
        zetaCompletedExplicitFormulaPhi f 0))

/-- Quantitative carrier separation with constant `1` for the explicit
carrier-control norm. -/
theorem completedEndpointCarrierEnergy_le_carrierControlNormSq
    (f : ZetaAdmissibleFunction) :
    completedEndpointCarrierEnergy f ≤ completedEndpointCarrierControlNormSq f :=
  let hpacket : 0 ≤ completedEndpointCenteredPacketEnergy f :=
    completedEndpointCenteredPacketEnergy_nonnegative f
  let hcontrol :
      completedEndpointCarrierControlNormSq f =
        completedEndpointCarrierEnergy f + completedEndpointCenteredPacketEnergy f :=
    completedEndpointCarrierControlNormSq_eq f
  Eq.subst
    (motive := fun value : ℝ => completedEndpointCarrierEnergy f ≤ value)
    hcontrol.symm
    (le_add_of_nonneg_right hpacket)

/-- The carrier-control estimate in visible endpoint coordinates. -/
theorem completedEndpointPhiNorms_le_carrierControlNormSq
    (f : ZetaAdmissibleFunction) :
    Complex.normSq (zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) +
        Complex.normSq (zetaCompletedExplicitFormulaPhi f (1 / 2 : ℂ)) ≤
      completedEndpointCarrierControlNormSq f :=
  Eq.subst
    (motive := fun value : ℝ => value ≤ completedEndpointCarrierControlNormSq f)
    (completedEndpointCarrierEnergy_eq_endpointPhiNorms f)
    (completedEndpointCarrierEnergy_le_carrierControlNormSq f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
