import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalCommonLimitPacketComponents

/-!
# Final common-limit owner

This file keeps the public common-limit theorem as a thin wrapper over the
canonical scheduled horizontal bounds and the canonical Phi/Gamma affine packet
data for autocorrelation probes.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Public pole-corrected common-limit owner.

The theorem is intentionally only an assembly wrapper.  The mathematical work
is owned by the canonical input constructors it consumes. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_canonicalPhiGammaPacket_final_owner
    horizontalBounds

theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_owner
    carrierData.horizontalBoundsFamily

end
end LFunctions
end Boundary
