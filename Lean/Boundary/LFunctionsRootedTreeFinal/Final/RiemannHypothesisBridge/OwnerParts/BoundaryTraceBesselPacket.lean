import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.BoundaryTraceBessel

/-!
# Boundary Trace-Bessel packet assembly

This file keeps the final RH owner route short by exposing the completed
affine packet decomposition as named component sinks.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- RH from canonical scheduled carrier factor bounds, component affine
integrability, and the two component packet value theorems. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrablePacketComponents_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (packetDecomposition :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
                probe family t) -
            ∑' n : ℕ,
              ∫ t : ℝ,
                ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                  probe family n t) +
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
                probe family t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                probe family t))
    (arithmeticEquality :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              probe family t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                probe family n t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            probe)
    (inverseGammaEquality :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              probe family t) -
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              probe family t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            probe) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrablePacketValue_owner
    factorData
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    (fun f =>
      let probe : ZetaAdmissibleFunction :=
        ZetaAdmissibleFunction.convolutionAutocorrelation f
      let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
      let arithmeticValue : ℂ :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          probe
      let archimedeanValue : ℂ :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          probe
      zetaCompletedAffineKernel_packet_value_of_component_values_owner
        probe family arithmeticValue archimedeanValue
        (packetDecomposition f)
        (arithmeticEquality f)
        (inverseGammaEquality f))

/-- RH from canonical scheduled carrier factor bounds, component affine
integrability, arithmetic packet value, and inverse-Gamma difference-kernel
value data. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrableArithmeticAndInverseGammaDifference_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (packetDecomposition :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
                probe family t) -
            ∑' n : ℕ,
              ∫ t : ℝ,
                ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                  probe family n t) +
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
                probe family t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                probe family t))
    (arithmeticEquality :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              probe family t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                probe family n t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            probe)
    (inverseGammaDifferenceIntegral :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            probe family t) =
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              probe family t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                probe family t)
    (archimedeanValue :
      ∀ f : ZetaAdmissibleFunction,
        let probe : ZetaAdmissibleFunction :=
          ZetaAdmissibleFunction.convolutionAutocorrelation f
        let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            probe family t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            probe) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrablePacketComponents_owner
    factorData
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    packetDecomposition
    arithmeticEquality
    (fun f =>
      let probe : ZetaAdmissibleFunction :=
        ZetaAdmissibleFunction.convolutionAutocorrelation f
      let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
      zetaCompletedAffineInverseGamma_packet_value_of_difference_kernel_value_owner
        probe family
        (inverseGammaDifferenceIntegral f)
        (archimedeanValue f))

/-- RH from canonical scheduled carrier factor bounds and log-derivative
control, routed through the completed affine packet component owner lemmas. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_logDerivControl_packet_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_affineComponentIntegrableArithmeticAndInverseGammaDifference_owner
    factorData
    (fun f =>
      zetaAutocorrelationPhysicalRightPrimeAffineKernel_integrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalRightInverseGammaAffineKernel_integrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalLeftReflectedCompletedAffineKernel_integrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalAffinePacket_decomposition_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalArithmeticPacket_value_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalInverseGammaDifference_integral_eq_sub_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalInverseGammaDifference_integral_eq_archimedean_of_logDerivControl_owner
        f (hPhi f) (hLog f))

/-- RH from separate zeta-side and inverse-Gamma data on the canonical scheduled
horizontal carrier, plus completed-log-derivative control. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_logDerivControl_packet_owner
    (zetaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (hPhi : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_logDerivControl_packet_owner
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData.ofParts
        (zetaData f)
        (gammaData f))
    hPhi
    hLog

/-- RH from canonical scheduled carrier factor bounds and supplied completed
log-derivative strip constants, routed through the affine packet owner chain. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_suppliedLogDerivConstants_packet_owner
    (factorData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (C :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < C f a b E N)
    (hCbound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv z‖ ≤
          C f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_logDerivControl_packet_owner
    factorData
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_suppliedConstants_owner
      C
      hCpos
      hCbound)

/-- RH from separate canonical scheduled carrier bound data and supplied
completed-log-derivative strip constants. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_suppliedLogDerivConstants_packet_owner
    (zetaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData : ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (C :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < C f a b E N)
    (hCbound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv z‖ ≤
          C f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_logDerivControl_packet_owner
    zetaData
    gammaData
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_suppliedConstants_owner
      C
      hCpos
      hCbound)

/-- RH from direct split polynomial constants on the canonical scheduled
carrier, plus supplied completed-log-derivative strip constants. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierSplitConstants_packet_owner
    (separated : ∀ f : ZetaAdmissibleFunction,
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        .HasPositiveSingularSeparation)
    (Czeta Cgamma :
      ∀ f : ZetaAdmissibleFunction, ℕ → ℝ)
    (Czeta_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < Czeta f N)
    (Cgamma_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < Cgamma f N)
    (Czeta_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ‖ZetaAdmissibleFunction.zetaSideNegLogDeriv z‖ ≤
          Czeta f N * (1 + ‖z.im‖) ^ N)
    (Cgamma_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma f N * (1 + ‖z.im‖) ^ N)
    (C :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < C f a b E N)
    (hCbound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv z‖ ≤
          C f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_suppliedLogDerivConstants_packet_owner
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofConstants
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        (separated f)
        (Czeta f)
        (Czeta_pos f)
        (Czeta_bound f))
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofLogDerivBound
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        (separated f)
        (Cgamma f)
        (Cgamma_pos f)
        (Cgamma_bound f))
    C
    hCpos
    hCbound

/-- RH from global split zeta-side and inverse-Gamma polynomial constants,
with canonical scheduled carrier separation. -/
theorem boundaryRiemannHypothesis_of_globalSplitLogDerivConstants_packet_owner
    (separated : ∀ f : ZetaAdmissibleFunction,
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        .HasPositiveSingularSeparation)
    (Czeta Cgamma :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (Czeta_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < Czeta f a b E N)
    (Cgamma_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < Cgamma f a b E N)
    (Czeta_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.zetaSideNegLogDeriv z‖ ≤
          Czeta f a b E N * (1 + ‖z.im‖) ^ N)
    (Cgamma_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_logDerivControl_packet_owner
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofConstants
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        (separated f)
        (fun N : ℕ =>
          Czeta f
            (min
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            N)
        (fun N : ℕ =>
          Czeta_pos f
            (min
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            N)
        (fun N z hz =>
          Czeta_bound f
            (min
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            N z hz))
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofLogDerivBound
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        (separated f)
        (fun N : ℕ =>
          Cgamma f
            (min
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            N)
        (fun N : ℕ =>
          Cgamma_pos f
            (min
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            N)
        (fun N z hz =>
          Cgamma_bound f
            (min
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 -
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            N z hz))
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteConstants
      Czeta
      Cgamma
      Czeta_pos
      Cgamma_pos
      Czeta_bound
      Cgamma_bound)

/-- RH from Cauchy logarithmic-derivative data on the canonical scheduled
carrier, plus supplied completed-log-derivative strip constants. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyLogDerivativeData_packet_owner
    (separated : ∀ f : ZetaAdmissibleFunction,
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        .HasPositiveSingularSeparation)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℕ → ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℕ → ℝ)
    (zetaRadius_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < zetaRadius f N)
    (zetaAmplitude_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < zetaAmplitude f N)
    (zetaValueLower_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < zetaValueLower f N)
    (gammaRadius_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < gammaRadius f N)
    (gammaAmplitude_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < gammaAmplitude f N)
    (gammaValueLower_pos :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ),
        0 < gammaValueLower f N)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f N)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f N)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f N) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f N * (1 + ‖z.im‖) ^ N)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f N) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f N * (1 + ‖z.im‖) ^ N)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        zetaValueLower f N ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (N : ℕ) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        gammaValueLower f N ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (C :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < C f a b E N)
    (hCbound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv z‖ ≤
          C f a b E N * (1 + ‖z.im‖) ^ N) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_suppliedLogDerivConstants_packet_owner
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofCauchyLogDerivative
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        (separated f)
        (zetaRadius f)
        (zetaAmplitude f)
        (zetaValueLower f)
        (zetaRadius_pos f)
        (zetaAmplitude_pos f)
        (zetaValueLower_pos f)
        (zetaDiffCont f)
        (zetaSphereBound f)
        (zetaValueLower_bound f))
    (fun f =>
      ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofCauchyLogDerivative
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
        (separated f)
        (gammaRadius f)
        (gammaAmplitude f)
        (gammaValueLower f)
        (gammaRadius_pos f)
        (gammaAmplitude_pos f)
        (gammaValueLower_pos f)
        (gammaDiffCont f)
        (gammaSphereBound f)
        (gammaValueLower_bound f))
    C
    hCpos
    hCbound

/-- RH from global completed-log-derivative factor bounds, routed through the
canonical scheduled affine packet owner chain. -/
theorem boundaryRiemannHypothesis_of_canonicalTransform_logDerivFactorBoundData_packet_owner
    (globalFactorData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierFactorData_logDerivControl_packet_owner
    (fun f =>
      globalFactorData
        (min
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 -
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (max
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 -
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_factorBoundData_owner
      globalFactorData)

/-- RH from separate global zeta-side and inverse-Gamma completed-log-derivative
bound data, routed through the canonical scheduled affine packet owner chain. -/
theorem boundaryRiemannHypothesis_of_canonicalTransform_logDerivBoundData_packet_owner
    (zetaData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierBoundData_logDerivControl_packet_owner
    (fun f =>
      zetaData
        (min
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 -
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (max
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 -
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (fun f =>
      gammaData
        (min
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 -
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (max
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 -
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_boundData_owner
      zetaData
      gammaData)

end
end LFunctions
end Boundary
