import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledHorizontalBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathAffineChannelLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathAnalyticPacket

/-!
# Final common-limit assembly from scheduled factor-bound data

This owner part keeps the final RH route on the corrected physical
autocorrelation boundary lane.  It does not import the historical broad contour
owner; it only assembles canonical scheduled-carrier factor-bound data and the
matching physical boundary limit into the pole-corrected common-limit theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Canonical scheduled-carrier factor-bound data and the corresponding
physical boundary limit give the corrected zero-side/physical-boundary common
limit.  This is the separated scheduled-carrier version of the final assembly,
and does not require log-derivative control on arbitrary carriers. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
              f
              ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
                ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
              (factorData f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_cleanScheduledPackageBoundaryLimit
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    boundaryLimit

/-- Polynomial scheduled packages and their physical boundary endpoint give the
corrected zero-side/physical-boundary common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledBoundaryLimit_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledEndpointLimits
    hPolynomial
    (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_family_of_selectedTangentResidue
      hPolynomial)
    boundaryLimit

/-- Polynomial scheduled packages plus affine-kernel integrability and value
construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffineKernelIntegrableValue_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  let channelLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f))) :=
    fun f =>
      zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)
        (hPolynomial f).height_schedule
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f)
  let boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f))) :=
    fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelLimit f)
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledBoundaryLimit_final_owner
    hPolynomial
    boundaryLimit

/-- Polynomial scheduled packages plus affine packet data construct the
pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffinePacketData_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffineKernelIntegrableValue_final_owner
    hPolynomial
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
        f
        (packetData f).right_prime_integrable
        (packetData f).right_inverse_gamma_integrable)
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
        f
        (packetData f).left_reflected_integrable)
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
        f
        (packetData f).right_prime_integrable
        (packetData f).right_inverse_gamma_integrable
        (packetData f).left_reflected_integrable
        (packetData f).left_inverse_gamma_integrable
        (packetData f).left_arithmetic_integral_exchange
        (packetData f).arithmetic_equality
        (packetData f).inverse_gamma_difference_integral
        (packetData f).archimedean_value)

/-- Polynomial scheduled packages plus physical completed-log-derivative control
construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledPhysicalLogDerivControl_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffineKernelIntegrableValue_final_owner
    hPolynomial
    (fun f =>
      zetaAutocorrelationPhysicalRightAffineKernel_integrable_of_logDerivControl_owner
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalLeftAffineKernel_integrable_of_logDerivControl_owner
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (hLog f))
    (fun f =>
      zetaAutocorrelationPhysicalAffineKernel_integral_eq_physical_of_logDerivControl_owner
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (hLog f))

/-- Canonical scheduled horizontal polynomial bounds plus physical
completed-log-derivative control construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_physicalLogDerivControl_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledPhysicalLogDerivControl_final_owner
    (ZetaAdmissibleFunction.canonicalScheduledPolynomialPackage_of_horizontalBounds
      horizontalBounds)
    hLog

/-- Canonical scheduled horizontal polynomial bounds and their physical
boundary endpoint construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_boundaryLimit_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
              f
              (horizontalBounds f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f) :=
    ZetaAdmissibleFunction.canonicalScheduledPolynomialPackage_of_horizontalBounds
      horizontalBounds
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledBoundaryLimit_final_owner
    hPolynomial
    boundaryLimit

/-- Canonical scheduled horizontal polynomial bounds and the corresponding
affine-channel physical endpoint construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affineChannelLimit_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (channelLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
                f
                (horizontalBounds f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  let boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
              f
              (horizontalBounds f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f))) :=
    fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
          f
          (horizontalBounds f))
        (channelLimit f)
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_boundaryLimit_final_owner
    horizontalBounds
    boundaryLimit

/-- Canonical scheduled horizontal polynomial bounds plus affine-kernel
integrability and value construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affineKernelIntegrableValue_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affineChannelLimit_final_owner
    horizontalBounds
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAffineChannel_tendsto_physical_of_canonicalScheduledPathBounds_integrable_value
        f
        (horizontalBounds f).degree
        (horizontalBounds f).constant
        (horizontalBounds f).constant_pos
        (horizontalBounds f).top_bound
        (horizontalBounds f).bottom_bound
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

/-- Canonical scheduled horizontal polynomial bounds plus affine packet data
construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affineKernelIntegrableValue_final_owner
    horizontalBounds
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
        f
        (packetData f).right_prime_integrable
        (packetData f).right_inverse_gamma_integrable)
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
        f
        (packetData f).left_reflected_integrable)
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
        f
        (packetData f).right_prime_integrable
        (packetData f).right_inverse_gamma_integrable
        (packetData f).left_reflected_integrable
        (packetData f).left_inverse_gamma_integrable
        (packetData f).left_arithmetic_integral_exchange
        (packetData f).arithmetic_equality
        (packetData f).inverse_gamma_difference_integral
        (packetData f).archimedean_value)

/-- Variable-local canonical scheduled Cauchy data plus affine packet data
construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledVariableCauchyPathData_affinePacketData_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.of_variableCauchyPathData
        f
        (K f)
        (zetaData f)
        (gammaData f))
    packetData

/-- Canonical scheduled horizontal polynomial bounds plus concrete
autocorrelation completed-log-derivative control construct the pole-corrected
common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_concreteControl_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
    horizontalBounds
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_concreteControl_owner
        f
        hConcrete)

/-- Canonical scheduled horizontal polynomial bounds plus split autocorrelation
completed-log-derivative factor controls construct the pole-corrected common
limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_splitControls_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_concreteControl_final_owner
    horizontalBounds
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled horizontal polynomial bounds plus global
completed-log-derivative factor controls construct the pole-corrected common
limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_globalFactorControls_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_splitControls_final_owner
    horizontalBounds
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

/-- Canonical scheduled Cauchy path data and the corresponding affine-channel
physical endpoint construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affineChannelLimit_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (channelLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
                f (K f) (zetaData f) (gammaData f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f) :=
    fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
        f
        (K f)
        (zetaData f)
        (gammaData f)
  let boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f))) :=
    fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelLimit f)
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledBoundaryLimit_final_owner
    hPolynomial
    boundaryLimit

/-- Canonical scheduled Cauchy path data plus affine-kernel integrability and
the full-line affine value construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affineChannelLimit_final_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAffineChannel_tendsto_physical_of_canonicalScheduledCauchyPathData_integrable_value
        f
        (K f)
        (zetaData f)
        (gammaData f)
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

/-- Canonical scheduled Cauchy path data plus affine packet data construct the
pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affinePacketData_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_final_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
        f
        (packetData f).right_prime_integrable
        (packetData f).right_inverse_gamma_integrable)
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
        f
        (packetData f).left_reflected_integrable)
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
        f
        (packetData f).right_prime_integrable
        (packetData f).right_inverse_gamma_integrable
        (packetData f).left_reflected_integrable
        (packetData f).left_inverse_gamma_integrable
        (packetData f).left_arithmetic_integral_exchange
        (packetData f).arithmetic_equality
        (packetData f).inverse_gamma_difference_integral
        (packetData f).archimedean_value)

/-- Canonical scheduled Cauchy path data plus concrete autocorrelation
completed-log-derivative control construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affinePacketData_final_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_concreteControl_owner
        f
        hConcrete)

/-- Canonical scheduled Cauchy path data plus split autocorrelation
completed-log-derivative factor controls construct the pole-corrected common
limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_splitControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_final_owner
    K
    zetaData
    gammaData
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled Cauchy path data plus global completed-log-derivative
factor controls construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_globalFactorControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_splitControls_final_owner
    K
    zetaData
    gammaData
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

end
end LFunctions
end Boundary
