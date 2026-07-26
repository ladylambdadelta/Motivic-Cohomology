import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.FactorBoundDataOwner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalLogDerivControlOwner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.FinalCommonLimitCanonicalPathCauchyData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.BoundaryTraceBesselCanonicalCauchyFactor
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.FinalCriteria
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.GlobalLogDerivCauchySinks
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.CanonicalCarrierSeparationConstantBounds

namespace Boundary
namespace LFunctions

noncomputable section

theorem boundaryRiemannHypothesis_eq_mathlib :
    boundaryRiemannHypothesis = RiemannHypothesis := rfl

theorem boundaryCompletedRiemannZeta_eq_mathlib :
    boundaryCompletedRiemannZeta = completedRiemannZeta := rfl

theorem boundaryRiemannZeta_eq_mathlib :
    boundaryRiemannZeta = riemannZeta := rfl

theorem finalRiemannHypothesis_canonicalAffinePacketData :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f :=
  fun f =>
    ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_canonicalPhiGamma_owner
      f
theorem finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε :=
  ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberDirectCenteredZeroTailSmallValuesRunge_owner
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hfinite
    hpartialLeft
    hcompactBoundary

theorem finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge_unconditional_owner :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      (∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            ρ ∉
              ZetaAdmissibleFunction.daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈
            ZetaAdmissibleFunction.autocorrelationSpectralEvalFiberZeroTailRealAbsValues
              S P f₀ ∧
            r < ε :=
  finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
    boundaryLineOneAbelPartialMajorant_from_realParam
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
    finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth_unconditional_owner
    (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      boundaryLineOneAbelPartialMajorant_from_realParam)
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact
theorem finalRiemannHypothesis_binetEndpointRestoredFiniteHeightContourInputs :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs :=
  Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner
theorem finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  poleClearedRightCriticalStripAdmissibleGrowth_owner hbranch hreflected

/- The Binet branch absorption is an owner theorem, so the RH-facing growth
   package does not need to expose it as a hypothesis.  The reflected tail
   envelope is likewise supplied by its canonical owner below; keeping this
   theorem separate makes the two analytic constructions visible in the
   dependency graph. -/
theorem finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth_canonical
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  poleClearedRightCriticalStripAdmissibleGrowth_owner
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
    hreflected

theorem finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth_unconditional_owner :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth_canonical
    poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_horizontalBounds
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_concreteControl_owner
    K
    pathData
    hConcrete
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyPacketData
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_packetData_owner
    K
    pathData
    packetData
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathComponentCauchyPacketData
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
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyPacketData
    K
    (canonicalScheduledPathCauchyData_of_componentData_owner
      K
      zetaData
      gammaData)
    packetData
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPacketData
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
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPathData_packetData_owner
    K
    zetaData
    gammaData
    packetData
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyData
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f)) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPacketData
    K zetaData gammaData finalRiemannHypothesis_canonicalAffinePacketData
theorem finalRiemannHypothesis_canonicalVariableCauchyPathData_of_carrierSeparationConstantBounds
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCarrierSeparationConstantBounds
          f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
          f (K f)) :
    (∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
        f (K f)) ×
    (∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
        f (K f)) :=
  ZetaAdmissibleFunction.canonicalScheduledVariableCauchyPathData_of_carrierSeparationConstantBounds_owner
    K zetaBounds gammaBounds

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalCarrierSeparationConstantBounds
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCarrierSeparationConstantBounds
          f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  let pairedData :=
    finalRiemannHypothesis_canonicalVariableCauchyPathData_of_carrierSeparationConstantBounds
      K zetaBounds gammaBounds
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPacketData
    K (fun f => (pairedData.1 f)) (fun f => (pairedData.2 f)) packetData
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_boundaryIdentification
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    hBoundary
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_physicalLogDerivControl
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_boundaryIdentification
    (zetaWeilAutocorrelationBoundaryIdentification_of_physicalLogDerivControl_owner
      hLog)
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_horizontalBounds
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_horizontalBounds_owner horizontalBounds

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_owner
    K
    carrierData

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K) :
    ZetaWeilQuadraticPositivity :=
  finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData
    K
    pathData.toCarrierCauchyData

theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_concreteControl
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_concreteControl_owner
    K
    pathData
    hConcrete

/-- Final centered-zero criterion wrapper for RH, using raw autocorrelation Weil positivity.

This bridge assembles the zero-tail separator and the raw positivity theorem. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_horizontalBounds
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  let hPositivity : ZetaWeilQuadraticPositivity :=
    finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_horizontalBounds
      horizontalBounds
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    hPositivity

/-- The final RH wrapper is thin once the canonical horizontal analytic bounds
have been constructed at their owner level. -/
theorem boundaryRiemannHypothesis_of_horizontalBounds_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_horizontalBounds horizontalBounds)

/-- Endpoint reserve and boundary identification give the Boundary RH
statement. -/
theorem boundaryRiemannHypothesis_of_endpointReserve_boundaryIdentification_owner
    (reserveDomination : FinalEndpointTraceReserveDomination)
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion reserveDomination hBoundary)

/-- Boundary identification gives the centered-zero criterion after consuming
the owned endpoint reserve theorem. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_boundaryIdentification_owner
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion
    finalRiemannHypothesis_endpointTraceReserveDomination_owner
    hBoundary

/-- Boundary identification gives the Boundary RH statement after consuming
the owned endpoint reserve theorem. -/
theorem boundaryRiemannHypothesis_of_ownedEndpointReserve_boundaryIdentification_owner
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_boundaryIdentification_owner
      hBoundary)

/-- Completed-boundary identification gives the centered-zero criterion after
consuming the owned endpoint reserve theorem. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_completedBoundaryIdentification_owner
    (hBoundary : ZetaWeilAutocorrelationCompletedBoundaryIdentification) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_completedBoundary
    finalRiemannHypothesis_endpointTraceReserveDomination_owner
    hBoundary

/-- Completed-boundary identification gives the Boundary RH statement after
consuming the owned endpoint reserve theorem. -/
theorem boundaryRiemannHypothesis_of_ownedEndpointReserve_completedBoundaryIdentification_owner
    (hBoundary : ZetaWeilAutocorrelationCompletedBoundaryIdentification) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_completedBoundaryIdentification_owner
      hBoundary)

/-- Global completed-log-derivative factor-bound data is the narrow analytic
sink for the Trace-Bessel final RH route. -/
theorem boundaryRiemannHypothesis_of_globalLogDerivFactorBoundData_owner
    (globalFactorData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalTransform_logDerivFactorBoundData_packet_owner
    globalFactorData

/-- Separate global zeta-side and inverse-Gamma log-derivative bound data give
the same Trace-Bessel final RH route. -/
theorem boundaryRiemannHypothesis_of_globalLogDerivBoundData_owner
    (zetaData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalTransform_logDerivBoundData_packet_owner
    zetaData
    gammaData

theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_horizontalBounds_owner
    carrierData.horizontalBoundsFamily

theorem boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyData_owner
    K
    pathData.toCarrierCauchyData

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_concreteControl
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  let hPositive : ZetaWeilQuadraticPositivity :=
    finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_concreteControl
      K
      pathData
      hConcrete
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    hPositive

/-- Variable-local component path-Cauchy data and affine packet data give the
centered-zero criterion. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledVariableCauchyPacketData
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
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  let hPositive : ZetaWeilQuadraticPositivity :=
    finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPacketData
      K
      zetaData
      gammaData
      packetData
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    hPositive

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledVariableCauchyData
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f)) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 → s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledVariableCauchyPacketData
    K zetaData gammaData finalRiemannHypothesis_canonicalAffinePacketData

/-- Canonical local carrier separation and constant bounds give the centered-
zero criterion. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalCarrierSeparationConstantBounds
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCarrierSeparationConstantBounds
          f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 := by
  let pairedData :=
    ZetaAdmissibleFunction.canonicalScheduledVariableCauchyPathData_of_carrierSeparationConstantBounds_owner
      K zetaBounds gammaBounds
  let hPositive : ZetaWeilQuadraticPositivity :=
    finalRiemannHypothesis_zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPacketData
      K
      (fun f => (pairedData f).1)
      (fun f => (pairedData f).2)
      packetData
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    hPositive

theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalCarrierSeparationConstantBounds_canonicalPacket
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCarrierSeparationConstantBounds
          f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
          f (K f)) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 → s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_canonicalCarrierSeparationConstantBounds
    K zetaBounds gammaBounds finalRiemannHypothesis_canonicalAffinePacketData

theorem boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_concreteControl
      K
      pathData
      hConcrete)

theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_concreteControl_owner
    K
    carrierData.pathData
    hConcrete

/-- Path-Cauchy data and zero-excised factor-bound data give the centered-zero
criterion through the concrete log-derivative owner. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_factorBoundData
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (data :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_concreteControl
    K
    pathData
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorBoundData_owner
      data)

/-- Path-Cauchy data and zero-excised factor-bound data give the Boundary RH
statement through the concrete log-derivative owner. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_factorBoundData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (data :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_factorBoundData
      K
      pathData
      data)

/-- Carrier Cauchy data and zero-excised factor-bound data give the Boundary RH
statement through the path-data conversion. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyData_factorBoundData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (data :
      ∀ (a b : ℝ)
        (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b),
          ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData E) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_factorBoundData_owner
    K
    carrierData.pathData
    data

/-- Path-Cauchy data and explicit zero-excised strip boundedness give the
centered-zero criterion through the concrete log-derivative owner. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_boundedLogDeriv
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hboundedZeta : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖ZetaAdmissibleFunction.zetaSideNegLogDeriv z‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier))
    (hboundedGamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_concreteControl
    K
    pathData
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_owner
      hboundedZeta
      hboundedGamma)

/-- Path-Cauchy data and explicit zero-excised strip boundedness give the
Boundary RH statement through the concrete log-derivative owner. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_boundedLogDeriv_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hboundedZeta : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖ZetaAdmissibleFunction.zetaSideNegLogDeriv z‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier))
    (hboundedGamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledPathCauchyData_boundedLogDeriv
      K
      pathData
      hboundedZeta
      hboundedGamma)

/-- Carrier Cauchy data and explicit zero-excised strip boundedness give the
Boundary RH statement through the path-data conversion. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledCarrierCauchyData_boundedLogDeriv_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hboundedZeta : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖ZetaAdmissibleFunction.zetaSideNegLogDeriv z‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier))
    (hboundedGamma : ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      BddAbove
        ((fun z : ℂ =>
            ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
                (Complex.Gammaℝ z)⁻¹‖ /
              (1 + ‖z.im‖) ^ N) '' E.carrier)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledPathCauchyData_boundedLogDeriv_owner
    K
    carrierData.pathData
    hboundedZeta
    hboundedGamma

/-- Variable-local component path-Cauchy data and affine packet data give the
Boundary RH statement. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledVariableCauchyPacketData_owner
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
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_centeredZeroCriterion
    (finalRiemannHypothesis_centeredZeroCriterion_of_canonicalScheduledVariableCauchyPacketData
      K
      zetaData
      gammaData
      packetData)

/-- Boundary RH from variable-local Cauchy data with the canonical Phi/Gamma
packet supplied by its owner. -/
theorem boundaryRiemannHypothesis_of_canonicalScheduledVariableCauchyData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalScheduledVariableCauchyPacketData_owner
    K zetaData gammaData finalRiemannHypothesis_canonicalAffinePacketData

/-- Canonical local carrier separation and constant bounds give the Boundary
RH statement through the variable Cauchy path route. -/
theorem boundaryRiemannHypothesis_of_canonicalCarrierSeparationConstantBounds_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCarrierSeparationConstantBounds
          f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    boundaryRiemannHypothesis := by
  let pairedData :=
    ZetaAdmissibleFunction.canonicalScheduledVariableCauchyPathData_of_carrierSeparationConstantBounds_owner
      K zetaBounds gammaBounds
  exact
    boundaryRiemannHypothesis_of_canonicalScheduledVariableCauchyPacketData_owner
      K
      (fun f => (pairedData f).1)
      (fun f => (pairedData f).2)
      packetData

theorem boundaryRiemannHypothesis_of_canonicalCarrierSeparationConstantBounds_canonicalPacket_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCarrierSeparationConstantBounds
          f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
          f (K f)) :
    boundaryRiemannHypothesis :=
  boundaryRiemannHypothesis_of_canonicalCarrierSeparationConstantBounds_owner
    K zetaBounds gammaBounds finalRiemannHypothesis_canonicalAffinePacketData

end
end LFunctions
end Boundary
