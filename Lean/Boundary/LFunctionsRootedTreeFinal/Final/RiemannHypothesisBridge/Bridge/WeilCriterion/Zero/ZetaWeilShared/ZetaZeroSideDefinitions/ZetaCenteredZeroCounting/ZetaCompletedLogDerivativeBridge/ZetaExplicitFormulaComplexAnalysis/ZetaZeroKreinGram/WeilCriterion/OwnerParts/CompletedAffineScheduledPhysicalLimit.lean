import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalScheduledBoundaryLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffinePhysicalLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundary

/-!
# Completed affine scheduled physical limit

This owner connects the full completed-affine value theorem to the scheduled
package boundary theorem.  The scheduled endpoint is proved through the direct
affine right-minus-left channel, not through a second zero-side translation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Component integrability of the prime and inverse-Gamma right affine kernels
gives integrability of the completed right affine kernel. -/
theorem zetaCompletedRightAffineKernel_integrable_of_component_integrable_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (primeIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family)
        (volume : Measure ℝ))
    (inverseGammaIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family)
        (volume : Measure ℝ)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family)
      (volume : Measure ℝ) :=
  let sumIntegrable :
      Integrable
        (fun t : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              probe family t +
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              probe family t)
        (volume : Measure ℝ) :=
    primeIntegrable.add inverseGammaIntegrable
  let functionEquality :
      ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family =
        fun t : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              probe family t +
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              probe family t :=
    funext
      (fun t : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_completedRightAffineKernel_eq_prime_add_inverseGamma
          probe family t)
  Eq.subst
    (motive := fun kernel : ℝ → ℂ =>
      Integrable kernel (volume : Measure ℝ))
    functionEquality.symm
    sumIntegrable

/-- Integrability of the reflected completed left affine kernel gives
integrability of the completed left affine kernel. -/
theorem zetaCompletedLeftAffineKernel_integrable_of_reflected_integrable_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (reflectedIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family)
        (volume : Measure ℝ)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family)
      (volume : Measure ℝ) :=
  let pointEquality : ∀ t : ℝ,
      ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family t :=
    fun t : ℝ =>
      let logarithmicDerivativeReflection :
          Boundary.LFunctions.ZetaAdmissibleFunction.completedZetaNegLogDeriv
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftAffineLine
                family t) =
            -Boundary.LFunctions.ZetaAdmissibleFunction.completedZetaNegLogDeriv
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightAffineLine
                family (-t)) :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
          family t
      congrArg
        (fun factor : ℂ =>
          factor *
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
                family t))
        logarithmicDerivativeReflection
  let functionEquality :
      ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family :=
    funext pointEquality
  Eq.subst
    (motive := fun kernel : ℝ → ℂ =>
      Integrable kernel (volume : Measure ℝ))
    functionEquality.symm
    reflectedIntegrable

/-- A completed affine packet value with the standard prime normalization is
the physical affine boundary value. -/
theorem zetaCompletedAffineKernelIntegral_eq_physical_of_packet_value_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (arithmeticValue archimedeanValue : ℂ)
    (packetValue :
      (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
        arithmeticValue + archimedeanValue)
    (arithmeticDivision :
      arithmeticValue / ZetaAdmissibleFunction.explicitFormulaTwoPi =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
          probe)
    (boundaryEquality :
      zetaCompletedAffinePhysicalBoundaryChannel probe =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
            probe +
          archimedeanValue /
            ZetaAdmissibleFunction.explicitFormulaTwoPi) :
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
      ZetaAdmissibleFunction.explicitFormulaTwoPi *
        zetaCompletedAffinePhysicalBoundaryChannel probe :=
  let boundary : ℂ :=
    zetaCompletedAffinePhysicalBoundaryChannel probe
  let normalizedArithmeticArchimedean :
      (arithmeticValue + archimedeanValue) /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
        boundary :=
    let splitDivision :
        (arithmeticValue + archimedeanValue) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi =
          arithmeticValue / ZetaAdmissibleFunction.explicitFormulaTwoPi +
          archimedeanValue /
            ZetaAdmissibleFunction.explicitFormulaTwoPi :=
      add_div arithmeticValue archimedeanValue
        ZetaAdmissibleFunction.explicitFormulaTwoPi
    let replaceArithmetic :
        arithmeticValue / ZetaAdmissibleFunction.explicitFormulaTwoPi +
            archimedeanValue /
              ZetaAdmissibleFunction.explicitFormulaTwoPi =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
              probe +
          archimedeanValue /
            ZetaAdmissibleFunction.explicitFormulaTwoPi :=
      congrArg
        (fun value : ℂ =>
          value +
            archimedeanValue /
              ZetaAdmissibleFunction.explicitFormulaTwoPi)
        arithmeticDivision
    Eq.trans splitDivision
      (Eq.trans replaceArithmetic boundaryEquality.symm)
  let arithmeticArchimedean :
      arithmeticValue + archimedeanValue =
        ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary :=
    let rightMultiplication :
        arithmeticValue + archimedeanValue =
          boundary * ZetaAdmissibleFunction.explicitFormulaTwoPi :=
      (div_eq_iff
        ZetaAdmissibleFunction.explicitFormulaTwoPi_ne_zero).mp
        normalizedArithmeticArchimedean
    Eq.trans rightMultiplication
      (mul_comm boundary ZetaAdmissibleFunction.explicitFormulaTwoPi)
  Eq.trans packetValue arithmeticArchimedean

/-- The completed affine packet value follows from the packet decomposition and
the arithmetic and inverse-Gamma packet values. -/
theorem zetaCompletedAffineKernel_packet_value_of_component_values_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (arithmeticValue archimedeanValue : ℂ)
    (packetDecomposition :
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
      ((∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            probe family t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t) =
        arithmeticValue)
    (inverseGammaEquality :
      ((∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            probe family t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family t) =
        archimedeanValue) :
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
      arithmeticValue + archimedeanValue :=
  Eq.trans packetDecomposition
    (congrArg₂ HAdd.hAdd arithmeticEquality inverseGammaEquality)

/-- The inverse-Gamma packet value follows from its difference-kernel integral
identity and the archimedean value theorem. -/
theorem zetaCompletedAffineInverseGamma_packet_value_of_difference_kernel_value_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (differenceIntegral :
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
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          probe) :
    ((∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family t) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        probe :=
  Eq.trans differenceIntegral.symm archimedeanValue

/-- The canonical right von Mangoldt affine kernel is integrable. -/
theorem zetaAutocorrelationPhysicalRightPrimeAffineKernel_integrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
      (volume : Measure ℝ) :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    fullPackage

/-- The canonical right inverse-Gamma affine kernel is integrable. -/
theorem zetaAutocorrelationPhysicalRightInverseGammaAffineKernel_integrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
      (volume : Measure ℝ) :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    fullPackage

/-- The canonical reflected left completed affine kernel is integrable. -/
theorem zetaAutocorrelationPhysicalLeftReflectedCompletedAffineKernel_integrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
      (volume : Measure ℝ) :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  let regularFamily :
      ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily :=
    ZetaAdmissibleFunction.CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
      f
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
    (zetaAutocorrelationPhysicalProbe f)
    regularFamily
    fullPackage

/-- The canonical completed affine packet decomposes into arithmetic and
inverse-Gamma packets under log-derivative control. -/
theorem zetaAutocorrelationPhysicalAffinePacket_decomposition_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    let probe : ZetaAdmissibleFunction :=
      zetaAutocorrelationPhysicalProbe f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      zetaAutocorrelationPhysicalContourFamily f
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
            probe family t) :=
  let regularFamily :
      ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily :=
    ZetaAdmissibleFunction.CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
      f
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        regularFamily.toContourFamily :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  zetaCompletedAffineIntegral_eq_arithmetic_add_inverseGamma_owner
    (zetaAutocorrelationPhysicalProbe f)
    regularFamily
    fullPackage

/-- The canonical arithmetic affine packet has the natural two-face value under
log-derivative control. -/
theorem zetaAutocorrelationPhysicalArithmeticPacket_value_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    let probe : ZetaAdmissibleFunction :=
      zetaAutocorrelationPhysicalProbe f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      zetaAutocorrelationPhysicalContourFamily f
    ((∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) -
      ∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
        probe :=
  zetaCompletedExplicitFormulaAutocorrelationCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_owner
    f hPhi hLog

/-- The canonical inverse-Gamma difference kernel integrates to the difference
of the right and reflected-left inverse-Gamma affine packets. -/
theorem zetaAutocorrelationPhysicalInverseGammaDifference_integral_eq_sub_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    let probe : ZetaAdmissibleFunction :=
      zetaAutocorrelationPhysicalProbe f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      zetaAutocorrelationPhysicalContourFamily f
    (∫ t : ℝ,
      ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family t :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    fullPackage

/-- The canonical inverse-Gamma difference kernel has the Hermitian
archimedean value. -/
theorem zetaAutocorrelationPhysicalInverseGammaDifference_integral_eq_archimedean_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    let probe : ZetaAdmissibleFunction :=
      zetaAutocorrelationPhysicalProbe f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      zetaAutocorrelationPhysicalContourFamily f
    (∫ t : ℝ,
      ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        probe :=
  ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_archimedean_owner
    f hPhi hLog

/-- The canonical right completed affine kernel is integrable. -/
theorem zetaAutocorrelationPhysicalRightAffineKernel_integrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
      (volume : Measure ℝ) :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  zetaCompletedRightAffineKernel_integrable_owner
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    fullPackage

/-- The canonical left completed affine kernel is integrable. -/
theorem zetaAutocorrelationPhysicalLeftAffineKernel_integrable_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
      (volume : Measure ℝ) :=
  let fullPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f) :=
    zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog
  let regularFamily :
      ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily :=
    ZetaAdmissibleFunction.CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
      f
  zetaCompletedLeftAffineKernel_integrable_of_verticallyRegular_owner
    (zetaAutocorrelationPhysicalProbe f)
    regularFamily
    fullPackage

/-- The canonical completed affine full-line value is the physical boundary value. -/
theorem zetaAutocorrelationPhysicalAffineKernel_integral_eq_physical_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
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
            (zetaAutocorrelationPhysicalProbe f) :=
  zetaCompletedExplicitFormulaAutocorrelationCompletedAffineIntegral_eq_physical_owner
    f hPhi hLog

/-- The canonical scheduled affine channel tends to the physical boundary value. -/
theorem zetaAutocorrelationPhysicalScheduledAffineChannel_tendsto_physical_of_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          ((zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog).toScheduledFamilyAnalyticPackage.height_schedule.height
            u))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel
            (zetaAutocorrelationPhysicalProbe f))) :=
  zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    (zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog).toScheduledFamilyAnalyticPackage.height_schedule
    (zetaAutocorrelationPhysicalRightAffineKernel_integrable_of_logDerivControl_owner
      f hPhi hLog)
    (zetaAutocorrelationPhysicalLeftAffineKernel_integrable_of_logDerivControl_owner
      f hPhi hLog)
    (zetaAutocorrelationPhysicalAffineKernel_integral_eq_physical_of_logDerivControl_owner
      f hPhi hLog)

/-- The canonical scheduled package tends to the pole-corrected physical boundary
through the direct completed affine channel. -/
theorem zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affine_logDerivControl_owner
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaAdmissibleFunction.ZetaPhiAnalyticControl
        (zetaAutocorrelationPhysicalProbe f))
    (hLog :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
        (zetaAutocorrelationPhysicalProbe f)) :
    Tendsto
      (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
        f
        ((zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog).toScheduledFamilyAnalyticPackage))
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
    f
    ((zetaAutocorrelationPhysicalAnalyticPackage f hPhi hLog).toScheduledFamilyAnalyticPackage)
    (zetaAutocorrelationPhysicalScheduledAffineChannel_tendsto_physical_of_logDerivControl_owner
      f hPhi hLog)

end
end LFunctions
end Boundary
