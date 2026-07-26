import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffinePhysicalBoundaryCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.NormalizedSignedBoundary
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineInverseGammaShift
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.NormalizedContourResidueLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftKernelReflection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelFourierValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightVonMangoldtInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AutocorrelationPrimeNormalization
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedLogDerivativeCore.Owner

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

theorem zetaCompletedRightAffineKernel_integrable_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family)
      (volume : Measure ℝ) :=
  let primeIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family)
        (volume : Measure ℝ) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
      probe family analyticPackage
  have inverseGammaIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family)
        (volume : Measure ℝ) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
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

theorem zetaCompletedLeftAffineKernel_integrable_of_verticallyRegular_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        probe family.toContourFamily) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
        probe family.toContourFamily)
      (volume : Measure ℝ) :=
  let reflectedIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family.toContourFamily)
        (volume : Measure ℝ) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
      probe family analyticPackage
  let pointEquality : ∀ t : ℝ,
      ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
          probe family.toContourFamily t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family.toContourFamily t :=
    fun t : ℝ =>
      let logarithmicDerivativeReflection :
          ZetaAdmissibleFunction.completedZetaNegLogDeriv
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftAffineLine
                family.toContourFamily t) =
            -ZetaAdmissibleFunction.completedZetaNegLogDeriv
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightAffineLine
                family.toContourFamily (-t)) :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
          family.toContourFamily t
      congrArg
        (fun factor : ℂ =>
          factor *
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
                family.toContourFamily t))
        logarithmicDerivativeReflection
  let functionEquality :
      ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
          probe family.toContourFamily =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe family.toContourFamily :=
    funext pointEquality
  Eq.subst
    (motive := fun kernel : ℝ → ℂ =>
      Integrable kernel (volume : Measure ℝ))
    functionEquality.symm
    reflectedIntegrable

/-- Direct integrability of the reflected inverse-Gamma kernel from the
finite Abel--Plana right-line logarithmic-derivative bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_direct_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family) :
    Integrable
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        probe family)
      (volume : Measure ℝ) :=
  match
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      family with
  | ⟨bound, boundNonnegative, factorBound⟩ =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_right_factor_bound
        probe family analyticPackage bound boundNonnegative factorBound

/-- Fubini exchange for the reflected von Mangoldt term kernels. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integrals_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family) :
    (∫ t : ℝ,
      ∑' n : ℕ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          probe family n t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t :=
  let measurableTerms :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun t : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t)
          (volume : Measure ℝ) :=
    fun n : ℕ =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_aestronglyMeasurable
        probe family analyticPackage n
  let finiteNormIntegralSum :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_ne_top
      probe family analyticPackage
  MeasureTheory.integral_tsum measurableTerms finiteNormIntegralSum

theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integrals_of_phiControl_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl probe) :
    (∫ t : ℝ,
      ∑' n : ℕ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          probe family n t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t :=
  let measurableTerms :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun t : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t)
          (volume : Measure ℝ) :=
    fun n : ℕ =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_aestronglyMeasurable_of_phiControl
        probe family hPhi n
  let finiteNormIntegralSum :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_ne_top_of_phiControl
      probe family hPhi
  MeasureTheory.integral_tsum measurableTerms finiteNormIntegralSum

/-- Subtraction of two two-term packets groups the first coordinates and the
second coordinates separately. -/
theorem completedAffinePacket_sub_packet_eq_coordinate_sub_add_coordinate_sub
    (rightArithmetic rightGamma leftArithmetic leftGamma : ℂ) :
    (rightArithmetic + rightGamma) - (leftArithmetic + leftGamma) =
      (rightArithmetic - leftArithmetic) +
        (rightGamma - leftGamma) :=
  let subtractAsAdd :
      (rightArithmetic + rightGamma) - (leftArithmetic + leftGamma) =
        (rightArithmetic + rightGamma) +
          (-(leftArithmetic + leftGamma)) :=
    sub_eq_add_neg
        (rightArithmetic + rightGamma)
        (leftArithmetic + leftGamma)
  let negatedPacket :
      (rightArithmetic + rightGamma) +
          (-(leftArithmetic + leftGamma)) =
        (rightArithmetic + rightGamma) +
          ((-leftArithmetic) + (-leftGamma)) :=
    congrArg
        (fun value : ℂ => rightArithmetic + rightGamma + value)
        (neg_add leftArithmetic leftGamma)
  let reassociateRight :
      (rightArithmetic + rightGamma) +
          ((-leftArithmetic) + (-leftGamma)) =
        rightArithmetic +
          (rightGamma + ((-leftArithmetic) + (-leftGamma))) :=
    add_assoc
        rightArithmetic rightGamma ((-leftArithmetic) + (-leftGamma))
  let middleEquality :
          rightGamma + ((-leftArithmetic) + (-leftGamma)) =
            (-leftArithmetic) + (rightGamma + (-leftGamma)) :=
    Eq.trans
      (add_assoc rightGamma (-leftArithmetic) (-leftGamma)).symm
      (Eq.trans
        (congrArg
              (fun value : ℂ => value + (-leftGamma))
              (add_comm rightGamma (-leftArithmetic)))
        (add_assoc (-leftArithmetic) rightGamma (-leftGamma)))
  let commuteMiddle :
      rightArithmetic +
          (rightGamma + ((-leftArithmetic) + (-leftGamma))) =
        rightArithmetic +
          ((-leftArithmetic) + (rightGamma + (-leftGamma))) :=
    congrArg (fun value : ℂ => rightArithmetic + value) middleEquality
  let finalReassociate :
      rightArithmetic +
          ((-leftArithmetic) + (rightGamma + (-leftGamma))) =
        (rightArithmetic + (-leftArithmetic)) +
          (rightGamma + (-leftGamma)) :=
    (add_assoc
        rightArithmetic (-leftArithmetic) (rightGamma + (-leftGamma))).symm
  let restoreSubtractions :
      (rightArithmetic + (-leftArithmetic)) +
          (rightGamma + (-leftGamma)) =
        (rightArithmetic - leftArithmetic) +
          (rightGamma - leftGamma) :=
    congrArg₂ HAdd.hAdd
        (sub_eq_add_neg rightArithmetic leftArithmetic).symm
        (sub_eq_add_neg rightGamma leftGamma).symm
  Eq.trans subtractAsAdd
    (Eq.trans negatedPacket
      (Eq.trans reassociateRight
        (Eq.trans commuteMiddle
          (Eq.trans finalReassociate restoreSubtractions))))

/-- The completed full-line right-minus-left integral separates, after left
reflection, into the coupled arithmetic packet and the coupled inverse-Gamma
packet. -/
theorem zetaCompletedAffineIntegral_eq_arithmetic_add_inverseGamma_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
        probe family.toContourFamily) :
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
          probe family.toContourFamily t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
          probe family.toContourFamily t =
      ((∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            probe family.toContourFamily t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family.toContourFamily n t) +
      ((∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            probe family.toContourFamily t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family.toContourFamily t) :=
  let contour : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    family.toContourFamily
  let rightArithmetic : ℝ → ℂ :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
      probe contour
  let rightGamma : ℝ → ℂ :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe contour
  let leftArithmetic : ℝ → ℂ := fun t : ℝ =>
    ∑' n : ℕ,
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
        probe contour n t
  let leftGamma : ℝ → ℂ :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
      probe contour
  have rightArithmeticIntegrable :
      Integrable rightArithmetic (volume : Measure ℝ) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integrable
      probe contour analyticPackage
  have rightGammaIntegrable :
      Integrable rightGamma (volume : Measure ℝ) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe contour analyticPackage
  have reflectedCompletedIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          probe contour)
        (volume : Measure ℝ) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
      probe family analyticPackage
  have leftGammaIntegrable :
      Integrable leftGamma (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_direct_owner
      probe contour analyticPackage
  have leftArithmeticEquality :
      leftArithmetic =
        fun t : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
              probe contour t -
            leftGamma t :=
    funext
      (fun t : ℝ =>
        let decomposition :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma_ownerSummable
            probe contour t
        Eq.trans
          (add_sub_cancel_right
            (leftArithmetic t)
            (leftGamma t)).symm
          (congrArg
            (fun value : ℂ => value - leftGamma t)
            decomposition.symm))
  have leftArithmeticIntegrable :
      Integrable leftArithmetic (volume : Measure ℝ) :=
    Eq.subst
      (motive := fun kernel : ℝ → ℂ =>
        Integrable kernel (volume : Measure ℝ))
      leftArithmeticEquality.symm
      (reflectedCompletedIntegrable.sub leftGammaIntegrable)
  have rightIntegralEquality :
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe contour t) =
        (∫ t : ℝ, rightArithmetic t) +
          ∫ t : ℝ, rightGamma t :=
    have pointEquality :
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe contour =
          fun t : ℝ => rightArithmetic t + rightGamma t :=
      funext
        (fun t : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_completedRightAffineKernel_eq_prime_add_inverseGamma
            probe contour t)
    Eq.trans
      (congrArg (fun kernel : ℝ → ℂ => ∫ t : ℝ, kernel t) pointEquality)
      (integral_add rightArithmeticIntegrable rightGammaIntegrable)
  have leftKernelEquality :
      ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe contour =
        fun t : ℝ => leftArithmetic t + leftGamma t :=
    funext
      (fun t : ℝ =>
        let reflection :
            ZetaAdmissibleFunction.completedZetaNegLogDeriv
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftAffineLine
                  contour t) =
              -ZetaAdmissibleFunction.completedZetaNegLogDeriv
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightAffineLine
                  contour (-t)) :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
            contour t
        let leftToReflected :
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe contour t =
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
                probe contour t :=
          congrArg
            (fun factor : ℂ =>
              factor *
                ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPhi probe
                  (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftCenteredAffineLine
                    contour t))
            reflection
        let reflectedDecomposition :=
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma_ownerSummable
            probe contour t
        Eq.trans leftToReflected reflectedDecomposition)
  have leftIntegralEquality :
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe contour t) =
        (∫ t : ℝ, leftArithmetic t) +
          ∫ t : ℝ, leftGamma t :=
    Eq.trans
      (congrArg (fun kernel : ℝ → ℂ => ∫ t : ℝ, kernel t) leftKernelEquality)
      (integral_add leftArithmeticIntegrable leftGammaIntegrable)
  have leftArithmeticIntegralExchange :
      (∫ t : ℝ, leftArithmetic t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe contour n t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integrals_owner
      probe contour analyticPackage
  calc
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe contour t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe contour t =
        ((∫ t : ℝ, rightArithmetic t) + ∫ t : ℝ, rightGamma t) -
          ((∫ t : ℝ, leftArithmetic t) + ∫ t : ℝ, leftGamma t) :=
      congrArg₂ HSub.hSub rightIntegralEquality leftIntegralEquality
    _ = ((∫ t : ℝ, rightArithmetic t) - ∫ t : ℝ, leftArithmetic t) +
          ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t) :=
      completedAffinePacket_sub_packet_eq_coordinate_sub_add_coordinate_sub
        (∫ t : ℝ, rightArithmetic t)
        (∫ t : ℝ, rightGamma t)
        (∫ t : ℝ, leftArithmetic t)
        (∫ t : ℝ, leftGamma t)
    _ = ((∫ t : ℝ, rightArithmetic t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                probe contour n t) +
          ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t) :=
      congrArg
        (fun arithmeticValue : ℂ =>
          arithmeticValue +
            ((∫ t : ℝ, rightGamma t) - ∫ t : ℝ, leftGamma t))
        (congrArg
          (fun leftValue : ℂ =>
            (∫ t : ℝ, rightArithmetic t) - leftValue)
          leftArithmeticIntegralExchange)

/-- The coupled right/reflected-right von Mangoldt packet has the raw natural
two-face boundary value. -/
theorem zetaCompletedExplicitFormulaCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_of_rightValue_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (rightValue :
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
          probe) :
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) -
      ∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
        probe :=
  have reflectedValue :
      (∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t) =
        -(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          probe) :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_reflectedBoundaryContribution
      probe family
  have twoFaceEquality :
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
            probe +
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
            probe =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          probe :=
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_eq_oneSided_add_reflectedBoundaryContribution
      probe).symm
  calc
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
            probe -
          (-(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
            probe)) :=
      congrArg₂ HSub.hSub rightValue reflectedValue
    _ = ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
          probe +
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          probe :=
      sub_neg_eq_add
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
          probe)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          probe)
    _ = ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          probe := twoFaceEquality

theorem zetaCompletedExplicitFormulaCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_of_analyticPackage_owner
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family) :
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) -
      ∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
        probe :=
  have rightValue :
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
          probe :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel_integral_eq_primeNaturalOneSidedContribution_direct_ownerInversion
      probe family analyticPackage
  zetaCompletedExplicitFormulaCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_of_rightValue_owner
    probe family rightValue

/-- The coupled right/reflected-right von Mangoldt packet has the raw natural
two-face boundary value on autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaAutocorrelationCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction :=
      ZetaAdmissibleFunction.convolutionAutocorrelation f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          probe family t) -
      ∑' n : ℕ,
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            probe family n t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
        probe :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  zetaCompletedExplicitFormulaCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_of_analyticPackage_owner
    probe family analyticPackage

/-- The coupled right/reflected-right inverse-Gamma packet is the centered
Hermitian archimedean distribution. -/
theorem zetaCompletedExplicitFormulaAutocorrelationCompletedAffineInverseGammaIntegral_eq_archimedean_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction :=
      ZetaAdmissibleFunction.convolutionAutocorrelation f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          probe family t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          probe family t =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        probe :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  have differenceIntegral :
      (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            probe family t) -
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              probe family t :=
    ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_sub
      probe family analyticPackage
  Eq.trans differenceIntegral.symm
    (ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel_integral_eq_archimedean_owner
      f hPhi hLog)

/-- The full-line completed right-minus-left value is the unnormalized affine
physical subchannel.  The explicit correction channel is not folded into this
packet; the correction-target owner normalizes it separately. -/
theorem zetaCompletedExplicitFormulaAutocorrelationCompletedAffineIntegral_eq_physical_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction :=
      ZetaAdmissibleFunction.convolutionAutocorrelation f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
      ZetaAdmissibleFunction.explicitFormulaTwoPi *
        zetaCompletedAffinePhysicalBoundaryChannel probe :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let regularFamily :
      ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily :=
    ZetaAdmissibleFunction.CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
      f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    regularFamily.toContourFamily
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let arithmeticValue : ℂ :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
      probe
  let archimedeanValue : ℂ :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution probe
  let boundary : ℂ :=
    zetaCompletedAffinePhysicalBoundaryChannel probe
  have packetDecomposition :=
    zetaCompletedAffineIntegral_eq_arithmetic_add_inverseGamma_owner
      probe regularFamily analyticPackage
  have arithmeticEquality :
      ((∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            probe family t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              probe family n t) =
        arithmeticValue :=
    zetaCompletedExplicitFormulaAutocorrelationCompletedAffineArithmeticIntegral_eq_twoFaceBoundary_owner
      f hPhi hLog
  have inverseGammaEquality :
      ((∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            probe family t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            probe family t) =
        archimedeanValue :=
    zetaCompletedExplicitFormulaAutocorrelationCompletedAffineInverseGammaIntegral_eq_archimedean_owner
      f hPhi hLog
  have packetValue :
      (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
        ∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
        arithmeticValue + archimedeanValue :=
    Eq.trans packetDecomposition
      (congrArg₂ HAdd.hAdd arithmeticEquality inverseGammaEquality)
  have arithmeticDivision :
      arithmeticValue / ZetaAdmissibleFunction.explicitFormulaTwoPi =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
          probe :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_div_twoPi_eq_primeContribution_autocorrelation
      f
  have boundaryEquality :
      boundary =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
            probe +
          archimedeanValue /
            ZetaAdmissibleFunction.explicitFormulaTwoPi :=
    Eq.refl
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
          probe +
        archimedeanValue /
          ZetaAdmissibleFunction.explicitFormulaTwoPi)
  have normalizedArithmeticArchimedean :
      (arithmeticValue + archimedeanValue) /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
        boundary :=
    calc
      (arithmeticValue + archimedeanValue) /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
          arithmeticValue / ZetaAdmissibleFunction.explicitFormulaTwoPi +
            archimedeanValue /
              ZetaAdmissibleFunction.explicitFormulaTwoPi :=
        add_div arithmeticValue archimedeanValue
          ZetaAdmissibleFunction.explicitFormulaTwoPi
      _ =
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
      _ = boundary := boundaryEquality.symm
  have arithmeticArchimedean :
      arithmeticValue + archimedeanValue =
        ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary :=
    have rightMultiplication :
        arithmeticValue + archimedeanValue =
          boundary * ZetaAdmissibleFunction.explicitFormulaTwoPi :=
      (div_eq_iff
        ZetaAdmissibleFunction.explicitFormulaTwoPi_ne_zero).mp
        normalizedArithmeticArchimedean
    Eq.trans rightMultiplication
      (mul_comm boundary ZetaAdmissibleFunction.explicitFormulaTwoPi)
  calc
    (∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t) -
      ∫ t : ℝ,
        ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t =
        arithmeticValue + archimedeanValue :=
      packetValue
    _ = ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary :=
      arithmeticArchimedean

end

end LFunctions
end Boundary
