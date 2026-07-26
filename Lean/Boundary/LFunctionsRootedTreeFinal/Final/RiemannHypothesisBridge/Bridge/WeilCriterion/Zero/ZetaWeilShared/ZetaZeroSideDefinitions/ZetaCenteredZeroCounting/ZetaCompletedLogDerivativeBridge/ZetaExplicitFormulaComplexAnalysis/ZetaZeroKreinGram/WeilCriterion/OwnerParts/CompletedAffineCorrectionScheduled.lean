import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineInverseGammaChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalScheduledBoundaryLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionVerticalConvergence

/-!
# Completed affine correction shift

Branch-free reflection and scheduled convergence of the elementary rational
correction channel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

open CleanAutocorrelationAnalyticPackage

/-- Conjugation commutes with the elementary rational correction. -/
theorem explicitFormulaCorrectionLogDerivative_star_shiftOwner
    (s : ℂ) :
    star (explicitFormulaCorrectionLogDerivative s) =
      explicitFormulaCorrectionLogDerivative (star s) :=
  let negativeOneStar : star (-1 : ℂ) = (-1 : ℂ) :=
    Eq.trans (star_neg (1 : ℂ))
      (congrArg Neg.neg (star_one (R := ℂ)))
  let oneStar : star (1 : ℂ) = (1 : ℂ) :=
    star_one (R := ℂ)
  let firstQuotient :
      star ((-1 : ℂ) / s) = (-1 : ℂ) / star s :=
    Eq.trans (star_div₀ (-1 : ℂ) s)
      (congrArg₂ HDiv.hDiv negativeOneStar rfl)
  let denominatorStar :
      star (s - 1) = star s - 1 :=
    Eq.trans (star_sub s (1 : ℂ))
      (congrArg (fun value : ℂ => star s - value) oneStar)
  let secondQuotient :
      star ((1 : ℂ) / (s - 1)) = 1 / (star s - 1) :=
    Eq.trans (star_div₀ (1 : ℂ) (s - 1))
      (congrArg₂ HDiv.hDiv oneStar denominatorStar)
  let unfoldLeft :
      star (explicitFormulaCorrectionLogDerivative s) =
        star (((-1 : ℂ) / s) - 1 / (s - 1)) :=
    congrArg star
        (explicitFormulaCorrectionLogDerivative_eq_poleCorrection s)
  let distributeStar :
      star (((-1 : ℂ) / s) - 1 / (s - 1)) =
        star ((-1 : ℂ) / s) - star (1 / (s - 1)) :=
    star_sub ((-1 : ℂ) / s) (1 / (s - 1))
  let quotientTransport :
      star ((-1 : ℂ) / s) - star (1 / (s - 1)) =
        (-1 : ℂ) / star s - 1 / (star s - 1) :=
    congrArg₂ HSub.hSub firstQuotient secondQuotient
  let foldRight :
      (-1 : ℂ) / star s - 1 / (star s - 1) =
        explicitFormulaCorrectionLogDerivative (star s) :=
    (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
      (star s)).symm
  Eq.trans unfoldLeft
    (Eq.trans distributeStar
      (Eq.trans quotientTransport foldRight))

/-- The elementary correction logarithmic derivative is odd about the
functional-equation center. -/
theorem explicitFormulaCorrectionLogDerivative_one_sub_eq_neg_shiftOwner
    (s : ℂ) :
    explicitFormulaCorrectionLogDerivative (1 - s) =
      -explicitFormulaCorrectionLogDerivative s :=
  let firstDenominator : (1 : ℂ) - s = -(s - 1) :=
    (neg_sub s 1).symm
  let secondDenominator : ((1 : ℂ) - s) - 1 = -s :=
    Eq.trans
      (sub_sub 1 s 1)
      (Eq.trans
        (congrArg (fun value : ℂ => 1 - value) (add_comm s 1))
        (Eq.trans
          (sub_sub 1 1 s).symm
          (Eq.trans
            (congrArg (fun value : ℂ => value - s) (sub_self 1))
            (zero_sub s))))
  let unfoldLeft :
      explicitFormulaCorrectionLogDerivative (1 - s) =
        (-1 : ℂ) / (1 - s) - 1 / ((1 - s) - 1) :=
    explicitFormulaCorrectionLogDerivative_eq_poleCorrection (1 - s)
  let denominatorTransport :
      (-1 : ℂ) / (1 - s) - 1 / ((1 - s) - 1) =
        (-1 : ℂ) / (-(s - 1)) - 1 / (-s) :=
    congrArg₂ HSub.hSub
        (congrArg (fun denominator : ℂ => (-1 : ℂ) / denominator)
          firstDenominator)
        (congrArg (fun denominator : ℂ => 1 / denominator)
          secondDenominator)
  let quotientTransport :
      (-1 : ℂ) / (-(s - 1)) - 1 / (-s) =
        1 / (s - 1) - (-(1 / s)) :=
    congrArg₂ HSub.hSub
        (neg_div_neg_eq (1 : ℂ) (s - 1))
        (one_div_neg_eq_neg_one_div s)
  let negativeQuotient :
      1 / (s - 1) - (-(1 / s)) =
        1 / (s - 1) - ((-1 : ℂ) / s) :=
    congrArg
        (fun value : ℂ => 1 / (s - 1) - value)
        (neg_div s 1).symm
  let swapSub :
      1 / (s - 1) - ((-1 : ℂ) / s) =
        -(((-1 : ℂ) / s) - 1 / (s - 1)) :=
    (neg_sub ((-1 : ℂ) / s) (1 / (s - 1))).symm
  let foldRight :
      -(((-1 : ℂ) / s) - 1 / (s - 1)) =
        -explicitFormulaCorrectionLogDerivative s :=
    congrArg Neg.neg
        (explicitFormulaCorrectionLogDerivative_eq_poleCorrection s).symm
  Eq.trans unfoldLeft
    (Eq.trans denominatorTransport
      (Eq.trans quotientTransport
        (Eq.trans negativeQuotient
          (Eq.trans swapSub foldRight))))

/-- Reflection of the right affine line converts the reflected rational
correction kernel exactly into the ordinary left correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_eq_leftAffineKernel_shiftOwner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        probe family t =
      zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
        probe family t :=
  let rightPoint : ℂ :=
    zetaCompletedExplicitFormulaRightAffineLine family (-t)
  let transformValue : ℂ :=
    zetaCompletedExplicitFormulaPhi probe
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t)
  let lineEquality :
      zetaCompletedExplicitFormulaLeftAffineLine family t =
        1 - rightPoint :=
    zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine
      family t
  let correctionEquality :
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine family t) =
        -(explicitFormulaCorrectionLogDerivative rightPoint) :=
    Eq.trans
      (congrArg explicitFormulaCorrectionLogDerivative lineEquality)
      (explicitFormulaCorrectionLogDerivative_one_sub_eq_neg_shiftOwner
        rightPoint)
  let unfoldLeft :
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        probe family t =
        (-(explicitFormulaCorrectionLogDerivative rightPoint)) *
          transformValue :=
    rfl
  let scalarTransport :
      (-(explicitFormulaCorrectionLogDerivative rightPoint)) *
          transformValue =
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine family t) *
          transformValue :=
    congrArg (fun value : ℂ => value * transformValue)
        correctionEquality.symm
  let foldRight :
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine family t) *
          transformValue =
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          probe family t :=
    rfl
  Eq.trans unfoldLeft
    (Eq.trans scalarTransport foldRight)

/-- Scheduled branch-free value of the coupled elementary correction
channel. -/
theorem zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_scheduledWindow_tendsto_standard_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    let analyticPackage :
        ExplicitFormulaFamilyAnalyticPackage probe family :=
      zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
        hLog
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(family.rectangle
              (analyticPackage.height_schedule.height u)).T)
            (family.rectangle
              (analyticPackage.height_schedule.height u)).T,
          zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
            probe family t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaCorrectionStandardContourContribution
          probe)) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let coupledWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(family.rectangle
          (analyticPackage.height_schedule.height u)).T)
        (family.rectangle
          (analyticPackage.height_schedule.height u)).T,
      zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
        probe family t
  let standardWindow : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionVerticalChannel
      probe family (analyticPackage.height_schedule.height u)
  let onePoleLimit :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            probe family (analyticPackage.height_schedule.height u))
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue
            probe family.c)) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_projection_direct_ownerOnePoleAffine
      probe family analyticPackage
  let standardLimit :
      Tendsto standardWindow atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe)) :=
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_concrete_ownerChannelTransportAnalytic
      probe family analyticPackage onePoleLimit
  let windowEquality : coupledWindow = standardWindow :=
    funext
      (fun u : ℝ =>
        let T : ℝ := analyticPackage.height_schedule.height u
        let window : Set ℝ :=
          Set.Icc (-(family.rectangle T).T) (family.rectangle T).T
        let coupledPointwise :
            zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
                probe family =
              fun t : ℝ =>
                zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                    probe family t -
                  zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                    probe family t :=
          funext
            (fun t : ℝ =>
              congrArg
                (fun value : ℂ =>
                  zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                      probe family t - value)
                  (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_eq_leftAffineKernel_shiftOwner
                    probe family t))
        let rightIntegrableOn :
            Integrable
              (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                probe family)
              ((volume : Measure ℝ).restrict window) :=
          (zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integrable_ownerGammaBinetLineValue
            probe family analyticPackage).integrableOn
        let reflectedIntegrableOn :
            Integrable
              (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
                probe family)
              ((volume : Measure ℝ).restrict window) :=
          (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_shiftOwner
            probe family analyticPackage).integrableOn
        let reflectedEquality :
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
                probe family =
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                probe family :=
          funext
            (fun t : ℝ =>
              zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_eq_leftAffineKernel_shiftOwner
                probe family t)
        let leftIntegrableOn :
            Integrable
              (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                probe family)
              ((volume : Measure ℝ).restrict window) :=
          Eq.subst
            (motive := fun function : ℝ → ℂ =>
              Integrable function
                ((volume : Measure ℝ).restrict window))
            reflectedEquality
            reflectedIntegrableOn
        let integralDifference :
            (∫ t in window,
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                  probe family t -
                zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                  probe family t) =
              (∫ t in window,
                zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                  probe family t) -
                ∫ t in window,
                  zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                    probe family t :=
          integral_sub rightIntegrableOn leftIntegrableOn
        let rightAffineToPath :
            (∫ t in window,
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                probe family t) =
              ∫ t in window,
                explicitFormulaCorrectionLogDerivative
                    (zetaCompletedExplicitFormulaRightPath
                      (family.rectangle T) t) *
                  zetaCompletedExplicitFormulaPhi probe
                    (zetaCompletedExplicitFormulaRightPath
                      (family.rectangle T) t - (1 / 2 : ℂ)) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc
            (fun t _membership =>
              let hline :
                  zetaCompletedExplicitFormulaRightAffineLine family t =
                    zetaCompletedExplicitFormulaRightPath
                      (family.rectangle T) t :=
                (zetaCompletedExplicitFormulaRightPath_rectangle_eq_rightAffineLine
                  family T t).symm
              let hcenter :
                  zetaCompletedExplicitFormulaRightCenteredAffineLine
                      family t =
                    zetaCompletedExplicitFormulaRightPath
                      (family.rectangle T) t - (1 / 2 : ℂ) :=
                zetaCompletedExplicitFormulaRightCenteredAffineLine_eq_rightPath_sub_half
                  family T t
              congrArg₂ HMul.hMul
                (congrArg explicitFormulaCorrectionLogDerivative hline)
                (congrArg (zetaCompletedExplicitFormulaPhi probe) hcenter))
        let leftAffineToPath :
            (∫ t in window,
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                probe family t) =
              ∫ t in window,
                explicitFormulaCorrectionLogDerivative
                    (zetaCompletedExplicitFormulaLeftPath
                      (family.rectangle T) t) *
                  zetaCompletedExplicitFormulaPhi probe
                    (zetaCompletedExplicitFormulaLeftPath
                      (family.rectangle T) t - (1 / 2 : ℂ)) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Icc
            (fun t _membership =>
              let hline :
                  zetaCompletedExplicitFormulaLeftAffineLine family t =
                    zetaCompletedExplicitFormulaLeftPath
                      (family.rectangle T) t :=
                (zetaCompletedExplicitFormulaLeftPath_rectangle_eq_leftAffineLine
                  family T t).symm
              let hcenter :
                  zetaCompletedExplicitFormulaLeftCenteredAffineLine
                      family t =
                    zetaCompletedExplicitFormulaLeftPath
                      (family.rectangle T) t - (1 / 2 : ℂ) :=
                zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_leftPath_sub_half
                  family T t
              congrArg₂ HMul.hMul
                (congrArg explicitFormulaCorrectionLogDerivative hline)
                (congrArg (zetaCompletedExplicitFormulaPhi probe) hcenter))
        let affineDifferenceToPath :
            ((∫ t in window,
                zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                  probe family t) -
              ∫ t in window,
                zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                  probe family t) =
              standardWindow u :=
          Eq.trans
            (congrArg₂ HSub.hSub rightAffineToPath leftAffineToPath)
            (Eq.refl (standardWindow u))
        Eq.trans
          (congrArg
            (fun integrand : ℝ → ℂ => ∫ t in window, integrand t)
            coupledPointwise)
          (Eq.trans integralDifference affineDifferenceToPath))
  Eq.subst
    (motive := fun window : ℝ → ℂ =>
      Tendsto window atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe)))
    windowEquality.symm
    standardLimit

/-- The whole-line coupled elementary correction packet has the standard
contour correction value. -/
theorem zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integral_eq_standard_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
        probe family t) =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution
        probe :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let correctionWindow : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(family.rectangle
          (analyticPackage.height_schedule.height u)).T)
        (family.rectangle
          (analyticPackage.height_schedule.height u)).T,
      zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
        probe family t
  let integralLimit :
      Tendsto correctionWindow atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
              probe family t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family
      analyticPackage.height_schedule.height
      (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel
        probe family)
      analyticPackage.height_schedule.cofinal
      (zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_integrable
        probe family analyticPackage)
  let standardLimit :
      Tendsto correctionWindow atTop
        (𝓝
          (zetaCompletedExplicitFormulaCorrectionStandardContourContribution
            probe)) :=
    zetaCompletedAffineCorrectionRightReflectedDifferenceKernel_scheduledWindow_tendsto_standard_owner
      f hPhi hLog
  tendsto_nhds_unique integralLimit standardLimit

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
