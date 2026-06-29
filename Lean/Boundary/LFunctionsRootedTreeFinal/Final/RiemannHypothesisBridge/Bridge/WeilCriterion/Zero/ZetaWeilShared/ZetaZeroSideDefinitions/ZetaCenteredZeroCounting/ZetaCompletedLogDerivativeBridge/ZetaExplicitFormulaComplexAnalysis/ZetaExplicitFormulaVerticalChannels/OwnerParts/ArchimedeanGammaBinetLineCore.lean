import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetInversion

/-!
# Archimedean Gamma/Binet line values

This file owns the remaining archimedean Gamma/Binet owner value wrappers.  The
kernel, majorant, and transport layers live in smaller upstream owner files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Line-core assembly from the two direct scheduled affine inputs.

This is the last algebraic layer before the owner contour theorem.  The inputs
are deliberately scheduled affine-window statements, not whole-line
inverse-Gamma normalizations and not downstream Gamma/Binet line values:

* the right affine window has value `Phi f 0`;
* the right-minus-left affine window has the archimedean contribution.

From these, the left affine value is forced by subtraction, and the paired
affine values transport across the Binet decomposition to the paired
Gamma/Binet full-transform contour values. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_directAffineInputs_ownerGammaBinetContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hdifference :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t) -
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffineScheduled_and_affineDifference
      f F h hcoh hright hdifference

/-- Line-core assembly from the direct right scheduled affine value and the
archimedean vertical-channel value. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffine_and_verticalChannel_ownerGammaBinetContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffineScheduled_and_verticalChannel
      f F h hcoh hright hchannel

/-- Owner scheduled right/left Gamma/Binet coupled full-transform contour values.

The ordinary admissible test function has no built-in evenness or
autocorrelation symmetry, so the Binet main and differentiated-remainder
channels are not owner-level scalar values separately.  The canonical analytic
leaf is the coupled fixed-vertical Gamma/Binet transform, where the Binet
decomposition is recombined before taking the contour limit. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_ownerGammaBinetContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_ownerInversion
      f F h hcoh

/-- Projection of the scheduled right coupled Gamma/Binet full-transform contour value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledValue_ownerGammaBinetContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_ownerGammaBinetContour
      f F h hcoh).1

/-- Projection of the scheduled shifted-left coupled Gamma/Binet full-transform contour value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledValue_ownerGammaBinetContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_ownerGammaBinetContour
      f F h hcoh).2

/-- Owner paired scheduled Gamma/Binet full-transform values.

The right and shifted-left scheduled contour deformations use the same
branch-coherent Binet normalization.  Keeping the owner statement paired
prevents the two orientations from becoming independent public assumptions. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    And.intro
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledValue_ownerGammaBinetContour
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledValue_ownerGammaBinetContour
        f F h hcoh)

/-- Owner scheduled right Gamma/Binet full-transform value.

This is the right-orientation contour-deformation assertion before exhaustion
is transported to the whole line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledValue_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_sourceGammaBinetLineCore
      f F h hcoh).1

/-- Owner scheduled shifted-left Gamma/Binet full-transform value.

This is the shifted-left orientation of the same branch-coherent contour
deformation, before exhaustion is transported to the whole line. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledValue_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_sourceGammaBinetLineCore
      f F h hcoh).2

/-- Paired named whole-line Gamma/Binet transform values, obtained by
transporting the scheduled contour-deformation values through the whole-line
exhaustion lemmas. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransformIntegral_pair_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
        f F.toContourFamily =
      zetaCompletedExplicitFormulaPhi f 0 ∧
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
        f F.toContourFamily =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hright_integral :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_scheduledFullTransform
      f F h
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledValue_sourceGammaBinetLineCore
        f F h hcoh)
  have hleft_regular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  have hleft_integral :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_scheduledFullTransform
      f F h hleft_regular
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledValue_sourceGammaBinetLineCore
        f F h hcoh)
  constructor
  · exact
      Eq.trans
        (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral_eq
          f F.toContourFamily)
        hright_integral
  · exact
      Eq.trans
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral_eq
          f F.toContourFamily)
        hleft_integral

/-- Main-plus-remainder form of the paired whole-line Gamma/Binet transform
values, obtained by definitional transport from the named integral owner
theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_integral_pair_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0) ∧
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0)) := by
  have hpair :
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
          f F.toContourFamily =
        zetaCompletedExplicitFormulaPhi f 0 ∧
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
          f F.toContourFamily =
        -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransformIntegral_pair_sourceGammaBinetLineCore
      f F h hcoh
  exact
    ⟨zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_namedIntegralValue
        f F hpair.1,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_namedIntegralValue
        f F hpair.2⟩

/-- Owner analytic projection: whole-line full right Binet transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_integral_pair_sourceGammaBinetLineCore
      f F h hcoh).1

/-- Owner analytic projection: whole-line full shifted-left Binet transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_sourceGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_integral_pair_sourceGammaBinetLineCore
      f F h hcoh).2

/-- Scheduled full right Binet transform value from the current whole-line
source theorem.

The whole-line source theorem is the coupled main-plus-remainder value.  This
wrapper only transports that value through scheduled-window exhaustion; it is
not an independent Gamma/Binet inversion proof. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_of_integral_eq
      f F h
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_sourceGammaBinetLineCore
        f F h hcoh)

/-- Scheduled full shifted-left Binet transform value from the current
whole-line source theorem.

As on the right, this is scheduled-window transport from the source theorem,
not an independent proof of the shifted Gamma/Binet inversion leaf. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_of_integral_eq
      f F h hregular
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_sourceGammaBinetLineCore
        f F h hcoh)

/-- Scheduled right affine Gamma/Binet value from the scheduled coupled
Gamma/Binet full-transform value.

This is only window-level transport across the pointwise Binet decomposition.
It is deliberately oriented from the scheduled full-transform owner leaf to
the affine line value, not conversely. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  have hA_eq_S : A = S := by
    funext u
    have hmain :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hremainder :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hpoint :
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily) =ᵐ[
            volume.restrict
              (Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily hcoh t)
    calc
      A u =
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t := by
        exact integral_congr_ae hpoint
      _ = S u := by
        exact integral_add hmain hremainder
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
      hA_eq_S.symm
      hscheduled

/-- Scheduled shifted-left affine Gamma/Binet value from the scheduled
coupled shifted-left Gamma/Binet full-transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hA_eq_S : A = S := by
    funext u
    have hmain :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hremainder :
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
    have hpoint :
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily) =ᵐ[
            volume.restrict
              (Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily hregular hcoh t)
    calc
      A u =
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t := by
        exact integral_congr_ae hpoint
      _ = S u := by
        exact integral_add hmain hremainder
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
      hA_eq_S.symm
      hscheduled

/-- Paired scheduled affine Gamma/Binet values transported from the paired
scheduled Binet full-transform owner.

This theorem contains only window-level Binet-decomposition transport.  The
contour-deformation content remains in
`zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_sourceGammaBinetLineCore`. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    ⟨zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_scheduledFullTransform
        f F h hcoh hscheduled.1,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_scheduledFullTransform
        f F h hcoh hscheduled.2⟩

/-- Owner paired scheduled affine Gamma/Binet values. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_scheduledFullTransform
      f F h hcoh
      (zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_sourceGammaBinetLineCore
        f F h hcoh)

/-- Whole-line full right Binet transform value.

This delegates to the coupled source theorem above and keeps the downstream
public name stable.  It does not assert a separate value for either Binet
summand. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_sourceGammaBinetLineCore
      f F h hcoh

/-- Whole-line full shifted-left Binet transform value.

This delegates to the coupled shifted-left source theorem above.  The finite
Gamma-recurrence shift remains part of the coupled Binet value, not a
downstream algebraic correction. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_sourceGammaBinetLineCore
      f F h hcoh

/-- Whole-line value of the right Gamma/Binet archimedean affine line.

This is an algebraic wrapper over the coupled Binet full-transform value and
the pointwise Binet decomposition of the affine kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_ownerGammaBinetLineCore
      f F h hcoh
  exact Eq.trans hdecomp hvalue

/-- Whole-line value of the shifted-left Gamma/Binet archimedean affine line.

This is the shifted-left wrapper over the coupled Binet full-transform value
and the pointwise shifted-Binet decomposition of the affine kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  have hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_ownerGammaBinetLineCore
      f F h hcoh
  exact Eq.trans hdecomp hvalue

/-- The right coupled Gamma/Binet full-transform source value is equivalent to
the whole-line right archimedean affine value.

This is only a bookkeeping equivalence across the pointwise Binet
decomposition.  It is useful for audits: an independent affine proof can close
the Gamma/Binet source leaf, but a proof routed through inverse-Gamma
one-sided values is cyclic because those one-sided values already consume this
owner theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_iff_affineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0) ↔
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  constructor
  · intro hbinet
    have hdecomp :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t :=
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
        f F h hcoh
    exact Eq.trans hdecomp hbinet
  · intro haffine
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue
        f F h hcoh haffine

/-- The shifted-left coupled Gamma/Binet full-transform source value is
equivalent to the whole-line left archimedean affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_iff_affineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0)) ↔
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  constructor
  · intro hbinet
    have hdecomp :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t :=
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
        f F h hcoh
    exact Eq.trans hdecomp hbinet
  · intro haffine
    exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue
        f F h hcoh haffine

/-- The coupled right/shifted-left Gamma/Binet whole-line values are
equivalent to the paired right/shifted-left affine whole-line values.

This is the exact algebraic boundary between the Binet-decomposition layer and
the remaining analytic owner evaluation.  It is deliberately paired: the
ordinary admissible function does not make the individual Binet summands into
separate canonical value leaves. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_integral_pair_iff_affineKernel_integral_pair_ownerGammaBinetLineCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0) ∧
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0))) ↔
    (((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0) ∧
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0))) := by
  constructor
  · intro hbinet
    have hright :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) =
          zetaCompletedExplicitFormulaPhi f 0 :=
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_iff_affineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
        f F h hcoh).mp hbinet.1
    have hleft :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) =
          -(zetaCompletedExplicitFormulaPhi f 0) :=
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_iff_affineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
        f F h hcoh).mp hbinet.2
    exact And.intro hright hleft
  · intro haffine
    have hright :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t =
          zetaCompletedExplicitFormulaPhi f 0 :=
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_iff_affineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
        f F h hcoh).mpr haffine.1
    have hleft :
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t =
          -(zetaCompletedExplicitFormulaPhi f 0) :=
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_iff_affineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
        f F h hcoh).mpr haffine.2
    exact And.intro hright hleft

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
