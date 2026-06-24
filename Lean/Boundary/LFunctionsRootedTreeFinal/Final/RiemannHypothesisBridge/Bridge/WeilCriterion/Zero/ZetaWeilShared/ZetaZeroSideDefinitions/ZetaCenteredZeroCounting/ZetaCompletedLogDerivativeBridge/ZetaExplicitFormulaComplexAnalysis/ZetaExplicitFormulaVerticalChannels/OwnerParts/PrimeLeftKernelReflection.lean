import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineCenteredProductMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeAffineKernelEstimates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeScheduledChannels
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Reflected left prime kernel

This file owns the pointwise reflection algebra for the left prime
logarithmic-derivative affine kernel.  It deliberately stops before any
whole-line value theorem: the contour and Mellin/Fourier value proofs consume
these pointwise identities downstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- Reflected completed-log-derivative kernel carried by the left prime line.

This is the part that must later be split into the reflected right one-sided
von Mangoldt channel and the complementary prime kernel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (- completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Completed-log-derivative reflection on the affine left/right lines. -/
theorem zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    completedZetaNegLogDeriv
        (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      - completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)) := by
  exact Eq.trans
    (congrArg completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine
        F t))
    (completedZetaNegLogDeriv_one_sub
      (zetaCompletedExplicitFormulaRightAffineLine F (-t))
      (zetaCompletedExplicitFormulaRightAffineLine_ne_zero F (-t))
      (zetaCompletedExplicitFormulaRightAffineLine_ne_one F (-t))
      (zetaCompletedExplicitFormulaRightAffineLine_completedRiemannZeta_ne_zero
        F (-t)))

/-- Pointwise reflected form of the left prime logarithmic derivative.

This is the owner algebra behind the eventual split into a residue-free tail
and a reflected prime-complement term. -/
theorem explicitFormulaPrimeLogDerivative_leftAffineLine_eq_reflectedCompleted_sub_inverseGamma
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t) =
      - completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)) -
        inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t) := by
  have hreflect :
      completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t) =
        - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) :=
    zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
      F t
  calc
    explicitFormulaPrimeLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t) =
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t) -
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t) := by
      rfl
    _ =
        - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) -
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t))
        hreflect

/-- Pointwise reflected form of the full left prime affine kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_eq_reflectedCompleted_sub_inverseGamma_mul_phi
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t =
      (- completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) -
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
  calc
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t =
        explicitFormulaPrimeLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      rfl
    _ =
        (- completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)) -
            inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      exact congrArg
        (fun z : ℂ =>
          z *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (explicitFormulaPrimeLogDerivative_leftAffineLine_eq_reflectedCompleted_sub_inverseGamma
          F t)

/-- Pointwise split of the left prime affine kernel into the reflected
completed kernel and the left inverse-Gamma kernel.

This is still only algebra.  It is the canonical input for the later analytic
statement that the reflected completed kernel supplies the one-sided plus
complementary prime arithmetic contribution while the inverse-Gamma part is
handled by the archimedean channel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_eq_reflectedCompleted_sub_inverseGammaKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t =
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t -
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  let A : ℂ :=
    - completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine F (-t))
  let B : ℂ :=
    inverseGammaCompletionLogDeriv
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have hleft :
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t =
        (A - B) * Φ :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_eq_reflectedCompleted_sub_inverseGamma_mul_phi
      f F t
  have hsplit :
      (A - B) * Φ = A * Φ - B * Φ :=
    sub_mul A B Φ
  have htarget :
      A * Φ - B * Φ =
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            f F t -
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
    rfl
  exact hleft.trans (hsplit.trans htarget)

/-- Linear control of the reflected completed-log-derivative factor follows
from the corresponding control on the left affine line. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedFactor_bound_of_left_completed_bound
    (F : ExplicitFormulaContourFamily) (B : ℝ)
    (hbound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ∀ t : ℝ,
      ‖- completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ ≤
        B * (1 + ‖t‖) :=
  fun t : ℝ =>
    have hreflect :
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t) =
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) :=
      zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
        F t
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ B * (1 + ‖t‖))
      hreflect
      (hbound t)

/-- Majorant package for the reflected completed part of the left prime
kernel, assuming the owner-level factor measurability and the standard linear
bound inherited from the completed logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_majorantPackage_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    - completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine F (-t))
  have hA_bound :
      ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedFactor_bound_of_left_completed_bound
      F B hleft_bound
  have hpackage :
      ExplicitFormulaAffineKernelMajorantPackage
        (fun t : ℝ =>
          A t *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
      f F h A B hB_nonneg hfactor_meas hA_bound
  have hkernel :
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F := by
    funext t
    rfl
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        ExplicitFormulaAffineKernelMajorantPackage φ)
      hkernel
      hpackage

/-- Integrability of the reflected completed part of the left prime kernel from
the reflected factor measurability and linear completed-log-derivative bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_majorantPackage_of_factor_bound
    f F h B hB_nonneg hfactor_meas hleft_bound).integrable

/-- Restricted-window integrability of the reflected completed part of the
left prime kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_restrict_Icc_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B a b : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_factor_bound
    f F h B hB_nonneg hfactor_meas hleft_bound).mono_measure
      Measure.restrict_le_self

/-- Majorant package for the reflected completed part of the left prime kernel
on a vertically regular contour.  The completed-log-derivative linear bound is
the standard zero-excised strip bound, and measurability is owned by the
right-affine-line continuity theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_majorantPackage_of_verticallyRegular
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily) := by
  let E : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) :=
    zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
      F
  let B : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) E 1
  have hB_nonneg : 0 ≤ B :=
    le_of_lt
      (h.logderiv_control.zeroExcisedStripBoundConstant_pos
        (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) E 1)
  have hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine
              F.toContourFamily t)‖ ≤
          B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_of_verticallyRegular
      f F h
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F.toContourFamily (-t)))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCompletedNegLogDeriv_reflectedRightAffineLine_aestronglyMeasurable
      F.toContourFamily
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_majorantPackage_of_factor_bound
      f F.toContourFamily h B hB_nonneg hfactor_meas hleft_bound

/-- Integrability of the reflected completed part of the left prime kernel on a
vertically regular contour. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_majorantPackage_of_verticallyRegular
    f F h).integrable

/-- Restricted-window integrability of the reflected completed part on a
vertically regular contour. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_restrict_Icc_of_verticallyRegular
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
    f F h).mono_measure Measure.restrict_le_self

/-- Finite-window integral split of the left prime affine kernel into the
reflected completed kernel and the left inverse-Gamma kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_intervalIntegral_eq_reflectedCompleted_sub_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (a b : ℝ)
    (hreflected :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume.restrict (Set.Icc a b)))
    (hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume.restrict (Set.Icc a b))) :
    (∫ t in Set.Icc a b,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
      (∫ t in Set.Icc a b,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) -
        ∫ t in Set.Icc a b,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  let L : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F
  let R : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel f F
  let G : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F
  have hpoint : L = fun t : ℝ => R t - G t := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_eq_reflectedCompleted_sub_inverseGammaKernel
        f F t
  calc
    (∫ t in Set.Icc a b,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        ∫ t in Set.Icc a b, L t := by
      rfl
    _ = ∫ t in Set.Icc a b, R t - G t := by
      exact congrArg
        (fun φ : ℝ → ℂ => ∫ t in Set.Icc a b, φ t)
        hpoint
    _ =
        (∫ t in Set.Icc a b, R t) -
          ∫ t in Set.Icc a b, G t := by
      exact integral_sub hreflected hinverse

/-- Whole-line split of the left prime logarithmic-derivative affine kernel
into the reflected completed kernel and the left inverse-Gamma kernel.

This is the measure-theoretic form of the pointwise reflection identity.  It
does not evaluate either component; it only fixes the algebraic target for the
left-complement contour proof. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_reflectedCompleted_sub_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hreflected :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume : Measure ℝ))
    (hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  let L : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F
  let R : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel f F
  let G : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F
  have hpoint : L = fun t : ℝ => R t - G t := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_eq_reflectedCompleted_sub_inverseGammaKernel
        f F t
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        ∫ t : ℝ, L t := by
      rfl
    _ = ∫ t : ℝ, R t - G t := by
      exact congrArg
        (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t)
        hpoint
    _ =
        (∫ t : ℝ, R t) -
          ∫ t : ℝ, G t := by
      exact integral_sub hreflected hinverse

/-- Component-value assembly for the whole-line left prime
logarithmic-derivative affine kernel.

If the reflected completed component and the left inverse-Gamma component have
the stated whole-line values, then the unsplit left logarithmic-derivative
kernel carries the negative complementary natural prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_negativeComplement_of_reflectedCompleted_and_inverseGamma_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hreflected :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume : Measure ℝ))
    (hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ))
    (V G : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) = V)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) = G)
    (hcomponent :
      V - G =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            f F t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_reflectedCompleted_sub_inverseGamma
      f F hreflected hinverse
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            f F t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
      exact hsplit
    _ = V -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
      exact congrArg
        (fun z : ℂ =>
          z -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
        hreflected_value
    _ = V - G := by
      exact congrArg (fun z : ℂ => V - z) hinverse_value
    _ = -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
      exact hcomponent

/-- Scheduled-window split of the left prime logarithmic-derivative integral
into the reflected completed kernel and the left inverse-Gamma kernel. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_reflectedCompleted_sub_inverseGamma
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hreflected :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume.restrict
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T)))
    (hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume.restrict
          (Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T))) :
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_affineKernelIntegral
      f F h u)
    (zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_intervalIntegral_eq_reflectedCompleted_sub_inverseGamma
      f F
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T
      hreflected hinverse)

/-- Scheduled-window split with the reflected-completed and inverse-Gamma
window integrability supplied by their owner estimates. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_reflectedCompleted_sub_inverseGamma_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral f F h u =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) -
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  let a : ℝ := (-(F.rectangle (h.height_schedule.height u)).T)
  let b : ℝ := (F.rectangle (h.height_schedule.height u)).T
  have hreflected :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume.restrict (Set.Icc a b)) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_restrict_Icc_of_factor_bound
      f F h B a b hB_nonneg hfactor_meas hleft_bound
  have hinverse :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume.restrict (Set.Icc a b)) :=
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
      f F h hregular hcoh).mono_measure Measure.restrict_le_self
  exact
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_reflectedCompleted_sub_inverseGamma
      f F h u hreflected hinverse

/-- Scheduled left prime complement limit from reflected-completed and
inverse-Gamma whole-line component values.

This theorem owns only the scheduled-window assembly.  The analytic component
values remain explicit inputs: reflected-completed Mellin/complement inversion
and the left inverse-Gamma one-sided value. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_tendsto_neg_complement_of_reflectedCompleted_and_inverseGamma_values_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ))
    (hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖))
    (V G : ℂ)
    (hreflected_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) = V)
    (hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) = G)
    (hcomponent :
      V - G =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
          f F h u)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
      f F h u
  let Rw : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F t
  let Gw : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hreflected_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_factor_bound
      f F h B hB_nonneg hfactor_meas hleft_bound
  have hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
      f F h hregular hcoh
  have hreflected_tendsto :
      Tendsto Rw atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            f F t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F h.height_schedule.height
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F)
      h.height_schedule.cofinal
      hreflected_integrable
  have hinverse_tendsto :
      Tendsto Gw atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)) :=
    explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      F h.height_schedule.height
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      h.height_schedule.cofinal
      hinverse_integrable
  have hsub :
      Tendsto (fun u : ℝ => Rw u - Gw u) atTop
        (𝓝
          ((∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
              f F t) -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
                f F t)) :=
    hreflected_tendsto.sub hinverse_tendsto
  have hlimit_value :
      ((∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
        V - G := by
    calc
      ((∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
          V -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
                f F t := by
        exact congrArg
          (fun z : ℂ =>
            z -
              ∫ t : ℝ,
                zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
                  f F t)
          hreflected_value
      _ = V - G := by
        exact congrArg (fun z : ℂ => V - z) hinverse_value
  have hsub_value :
      Tendsto (fun u : ℝ => Rw u - Gw u) atTop (𝓝 (V - G)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => Rw u - Gw u) atTop (𝓝 z))
      hlimit_value
      hsub
  have hsub_complement :
      Tendsto (fun u : ℝ => Rw u - Gw u) atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => Rw u - Gw u) atTop (𝓝 z))
      hcomponent
      hsub_value
  have hS_eq :
      S = fun u : ℝ => Rw u - Gw u := by
    funext u
    exact
      zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_reflectedCompleted_sub_inverseGamma_of_factor_bound
        f F h u hregular hcoh B hB_nonneg hfactor_meas hleft_bound
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (-(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f))))
      hS_eq.symm
      hsub_complement

/-- Scheduled-window split for vertically regular contours.  This consumes the
standard zero-excised completed-log-derivative bound and the Gamma-regularity
implied by vertical regularity. -/
theorem zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_reflectedCompleted_sub_inverseGamma_of_verticallyRegular
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) (u : ℝ)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral
        f F.toContourFamily h u =
      (∫ t in Set.Icc
          (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
          (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) -
        ∫ t in Set.Icc
          (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
          (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
            f F.toContourFamily t := by
  let E : CompletedZetaZeroExcisedStrip
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) :=
    zetaCompletedExplicitFormulaLeftAffineLineZeroExcisedStrip_of_verticallyRegular
      F
  let B : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) E 1
  have hB_nonneg : 0 ≤ B :=
    le_of_lt
      (h.logderiv_control.zeroExcisedStripBoundConstant_pos
        (1 - F.toContourFamily.c) (1 - F.toContourFamily.c) E 1)
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hleft_bound :
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine
              F.toContourFamily t)‖ ≤
          B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivative_completed_factor_bound_of_verticallyRegular
      f F h
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          - completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F.toContourFamily (-t)))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCompletedNegLogDeriv_reflectedRightAffineLine_aestronglyMeasurable
      F.toContourFamily
  exact
    zetaCompletedExplicitFormulaPrimeScheduledLeftLogDerivativeIntegral_eq_reflectedCompleted_sub_inverseGamma_of_factor_bound
      f F.toContourFamily h u hregular hcoh B hB_nonneg hfactor_meas
      hleft_bound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
