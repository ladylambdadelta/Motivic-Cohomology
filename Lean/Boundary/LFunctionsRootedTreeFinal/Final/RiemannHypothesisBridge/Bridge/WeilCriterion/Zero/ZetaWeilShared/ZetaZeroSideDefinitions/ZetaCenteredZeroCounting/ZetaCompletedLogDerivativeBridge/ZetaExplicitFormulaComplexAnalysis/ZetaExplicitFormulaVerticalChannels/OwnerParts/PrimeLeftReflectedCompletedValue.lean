import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftKernelReflection
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedInverseGammaComponents
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedBoundarySymmetryValues
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelFourierValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaOneSidedValues

/-!
# Reflected-left completed prime value

This file owns the whole-line value of the reflected completed-log-derivative
kernel on the left prime line.  The transport file consumes this theorem but
does not own its Mellin/Fourier inversion proof.
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

/-- The reflected completed kernel value target before subtracting the
one-sided inverse-Gamma value. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue
    (f : ZetaAdmissibleFunction) : ℂ :=
  -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) +
    zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f

/-- Algebraic recombination of the reflected completed value with the
one-sided inverse-Gamma value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue_sub_leftOneSidedInverseGammaValue
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  change (-C + G) - G = -C
  exact add_sub_cancel_right (-C) G

/-- Reflected-completed complement value from an independently proved unsplit
left logarithmic-derivative value.

This is the reverse algebra to the usual component assembly:
`left = reflected completed - inverseGamma`.  It is useful for a future direct
left-contour proof of the negative complement value, but it must not be fed by
the reflected-completed owner theorem below, or it would be circular. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_leftLogDerivativeValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  let R : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  let L : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
        f F.toContourFamily t
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hreflected_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integrable_of_verticallyRegular
      f F h
  have hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
      f F.toContourFamily h hregular hcoh
  have hinverse_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily t) = G :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_negPhiZero_add_correctionLeftValue_ownerOneSidedValues
      f F h hcoh
  have hsplit :
      L = R -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
            f F.toContourFamily t :=
    zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel_integral_eq_reflectedCompleted_sub_inverseGamma
      f F.toContourFamily hreflected_integrable hinverse_integrable
  have hsplit_scalar :
      L = R - G := by
    calc
      L = R -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
              f F.toContourFamily t := by
        exact hsplit
      _ = R - G := by
        exact congrArg (fun z : ℂ => R - z) hinverse_value
  calc
    R - G = L := by
      exact hsplit_scalar.symm
    _ = -C := by
      exact hleft_value

/-- Packaged reflected-completed value from an independently proved unsplit
left logarithmic-derivative complement value.

This is a thin scalar wrapper around
`zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_leftLogDerivativeValue`.
It records the direct-contour route to the reflected-completed owner value
without using the reflected-completed owner theorem itself. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_ownerReflectedCompletedValue_of_leftLogDerivativeValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f := by
  let A : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  have hsub :
      A - G = -C :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_leftLogDerivativeValue
      f F h hcoh hleft_value
  calc
    A = (A - G) + G := by
      exact (sub_add_cancel A G).symm
    _ = -C + G := by
      exact congrArg (fun z : ℂ => z + G) hsub
    _ = zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f := by
      rfl

/-- Reflected-completed complement value from the direct Mellin/complement
evaluation of the reflected completed kernel.

This is the final algebraic wrapper around the actual analytic theorem needed
here: the reflected completed-log-derivative kernel has whole-line value
`- complement + leftOneSidedInverseGammaValue`.  The analytic proof of that
input is the Mellin/Fourier expansion of the reflected completed logarithmic
derivative; this lemma only packages the scalar subtraction used by downstream
prime transport. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedCompletedValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  let A : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  calc
    A - G = (-C + G) - G := by
      exact congrArg (fun z : ℂ => z - G) hvalue
    _ = -C := by
      exact add_sub_cancel_right (-C) G

/-- Packaged reflected-completed owner value from the direct Mellin/complement
evaluation of the reflected completed kernel.

This is the value-form analogue of
`zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedCompletedValue`.
It is useful for consumers that want the named scalar
`zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_ownerReflectedCompletedValue_of_reflectedCompletedValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f := by
      exact hvalue
    _ = zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f := by
      rfl

/-- Reflected-completed complement value from a reflected term-sum expansion.

This is the exact algebra needed after the future reflected completed-kernel
Dirichlet expansion and sum-integral exchange theorem is proved.  The two
inputs are deliberately explicit:

* the completed reflected kernel expands to the reflected term-kernel sum plus
  the left one-sided inverse-Gamma scalar;
* the reflected term-kernel sum has value `- complementContribution`.

No Mellin inversion, summability, or sum-integral exchange is asserted here. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_tsum
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f)
    (hterm_tsum :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  let A : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let S : ℂ :=
    ∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F.toContourFamily n t
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  calc
    A - G = (S + G) - G := by
      exact congrArg (fun z : ℂ => z - G) hexpansion
    _ = S := by
      exact add_sub_cancel_right S G
    _ = -C := by
      exact hterm_tsum

/-- Whole-line reflected completed split from the pointwise reflected
Dirichlet/inverse-Gamma split and integrability of the two split summands.

This closes the measure-theoretic `integral_add` part of the split.  It does
not assert the reflected term-kernel sum-integral exchange. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_pointwise_summable_integrable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hterm :
      ∀ t : ℝ,
        Summable
          (fun n : ℕ =>
            LSeries.term (↗Λ)
              (zetaCompletedExplicitFormulaRightAffineLine
                F.toContourFamily (-t)) n))
    (hseries_integrable :
      Integrable
        (fun t : ℝ =>
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
        (volume : Measure ℝ))
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F.toContourFamily t := by
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        fun t : ℝ =>
          (∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_eq_tsum_termKernel_add_reflectedInverseGamma
        f F.toContourFamily t (hterm t)
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
        ∫ t : ℝ,
          (∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t := by
      exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hpoint
    _ =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t := by
      exact integral_add hseries_integrable hinverse_integrable

/-- Whole-line reflected completed split with pointwise Dirichlet summability
discharged by the affine-line von Mangoldt owner.

The remaining inputs are exactly the two integrability facts needed for
`integral_add`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_integrable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hseries_integrable :
      Integrable
        (fun t : ℝ =>
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
        (volume : Measure ℝ))
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F.toContourFamily t := by
  have hterm :
      ∀ t : ℝ,
        Summable
          (fun n : ℕ =>
            LSeries.term (↗Λ)
              (zetaCompletedExplicitFormulaRightAffineLine
                F.toContourFamily (-t)) n) :=
    fun t : ℝ =>
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtFactor_terms_complex_summable
        F.toContourFamily (-t)
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_pointwise_summable_integrable
      f F hterm hseries_integrable hinverse_integrable

/-- Completed reflected kernel expansion from a reflected completed split,
reflected term-kernel sum-integral exchange, and the reflected inverse-Gamma
value.

This theorem owns only scalar assembly.  The three inputs are the genuine
analytic leaves:
the reflected completed kernel splits into the reflected von Mangoldt series
plus the reflected inverse-Gamma kernel; the reflected von Mangoldt series
may be integrated termwise; and the reflected inverse-Gamma integral has the
left one-sided inverse-Gamma value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_termKernel_tsum_add_leftOneSidedInverseGammaValue_of_split_exchange_inverseGamma
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t)
    (hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) +
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f := by
  let A : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let S : ℂ :=
    ∫ t : ℝ,
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F.toContourFamily n t
  let T : ℂ :=
    ∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F.toContourFamily n t
  let G : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F.toContourFamily t
  let V : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  calc
    A = S + G := by
      exact hsplit
    _ = T + G := by
      exact congrArg (fun z : ℂ => z + G) hexchange
    _ = T + V := by
      exact congrArg (fun z : ℂ => T + z) hinverse

/-- Integrability of the reflected left Dirichlet-term `tsum`.

This is the integrability half of the reflected sum-integral exchange.  The
proof follows from the termwise a.e. strong measurability and the finite
`lintegral` norm-sum majorant established in
`PrimeLeftReflectedTermKernelAlgebra`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_tsum_integrable_ownerExchange
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (fun t : ℝ =>
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t)
      (volume : Measure ℝ) := by
  let K : ℕ → ℝ → ℂ :=
    fun n t =>
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t
  have hmeas :
      ∀ n : ℕ,
        AEStronglyMeasurable (K n) (volume : Measure ℝ) :=
    fun n : ℕ =>
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_aestronglyMeasurable
        f F h n
  have hnormMeas :
      ∀ n : ℕ,
        AEMeasurable
          (fun t : ℝ => (‖K n t‖₊ : ℝ≥0∞))
          (volume : Measure ℝ) :=
    fun n : ℕ => (hmeas n).ennnorm
  have hfinite :
      (∑' n : ℕ,
        ∫⁻ t : ℝ, ‖K n t‖₊ ∂(volume : Measure ℝ)) ≠ ∞ := by
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_ne_top
        f F h
  have hsummable :
      ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
        Summable fun n : ℕ => (‖K n t‖₊ : ℝ) := by
    have hfinite_lintegral :
        (∫⁻ t : ℝ,
          ∑' n : ℕ, (‖K n t‖₊ : ℝ≥0∞) ∂(volume : Measure ℝ)) ≠ ∞ :=
      Eq.subst
        (motive := fun x : ℝ≥0∞ => x ≠ ∞)
        (MeasureTheory.lintegral_tsum hnormMeas).symm
        hfinite
    refine
      (ae_lt_top' (AEMeasurable.ennreal_tsum hnormMeas) hfinite_lintegral).mono ?_
    intro t ht
    exact ENNReal.tsum_coe_ne_top_iff_summable_coe.mp ht.ne
  have htsumMeas :
      AEStronglyMeasurable
        (fun t : ℝ => ∑' n : ℕ, K n t)
        (volume : Measure ℝ) := by
    have hpartial :
        ∀ N : ℕ,
          AEStronglyMeasurable
            (fun t : ℝ => ∑ n ∈ Finset.range N, K n t)
            (volume : Measure ℝ) :=
      fun N : ℕ =>
        (Finset.range N).aestronglyMeasurable_sum
          (fun n _ => hmeas n)
    have hlim :
        ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
          Tendsto
            (fun N : ℕ => ∑ n ∈ Finset.range N, K n t)
            atTop
            (𝓝 (∑' n : ℕ, K n t)) := by
      filter_upwards [hsummable] with t ht
      have hnorm :
          Summable fun n : ℕ => ‖K n t‖ := by
        exact ht
      exact hnorm.of_norm.hasSum.tendsto_sum_nat
    exact aestronglyMeasurable_of_tendsto_ae atTop hpartial hlim
  have hfiniteIntegral :
      HasFiniteIntegral
        (fun t : ℝ => ∑' n : ℕ, K n t)
        (volume : Measure ℝ) := by
    dsimp [HasFiniteIntegral]
    have hlt :
        (∫⁻ t : ℝ,
          ∑' n : ℕ, ‖K n t‖₊ ∂(volume : Measure ℝ)) < ⊤ := by
      rwa [MeasureTheory.lintegral_tsum hnormMeas, lt_top_iff_ne_top]
    convert hlt using 1
    apply MeasureTheory.lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, NNReal.nnnorm_eq]
    filter_upwards [hsummable] with t ht
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp ht)
  exact ⟨htsumMeas, hfiniteIntegral⟩

/-- Sum-integral exchange for the reflected left Dirichlet-term kernels.

This is the reflected analogue of the right von-Mangoldt exchange theorem.
It uses the reflected term-kernel measurability and the reflected
inverse-quadratic norm majorant; it contains no Mellin value theorem and no
prime-power arithmetic. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integral_ownerExchange
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t := by
  have hmeas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F n t)
          (volume : Measure ℝ) :=
    fun n : ℕ =>
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_aestronglyMeasurable
        f F h n
  have hfinite :
      (∑' n : ℕ,
        ∫⁻ t : ℝ,
          ‖zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F n t‖₊ ∂(volume : Measure ℝ)) ≠ ∞ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_lintegral_norm_tsum_ne_top
      f F h
  exact
    MeasureTheory.integral_tsum hmeas hfinite

/-- Whole-line reflected completed split with the reflected term-series
integrability discharged by the owner exchange estimate.

After this reduction, the only integrability input still needed for the split
is the reflected inverse-Gamma kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_reflectedInverseGamma_integrable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F.toContourFamily t := by
  have hseries_integrable :
      Integrable
        (fun t : ℝ =>
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_tsum_integrable_ownerExchange
      f F.toContourFamily h
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_integrable
      f F hseries_integrable hinverse_integrable

/-- Reflected-completed complement value from the positive-index reflected
Mellin theorem, complement `tsum` normalization, and completed-kernel
expansion.

This theorem assembles the already peeled reflected termwise API with the
future completed-kernel expansion theorem.  It is still conditional on the two
genuine analytic/summability inputs; it is not the public owner theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hcomplement_tsum :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f)
    (hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hterm_tsum :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_pos_and_complement_tsum
      f F.toContourFamily hpos hcomplement_tsum
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_tsum
      f F hexpansion hterm_tsum

/-- Reflected-completed value in terms of the actual reflected boundary
contribution.

This is the non-Hermitian reflected Mellin value: the reflected term-kernel
sum is evaluated by the proved reflected Paley-Wiener theorem, but no
identification with the arithmetic complement is made here.  The missing
normalization is exactly the later comparison between reflected boundary and
complement contributions. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_reflectedBoundary_of_split_exchange_inverseGamma
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t)
    (hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f) := by
  have hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_termKernel_tsum_add_leftOneSidedInverseGammaValue_of_split_exchange_inverseGamma
      f F hsplit hexchange hinverse
  have hterm_tsum :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_reflectedBoundaryContribution
      f F.toContourFamily
  let A : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let S : ℂ :=
    ∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
          f F.toContourFamily n t
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  let R : ℂ :=
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f
  calc
    A - G = (S + G) - G := by
      exact congrArg (fun z : ℂ => z - G) hexpansion
    _ = S := by
      exact add_sub_cancel_right S G
    _ = -R := by
      exact hterm_tsum

/-- Reflected-completed value in terms of the reflected boundary contribution,
with the split and reflected term-series exchange discharged by owner
theorems.

Only the reflected inverse-Gamma scalar value remains as an analytic input. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_reflectedBoundary_of_reflectedInverseGammaValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f) := by
  have hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_gammaBinetCoherence
      f F.toContourFamily h hcoh
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_reflectedInverseGamma_integrable
      f F h hinverse_integrable
  have hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integral_ownerExchange
      f F.toContourFamily h
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_reflectedBoundary_of_split_exchange_inverseGamma
      f F hsplit hexchange hinverse

/-- Reflected-completed complement value from the positive-index reflected
Mellin theorem, the raw `tsum_sub` normalization of complement samples, and
the completed-kernel expansion.

This is the most convenient final assembly form for the reflected prime
branch: it consumes exactly the three non-algebraic inputs left after peeling. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos_tsumSub
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (htsum_sub :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) -
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n)
    (hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hcomplement_tsum :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f :=
    zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_tsum_eq_contribution_of_tsum_sub
      f htsum_sub
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos
      f F hpos hcomplement_tsum hexpansion

/-- Reflected-completed complement value from the positive-index reflected
Mellin theorem, summability of the two natural prime series, and the
completed-kernel expansion.

Compared with the raw `tsum_sub` assembly theorem, this version has the
arithmetic complement normalization already discharged by the owner theorem in
`PrimeNaturalTimeArithmetic`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos_summable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n))
    (hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hcomplement_tsum :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f :=
    zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_tsum_eq_contribution_of_summable
      f hsymmetric honeSided
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos
      f F hpos hcomplement_tsum hexpansion

/-- Reflected-completed complement value from the positive-index reflected
Mellin theorem and the completed-kernel expansion, with natural-prime
summability discharged by the arithmetic owner. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos_arithmetic
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos_summable
      f F hpos
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable f)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f)
      hexpansion

/-- Reflected-completed complement value from the fully split reflected
completed expansion, positive-index reflected Mellin inversion, and
summability of the two natural prime series.

This is the assembly theorem closest to the public owner leaf without hiding
any analytic statement: it names the reflected split, termwise exchange, and
reflected inverse-Gamma value separately. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_split_exchange_inverseGamma_pos_summable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n))
    (hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t)
    (hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_termKernel_tsum_add_leftOneSidedInverseGammaValue_of_split_exchange_inverseGamma
      f F hsplit hexchange hinverse
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_pos_summable
      f F hpos hsymmetric honeSided hexpansion

/-- Reflected-completed complement value from the fully split reflected
completed expansion, positive-index reflected Mellin inversion, and the
reflected inverse-Gamma value, with natural-prime summability supplied by the
arithmetic owner. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_split_exchange_inverseGamma_pos
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t)
    (hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_split_exchange_inverseGamma_pos_summable
      f F hpos
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable f)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f)
      hsplit hexchange hinverse

/-- Reflected-completed complement value with the reflected completed split and
the reflected term-series exchange discharged by owner theorems.

The remaining inputs are exactly the value facts not proved by the exchange
machinery: positive-index reflected Mellin inversion, summability of the two
natural prime sample series, reflected inverse-Gamma integrability, and the
reflected inverse-Gamma scalar value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedAnalyticValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n))
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_reflectedInverseGamma_integrable
      f F h hinverse_integrable
  have hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integral_ownerExchange
      f F.toContourFamily h
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_split_exchange_inverseGamma_pos_summable
      f F hpos hsymmetric honeSided hsplit hexchange hinverse

/-- Reflected-completed complement value with split and exchange discharged by
owner theorems and natural-prime summability supplied by arithmetic.

The remaining inputs are the positive-index reflected Mellin values, reflected
inverse-Gamma integrability, and the reflected inverse-Gamma scalar value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedAnalyticValues_pos
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedAnalyticValues
      f F h hpos
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable f)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f)
      hinverse_integrable hinverse

/-- Reflected-completed complement value with the reflected inverse-Gamma
integrability discharged from Gamma/Binet factor bounds.

After this reduction, the reflected inverse-Gamma input is only its scalar
whole-line value; the integrability needed for `integral_add` is supplied by
the owner factor-bound theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n))
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_gammaBinetCoherence
      f F.toContourFamily h hcoh
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedAnalyticValues
      f F h hpos hsymmetric honeSided hinverse_integrable hinverse

/-- Reflected-completed complement value after the natural prime sample
summability facts have been discharged in the arithmetic owner file.

The only remaining scalar inputs are the positive-index reflected Mellin
values and the reflected inverse-Gamma scalar value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues_pos_inverse
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues
      f F h hcoh hpos
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable f)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f)
      hinverse

/-- Reflected-completed complement value from a pointwise two-face
normalization, after the completed split, reflected term-series exchange, and
reflected inverse-Gamma scalar value are supplied.

This route does not assert the older positive-index complement value directly.
Instead, it uses the already proved reflected-boundary summation theorem and
then consumes the named two-face normalization as the precise remaining
time-side input. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_split_exchange_inverseGamma_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t)
    (hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hexpansion :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_termKernel_tsum_add_leftOneSidedInverseGammaValue_of_split_exchange_inverseGamma
      f F hsplit hexchange hinverse
  have hterm_tsum :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_timeSummand_eq_twoFace
      f F.toContourFamily htwoFace
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedTermKernel_tsum
      f F hexpansion hterm_tsum

/-- Reflected-completed complement value from the two-face normalization, with
the reflected completed split and reflected term-series exchange discharged by
their owner theorems.

The remaining analytic inputs are the reflected inverse-Gamma integrability
needed for the split and its scalar whole-line value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedAnalyticValues_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_integral_tsum_termKernel_add_reflectedInverseGamma_of_reflectedInverseGamma_integrable
      f F h hinverse_integrable
  have hexchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            f F.toContourFamily n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F.toContourFamily n t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_tsum_eq_tsum_integral_ownerExchange
      f F.toContourFamily h
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_split_exchange_inverseGamma_timeSummand_eq_twoFace
      f F htwoFace hsplit hexchange hinverse

/-- Reflected-completed complement value from the two-face normalization, with
the reflected inverse-Gamma integrability discharged from Gamma/Binet
coherence.

After this reduction, the only remaining scalar inputs are the two-face
normalization and the reflected inverse-Gamma value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hinverse_integrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_gammaBinetCoherence
      f F.toContourFamily h hcoh
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedAnalyticValues_timeSummand_eq_twoFace
      f F h htwoFace hinverse_integrable hinverse

/-- Reflected-completed complement value from the scalar Hermitian
time-boundary normalization at every nonzero natural prime center.

This is the closest reflected-prime assembly form to the autocorrelation owner
layer: all contour, exchange, and inverse-Gamma integrability work is
discharged, and the remaining prime-side input is the exact scalar Hermitian
identity that identifies the symmetric summand with its two boundary faces. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues_scalarHermitian
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar :
      ∀ n : ℕ, n ≠ 0 →
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
            ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))))
    (hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_scalarHermitian
      f hscalar
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues_timeSummand_eq_twoFace
      f F h hcoh htwoFace hinverse

/-- Reflected-completed complement value from the two prime-side and
inverse-Gamma component inputs that remain genuinely analytic.

This theorem is the intended final assembly shape before the owner leaf:
the prime arithmetic side supplies `timeSummand = twoFace`, while the
Gamma/Binet and correction-pole sides supply the reflected inverse-Gamma
component scalar values. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_componentValues_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hcorr_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F.toContourFamily t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hinverse :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_leftOneSidedInverseGammaValue_of_componentValues
      f F.toContourFamily h hcoh harch_value hcorr_value
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedScalarValues_timeSummand_eq_twoFace
      f F h hcoh htwoFace hinverse

/-- Scalar-Hermitian version of the component-value reflected-completed
assembly theorem.

The scalar Hermitian condition is still explicit because it is not a property
of an arbitrary admissible probe. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_componentValues_scalarHermitian
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar :
      ∀ n : ℕ, n ≠ 0 →
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
            ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))))
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hcorr_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F.toContourFamily t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_scalarHermitian
      f hscalar
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_componentValues_timeSummand_eq_twoFace
      f F h hcoh htwoFace harch_value hcorr_value

/-- Component-value reflected-completed assembly with the reflected correction
value reduced to the two reflected pole Cauchy values. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedPoleValues_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n)
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F.toContourFamily t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
    (hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hcorr_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F.toContourFamily t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_of_zeroPole_onePole_values_ownerComponents
      f F.toContourFamily h hzero_value hone_value
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_componentValues_timeSummand_eq_twoFace
      f F h hcoh htwoFace harch_value hcorr_value

/-- Scalar-Hermitian version with the reflected correction value reduced to the
two reflected pole Cauchy values. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedPoleValues_scalarHermitian
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar :
      ∀ n : ℕ, n ≠ 0 →
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
            ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))))
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F.toContourFamily t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
    (hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_scalarHermitian
      f hscalar
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedPoleValues_timeSummand_eq_twoFace
      f F h hcoh htwoFace harch_value hzero_value hone_value

/-- Owner analytic leaf: reflected completed kernel after subtracting the
one-sided inverse-Gamma scalar gives the negative complementary prime
contribution.

Proof target:
reflect the completed logarithmic derivative to the right affine line, expand
the von Mangoldt Dirichlet series, apply the Paley-Wiener/Mellin inversion
termwise, and identify the complementary natural prime contribution.

The proved algebra around this leaf is already separated:
`PrimeLeftKernelReflection` owns
`left prime = reflected completed - inverseGamma`, and
`zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue_sub_leftOneSidedInverseGammaValue`
owns the scalar recombination.  What remains here is only the
reflected-completed Mellin/complement inversion value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_ownerReflectedCompletedValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) -
      zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_of_reflectedPoleValues_scalarHermitian
      f F h hcoh hscalar
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integral_eq_neg_phi_zero_ownerComponents
        f F.toContourFamily h hcoh)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integral_eq_standardResidue_ownerComponents
        f F.toContourFamily h)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integral_eq_zero_ownerComponents
        f F.toContourFamily h)

/-- Packaged whole-line value of the reflected completed logarithmic-derivative
kernel on the left prime line.

This theorem is now only scalar recombination from the Mellin/complement leaf
above. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_ownerReflectedCompletedValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f := by
  let A : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f
  let G : ℂ := zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f
  have hsub :
      A - G = -C :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_sub_leftOneSidedInverseGammaValue_eq_neg_complement_ownerReflectedCompletedValue
      f F h hcoh hscalar
  calc
    A = (A - G) + G := by
      exact (sub_add_cancel A G).symm
    _ = -C + G := by
      exact congrArg (fun z : ℂ => z + G) hsub
    _ = zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedValue f := by
      rfl

/-- Expanded statement of the reflected completed kernel value, matching the
scalar shape consumed by `PrimeLogDerivativeTransport`. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_expanded_ownerReflectedCompletedValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscalar : zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) +
        (-(zetaCompletedExplicitFormulaPhi f 0) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel_integral_eq_ownerReflectedCompletedValue
      f F h hcoh hscalar

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
