import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftKernelReflection

/-!
# Completed affine contour

This file owns the coupled completed logarithmic-derivative kernels. Channel
splits are exact pointwise representations; analytic values and residues are
assigned only after the channels have been recombined.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The completed right affine-line kernel. -/
noncomputable def zetaCompletedRightAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- The completed left affine-line kernel. -/
noncomputable def zetaCompletedLeftAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftAffineLine F t) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- The right affine kernel written in the coordinates induced from reflection
of the left line. -/
noncomputable def zetaCompletedReflectedRightAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  -completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
    zetaCompletedExplicitFormulaPhi f
      (-zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))

/-- The finite completed right-minus-left affine channel. -/
noncomputable def zetaCompletedAffineVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedRightAffineKernel f F t) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedLeftAffineKernel f F t

/-- The completed logarithmic derivative is the exact sum of its three
channel factors. -/
theorem completedZetaNegLogDeriv_eq_prime_add_archimedean_add_correction
    (s : ℂ) :
    completedZetaNegLogDeriv s =
      explicitFormulaPrimeLogDerivative s +
        explicitFormulaArchimedeanLogDerivative s +
          explicitFormulaCorrectionLogDerivative s := by
  have packetEquality :
      completedZetaNegLogDeriv s =
        explicitFormulaCompletedLogDerivative s :=
    completedZetaNegLogDeriv_eq_explicitFormulaCompletedLogDerivative_ownerCompletedLogDerivativeDecomposition
      s
  exact Eq.trans packetEquality
    (Eq.refl (explicitFormulaCompletedLogDerivative s))

/-- Pointwise decomposition of the completed right affine kernel. -/
theorem zetaCompletedRightAffineKernel_eq_channelKernelSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedRightAffineKernel f F t =
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let transformValue : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  have factorEquality :
      completedZetaNegLogDeriv s =
        explicitFormulaPrimeLogDerivative s +
          explicitFormulaArchimedeanLogDerivative s +
            explicitFormulaCorrectionLogDerivative s :=
    completedZetaNegLogDeriv_eq_prime_add_archimedean_add_correction s
  calc
    zetaCompletedRightAffineKernel f F t =
        completedZetaNegLogDeriv s * transformValue := by
      exact Eq.refl (zetaCompletedRightAffineKernel f F t)
    _ =
        (explicitFormulaPrimeLogDerivative s +
          explicitFormulaArchimedeanLogDerivative s +
            explicitFormulaCorrectionLogDerivative s) * transformValue := by
      exact congrArg (fun value : ℂ => value * transformValue) factorEquality
    _ =
        explicitFormulaPrimeLogDerivative s * transformValue +
          explicitFormulaArchimedeanLogDerivative s * transformValue +
            explicitFormulaCorrectionLogDerivative s * transformValue := by
      exact Eq.trans
        (add_mul
          (explicitFormulaPrimeLogDerivative s +
            explicitFormulaArchimedeanLogDerivative s)
          (explicitFormulaCorrectionLogDerivative s)
          transformValue)
        (congrArg
          (fun value : ℂ =>
            value +
              explicitFormulaCorrectionLogDerivative s * transformValue)
          (add_mul
            (explicitFormulaPrimeLogDerivative s)
            (explicitFormulaArchimedeanLogDerivative s)
            transformValue))
    _ =
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel f F t +
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F t := by
      exact Eq.refl _

/-- Pointwise decomposition of the completed left affine kernel. -/
theorem zetaCompletedLeftAffineKernel_eq_channelKernelSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedLeftAffineKernel f F t =
      zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let transformValue : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have factorEquality :
      completedZetaNegLogDeriv s =
        explicitFormulaPrimeLogDerivative s +
          explicitFormulaArchimedeanLogDerivative s +
            explicitFormulaCorrectionLogDerivative s :=
    completedZetaNegLogDeriv_eq_prime_add_archimedean_add_correction s
  calc
    zetaCompletedLeftAffineKernel f F t =
        completedZetaNegLogDeriv s * transformValue := by
      exact Eq.refl (zetaCompletedLeftAffineKernel f F t)
    _ =
        (explicitFormulaPrimeLogDerivative s +
          explicitFormulaArchimedeanLogDerivative s +
            explicitFormulaCorrectionLogDerivative s) * transformValue := by
      exact congrArg (fun value : ℂ => value * transformValue) factorEquality
    _ =
        explicitFormulaPrimeLogDerivative s * transformValue +
          explicitFormulaArchimedeanLogDerivative s * transformValue +
            explicitFormulaCorrectionLogDerivative s * transformValue := by
      exact Eq.trans
        (add_mul
          (explicitFormulaPrimeLogDerivative s +
            explicitFormulaArchimedeanLogDerivative s)
          (explicitFormulaCorrectionLogDerivative s)
          transformValue)
        (congrArg
          (fun value : ℂ =>
            value +
              explicitFormulaCorrectionLogDerivative s * transformValue)
          (add_mul
            (explicitFormulaPrimeLogDerivative s)
            (explicitFormulaArchimedeanLogDerivative s)
            transformValue))
    _ =
        zetaCompletedExplicitFormulaPrimeLeftLogDerivativeAffineKernel f F t +
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F t := by
      exact Eq.refl _

/-- Functional-equation reflection of the completed left affine kernel. -/
theorem zetaCompletedLeftAffineKernel_eq_reflectedRightAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedLeftAffineKernel f F t =
      zetaCompletedReflectedRightAffineKernel f F t := by
  have logarithmicDerivativeReflection :
      completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t) =
        -completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine F (-t)) :=
    zetaCompletedExplicitFormula_completedZetaNegLogDeriv_leftAffineLine_eq_neg_rightAffineLine
      F t
  have transformCoordinateReflection :
      zetaCompletedExplicitFormulaLeftCenteredAffineLine F t =
        -zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine
      F t
  calc
    zetaCompletedLeftAffineKernel f F t =
        completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      exact Eq.refl (zetaCompletedLeftAffineKernel f F t)
    _ =
        -completedZetaNegLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
          zetaCompletedExplicitFormulaPhi f
            (-zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)) := by
      exact congrArg₂ HMul.hMul
        logarithmicDerivativeReflection
        (congrArg (zetaCompletedExplicitFormulaPhi f)
          transformCoordinateReflection)
    _ = zetaCompletedReflectedRightAffineKernel f F t := by
      exact Eq.refl _

/-- The finite completed channel may replace its left face by the reflected
right kernel before any limiting argument. -/
theorem zetaCompletedAffineVerticalChannel_eq_right_sub_reflectedRight
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) :
    zetaCompletedAffineVerticalChannel f F T =
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedRightAffineKernel f F t) -
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedReflectedRightAffineKernel f F t := by
  have leftIntegralReflection :
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedLeftAffineKernel f F t) =
        ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedReflectedRightAffineKernel f F t := by
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun t _membership =>
        zetaCompletedLeftAffineKernel_eq_reflectedRightAffineKernel f F t)
  exact congrArg
    (fun leftIntegral : ℂ =>
      (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
          zetaCompletedRightAffineKernel f F t) - leftIntegral)
    leftIntegralReflection

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
