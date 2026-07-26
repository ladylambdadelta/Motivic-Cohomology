import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineCorrectionScheduled
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetTransport

/-!
# Coupled affine archimedean Binet kernel

The unconditional finite Abel--Plana logarithmic-derivative formula is applied
before either test-transform factor is introduced.  This produces one scalar
decomposition shared by the right and reflected-right channels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Main scalar in the positive right-line finite-Binet decomposition. -/
noncomputable def zetaCompletedAffineArchimedeanRightBinetMainFactor
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalMain
          (family.c / 2) (t / 2)) -
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine family t)

/-- Remainder scalar in the positive right-line finite-Binet decomposition. -/
noncomputable def zetaCompletedAffineArchimedeanRightBinetRemainderFactor
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  -((1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalRemainder
      (family.c / 2) (t / 2))

/-- Direct scalar finite-Binet decomposition on the right affine line. -/
theorem explicitFormulaArchimedeanLogDerivative_rightAffineLine_eq_binetFactors_shiftOwner
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    explicitFormulaArchimedeanLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine family t) =
      zetaCompletedAffineArchimedeanRightBinetMainFactor family t +
        zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t :=
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine family t
  let w : ℂ := s / 2
  let sigma : ℝ := family.c / 2
  let tau : ℝ := t / 2
  let piTerm : ℂ :=
    zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let mainTerm : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalMain sigma tau
  let remainderTerm : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalRemainder sigma tau
  let correctionTerm : ℂ := explicitFormulaCorrectionLogDerivative s
  let sigmaPositive : 0 < sigma :=
    div_pos family.c_pos zero_lt_two
  let lineEquality : w = (sigma + tau * Complex.I : ℂ) :=
    zetaCompletedExplicitFormulaRightAffineLine_div_two_eq_fixedVertical
      family t
  let gammaFixed :
      deriv Complex.Gamma w / Complex.Gamma w =
        Complex.GammaLogDerivativeFixedVerticalMain sigma tau +
          Complex.GammaLogDerivativeFixedVerticalRemainder sigma tau :=
    Eq.subst
      (motive := fun point : ℂ =>
        deriv Complex.Gamma point / Complex.Gamma point =
          Complex.GammaLogDerivativeFixedVerticalMain sigma tau +
            Complex.GammaLogDerivativeFixedVerticalRemainder sigma tau)
      lineEquality.symm
      (Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_direct
        sigmaPositive tau)
  let halfGamma :
      (deriv Complex.Gamma w * (1 / 2 : ℂ)) / Complex.Gamma w =
        mainTerm + remainderTerm :=
    zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
      (deriv Complex.Gamma w)
      (Complex.Gamma w)
      (Complex.GammaLogDerivativeFixedVerticalMain sigma tau)
      (Complex.GammaLogDerivativeFixedVerticalRemainder sigma tau)
      gammaFixed
  let gammaRealRaw :
      deriv Complex.Gammaℝ s / Complex.Gammaℝ s =
        piTerm +
          (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w :=
    zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq
      family t
  let gammaReal :
      deriv Complex.Gammaℝ s / Complex.Gammaℝ s =
        piTerm + (mainTerm + remainderTerm) :=
    Eq.trans gammaRealRaw
      (congrArg (fun value : ℂ => piTerm + value) halfGamma)
  let inverseGammaRaw :
      inverseGammaCompletionLogDeriv s =
        -deriv Complex.Gammaℝ s / Complex.Gammaℝ s :=
    zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_eq_neg_Gammaℝ_logDeriv
      family t
  let inverseGamma :
      inverseGammaCompletionLogDeriv s =
        -(piTerm + (mainTerm + remainderTerm)) :=
    calc
      inverseGammaCompletionLogDeriv s =
          -deriv Complex.Gammaℝ s / Complex.Gammaℝ s :=
        inverseGammaRaw
      _ = -(deriv Complex.Gammaℝ s / Complex.Gammaℝ s) :=
        neg_div (Complex.Gammaℝ s) (deriv Complex.Gammaℝ s)
      _ = -(piTerm + (mainTerm + remainderTerm)) :=
        congrArg Neg.neg gammaReal
  let archimedeanUnfold :
      explicitFormulaArchimedeanLogDerivative s =
        inverseGammaCompletionLogDeriv s - correctionTerm :=
    Eq.refl (explicitFormulaArchimedeanLogDerivative s)
  let logarithmicDerivative :
      explicitFormulaArchimedeanLogDerivative s =
        (-(piTerm + mainTerm) - correctionTerm) +
          -remainderTerm :=
    calc
      explicitFormulaArchimedeanLogDerivative s =
          inverseGammaCompletionLogDeriv s - correctionTerm :=
        archimedeanUnfold
      _ = -(piTerm + (mainTerm + remainderTerm)) - correctionTerm :=
        congrArg
          (fun value : ℂ => value - correctionTerm)
          inverseGamma
      _ = (-(piTerm + mainTerm) - correctionTerm) +
          -remainderTerm :=
        zetaCompletedExplicitFormula_archimedeanBinet_logDerivative_algebra
          piTerm mainTerm remainderTerm correctionTerm
  logarithmicDerivative

/-- Reflected main Binet kernel with the forced left-centered transform. -/
noncomputable def zetaCompletedAffineArchimedeanReflectedBinetMainKernel
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t)) *
    zetaCompletedExplicitFormulaPhi probe
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t)

/-- Reflected remainder Binet kernel with the forced left-centered transform. -/
noncomputable def zetaCompletedAffineArchimedeanReflectedBinetRemainderKernel
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (-zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t)) *
    zetaCompletedExplicitFormulaPhi probe
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t)

/-- Pointwise reflected archimedean decomposition from the shared scalar
finite-Binet identity. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq_binetFactors_shiftOwner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        probe family t =
      zetaCompletedAffineArchimedeanReflectedBinetMainKernel
          probe family t +
        zetaCompletedAffineArchimedeanReflectedBinetRemainderKernel
          probe family t :=
  let mainFactor : ℂ :=
    zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t)
  let remainderFactor : ℂ :=
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t)
  let transformValue : ℂ :=
    zetaCompletedExplicitFormulaPhi probe
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t)
  let scalarEquality :
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine family (-t)) =
        mainFactor + remainderFactor :=
    explicitFormulaArchimedeanLogDerivative_rightAffineLine_eq_binetFactors_shiftOwner
      family (-t)
  let kernelUnfold :
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          probe family t =
        (-explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine family (-t))) *
          transformValue :=
    Eq.refl
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        probe family t)
  let reflectedUnfold :
      (-mainFactor) * transformValue +
          (-remainderFactor) * transformValue =
        zetaCompletedAffineArchimedeanReflectedBinetMainKernel
            probe family t +
          zetaCompletedAffineArchimedeanReflectedBinetRemainderKernel
            probe family t :=
    Eq.refl
      (zetaCompletedAffineArchimedeanReflectedBinetMainKernel
          probe family t +
        zetaCompletedAffineArchimedeanReflectedBinetRemainderKernel
          probe family t)
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        probe family t =
        (-explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine family (-t))) *
          transformValue :=
      kernelUnfold
    _ = (-(mainFactor + remainderFactor)) * transformValue :=
      congrArg (fun value : ℂ => (-value) * transformValue)
        scalarEquality
    _ = ((-mainFactor) + (-remainderFactor)) * transformValue :=
      congrArg (fun value : ℂ => value * transformValue)
        (neg_add mainFactor remainderFactor)
    _ = (-mainFactor) * transformValue +
          (-remainderFactor) * transformValue :=
      add_mul (-mainFactor) (-remainderFactor) transformValue
    _ = zetaCompletedAffineArchimedeanReflectedBinetMainKernel
          probe family t +
        zetaCompletedAffineArchimedeanReflectedBinetRemainderKernel
          probe family t :=
      reflectedUnfold

/-- The explicit paired finite-Binet kernel for the coupled affine
archimedean packet. -/
noncomputable def zetaCompletedAffineArchimedeanPairedBinetKernel
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
      probe family t +
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      probe family t) -
    (zetaCompletedAffineArchimedeanReflectedBinetMainKernel
        probe family t +
      zetaCompletedAffineArchimedeanReflectedBinetRemainderKernel
        probe family t)

/-- The coupled affine archimedean kernel is pointwise its paired finite-Binet
kernel. -/
theorem zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel_eq_pairedBinet_shiftOwner
    (probe : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanRightReflectedDifferenceKernel
        probe family t =
      zetaCompletedAffineArchimedeanPairedBinetKernel
        probe family t :=
  let rightEquality :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
      probe family t
  let reflectedEquality :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq_binetFactors_shiftOwner
      probe family t
  congrArg₂ HSub.hSub rightEquality reflectedEquality

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
