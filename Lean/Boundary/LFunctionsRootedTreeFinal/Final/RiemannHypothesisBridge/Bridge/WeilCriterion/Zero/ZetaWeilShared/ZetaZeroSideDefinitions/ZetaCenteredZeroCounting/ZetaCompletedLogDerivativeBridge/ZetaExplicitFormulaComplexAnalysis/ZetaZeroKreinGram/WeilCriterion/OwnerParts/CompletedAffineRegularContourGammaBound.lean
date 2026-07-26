import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourFinite
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourGammaBoundParts.Coordinates
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaFactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.IteratedOscillatoryKernel.Owner

/-! Compact-strip Gamma bounds for the regular inverse-Gamma contour. -/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The Binet remainder integral with its real-part scalar removed. -/
noncomputable def regularInverseGammaBinetKernelIntegral : ℝ :=
  ∫ u : ℝ in Set.Ioi (0 : ℝ),
    u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)

/-- A visibly continuous form of the positive-line Gamma bound constant. -/
noncomputable def regularInverseGammaContinuousPositiveLineConstant
    (sigma : ℝ) : ℝ :=
  (((|Real.log sigma| + (sigma + 1) + Real.pi) + 1 / sigma) +
    |‖(2 : ℂ)‖ *
      ((1 / sigma ^ 2) * regularInverseGammaBinetKernelIntegral)|)

/-- Pulling the real-part scalar through the Binet integral identifies the
fixed-line constant with its continuous normal form. -/
theorem GammaLogDerivativeFixedVerticalPositiveLineConstant_eq_continuous
    (sigma : ℝ) :
    Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma =
      regularInverseGammaContinuousPositiveLineConstant sigma :=
  let integralScaling :
      (∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / sigma ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))) =
        (1 / sigma ^ 2) * regularInverseGammaBinetKernelIntegral :=
    let scalarIntegral :=
      MeasureTheory.integral_mul_left
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (1 / sigma ^ 2)
        (fun u : ℝ =>
          u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))
    scalarIntegral
  congrArg
    (fun remainder : ℝ =>
      (((|Real.log sigma| + (sigma + 1) + Real.pi) + 1 / sigma) +
        |‖(2 : ℂ)‖ * remainder|))
    integralScaling

/-- The continuous normal form of the Gamma fixed-line constant is continuous
at every positive real coordinate. -/
theorem regularInverseGammaContinuousPositiveLineConstant_continuousAt
    (sigma : ℝ)
    (sigmaPositive : 0 < sigma) :
    ContinuousAt regularInverseGammaContinuousPositiveLineConstant sigma :=
  let sigmaNonzero : sigma ≠ 0 := ne_of_gt sigmaPositive
  let logContinuous : ContinuousAt Real.log sigma :=
    Real.continuousAt_log sigmaNonzero
  let logAbsoluteContinuous :
      ContinuousAt (fun value : ℝ => |Real.log value|) sigma :=
    logContinuous.abs
  let sigmaPlusOneContinuous :
      ContinuousAt (fun value : ℝ => value + 1) sigma :=
    continuousAt_id.add continuousAt_const
  let reciprocalContinuous :
      ContinuousAt (fun value : ℝ => 1 / value) sigma :=
    continuousAt_const.div continuousAt_id sigmaNonzero
  let squareNonzero : sigma ^ 2 ≠ 0 :=
    pow_ne_zero 2 sigmaNonzero
  let inverseSquareContinuous :
      ContinuousAt (fun value : ℝ => 1 / value ^ 2) sigma :=
    continuousAt_const.div (continuousAt_id.pow 2) squareNonzero
  let remainderContinuous :
      ContinuousAt
        (fun value : ℝ =>
          (1 / value ^ 2) * regularInverseGammaBinetKernelIntegral)
        sigma :=
    inverseSquareContinuous.mul continuousAt_const
  let remainderScaledContinuous :
      ContinuousAt
        (fun value : ℝ =>
          ‖(2 : ℂ)‖ *
            ((1 / value ^ 2) * regularInverseGammaBinetKernelIntegral))
        sigma :=
    continuousAt_const.mul remainderContinuous
  let remainderAbsoluteContinuous :
      ContinuousAt
        (fun value : ℝ =>
          |‖(2 : ℂ)‖ *
            ((1 / value ^ 2) * regularInverseGammaBinetKernelIntegral)|)
        sigma :=
    remainderScaledContinuous.abs
  (((logAbsoluteContinuous.add sigmaPlusOneContinuous).add
    continuousAt_const).add reciprocalContinuous).add
    remainderAbsoluteContinuous

/-- The positive-line Gamma constants have one uniform upper bound on every
positive compact interval. -/
theorem exists_uniform_GammaLogDerivative_constant_on_positive_Icc
    (a b : ℝ)
    (aPositive : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ sigma : ℝ,
        sigma ∈ Set.Icc a b →
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma ≤ B := by
  let compactInterval : IsCompact (Set.Icc a b) := isCompact_Icc
  let continuousOnInterval :
      ContinuousOn regularInverseGammaContinuousPositiveLineConstant
        (Set.Icc a b) :=
    fun sigma membership =>
    let sigmaPositive : 0 < sigma :=
      lt_of_lt_of_le aPositive membership.1;
      (regularInverseGammaContinuousPositiveLineConstant_continuousAt
        sigma sigmaPositive).continuousWithinAt
  let boundedImage :
      BddAbove
        (regularInverseGammaContinuousPositiveLineConstant '' Set.Icc a b) :=
    compactInterval.bddAbove_image continuousOnInterval
  exact
    match boundedImage with
    | ⟨B, upperBound⟩ =>
        let nonnegativeBound : ℝ := max 0 B
        have nonnegativeBoundNonnegative : 0 ≤ nonnegativeBound :=
          le_max_left 0 B
        have originalBoundLeNonnegativeBound : B ≤ nonnegativeBound :=
          le_max_right 0 B
        Exists.intro nonnegativeBound
          (And.intro nonnegativeBoundNonnegative
            (fun sigma membership =>
              Eq.subst
                (motive := fun value : ℝ => value ≤ nonnegativeBound)
                (GammaLogDerivativeFixedVerticalPositiveLineConstant_eq_continuous
                  sigma).symm
                ((upperBound
                  ⟨sigma, membership,
                    Eq.refl
                      (regularInverseGammaContinuousPositiveLineConstant sigma)⟩).trans
                  originalBoundLeNonnegativeBound)))

/-- On the positive half-plane the inverse-Gamma logarithmic derivative is
the negative of the elementary pi term and the half-argument Gamma quotient. -/
theorem inverseGammaCompletionLogDeriv_eq_neg_pi_add_halfGamma_of_re_pos
    (z : ℂ)
    (realPartPositive : 0 < z.re) :
    inverseGammaCompletionLogDeriv z =
      -(
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
          (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2)) :=
  let avoidsGammaRealPoles :
      ∀ n : ℕ, z ≠ -(2 * (n : ℂ)) :=
    fun n equality =>
    let realPartEquality :
        z.re = (-(2 * (n : ℂ))).re :=
      congrArg Complex.re equality
    let poleRealPartNonpositive :
        (-(2 * (n : ℂ))).re ≤ 0 :=
      let naturalNonnegative : (0 : ℝ) ≤ (n : ℝ) :=
        Nat.cast_nonneg n
      let twiceNaturalNonnegative : (0 : ℝ) ≤ 2 * (n : ℝ) :=
        mul_nonneg zero_le_two naturalNonnegative
      let poleRealPartEquality :
          (-(2 * (n : ℂ))).re = -(2 * (n : ℝ)) :=
        Eq.trans
          (Complex.neg_re (2 * (n : ℂ)))
          (congrArg Neg.neg
            (regularInverseGamma_two_nat_complex_mul_re n))
      Eq.subst
        (motive := fun value : ℝ => value ≤ 0)
        poleRealPartEquality.symm
        (neg_nonpos.mpr twiceNaturalNonnegative)
    let zRealPartNonpositive : z.re ≤ 0 :=
      Eq.subst
        (motive := fun value : ℝ => value ≤ 0)
        realPartEquality.symm
        poleRealPartNonpositive
    (not_le_of_gt realPartPositive) zRealPartNonpositive
  let gammaRealNonzero : Complex.Gammaℝ z ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos realPartPositive
  let gammaRealDifferentiable :
      DifferentiableAt ℂ Complex.Gammaℝ z :=
    (Gammaℝ_hasDerivAt_of_ne_zero_locus avoidsGammaRealPoles).differentiableAt
  let inverseGammaIdentity :
      inverseGammaCompletionLogDeriv z =
        -deriv Complex.Gammaℝ z / Complex.Gammaℝ z :=
    inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
      gammaRealDifferentiable gammaRealNonzero
  let gammaRealIdentity :
      deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
          (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2) :=
    Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
      avoidsGammaRealPoles gammaRealNonzero
  let quotientNegation :
      -deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
        -(deriv Complex.Gammaℝ z / Complex.Gammaℝ z) :=
    neg_div (Complex.Gammaℝ z) (deriv Complex.Gammaℝ z)
  Eq.trans inverseGammaIdentity
    (Eq.trans quotientNegation (congrArg Neg.neg gammaRealIdentity))

/-- A uniform bound for the ordinary Gamma constants on the half-real-part
strip gives a uniform linear bound for the inverse-Gamma completion factor. -/
theorem inverseGammaCompletionLogDeriv_linear_bound_of_uniform_halfStrip
    (z : ℂ)
    (a b B : ℝ)
    (realPartPositive : 0 < z.re)
    (halfRealPartMembership : z.re / 2 ∈ Set.Icc a b)
    (boundNonnegative : 0 ≤ B)
    (uniformGammaBound :
      ∀ sigma : ℝ,
        sigma ∈ Set.Icc a b →
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma ≤ B) :
    ‖inverseGammaCompletionLogDeriv z‖ ≤
      (‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖ +
        ‖(1 / 2 : ℂ)‖ * B) *
          (1 + ‖z.im‖) :=
  let sigma : ℝ := z.re / 2
  let height : ℝ := z.im / 2
  let piTerm : ℂ :=
    Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))
  let gammaQuotient : ℂ :=
    deriv Complex.Gamma (z / 2) / Complex.Gamma (z / 2)
  have sigmaPositive : 0 < sigma :=
    div_pos realPartPositive zero_lt_two
  have fixedLineBound :
      ‖deriv Complex.Gamma
          ((sigma : ℂ) + (height : ℂ) * Complex.I) /
        Complex.Gamma
          ((sigma : ℂ) + (height : ℂ) * Complex.I)‖ ≤
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma *
          (1 + ‖height‖) :=
    Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_direct
      sigmaPositive height
  have coordinateEquality :
      z / 2 = (sigma : ℂ) + (height : ℂ) * Complex.I :=
    regularInverseGamma_halfCoordinate z
  have gammaQuotientBoundAtConstant :
      ‖gammaQuotient‖ ≤
        Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma *
          (1 + ‖height‖) :=
    Eq.subst
      (motive := fun point : ℂ =>
        ‖deriv Complex.Gamma point / Complex.Gamma point‖ ≤
          Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma *
            (1 + ‖height‖))
      coordinateEquality.symm
      fixedLineBound
  have gammaConstantBound :
      Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma ≤ B :=
    uniformGammaBound sigma halfRealPartMembership
  have heightWeightNonnegative : 0 ≤ 1 + ‖height‖ :=
    Real.zero_le_one_add_norm height
  have gammaQuotientBoundAtUniformConstant :
      ‖gammaQuotient‖ ≤ B * (1 + ‖height‖) :=
    gammaQuotientBoundAtConstant.trans
      (mul_le_mul_of_nonneg_right gammaConstantBound
        heightWeightNonnegative)
  have heightNormBound : ‖height‖ ≤ ‖z.im‖ :=
    let divisorNormAtLeastOne : (1 : ℝ) ≤ ‖(2 : ℝ)‖ :=
      let twoNormEquality : ‖(2 : ℝ)‖ = (2 : ℝ) :=
        Real.norm_of_nonneg zero_le_two
      Eq.subst
        (motive := fun value : ℝ => 1 ≤ value)
        twoNormEquality.symm one_le_two
    Eq.subst
        (motive := fun value : ℝ => value ≤ ‖z.im‖)
        (norm_div z.im (2 : ℝ)).symm
        (div_le_self (norm_nonneg z.im) divisorNormAtLeastOne)
  have heightWeightBound :
      1 + ‖height‖ ≤ 1 + ‖z.im‖ :=
    add_le_add_left heightNormBound 1
  have gammaQuotientLinearBound :
      ‖gammaQuotient‖ ≤ B * (1 + ‖z.im‖) :=
    gammaQuotientBoundAtUniformConstant.trans
      (mul_le_mul_of_nonneg_left heightWeightBound boundNonnegative)
  have halfGammaEquality :
      (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
          Complex.Gamma (z / 2) =
        gammaQuotient * (1 / 2 : ℂ) :=
    mul_div_right_comm
      (deriv Complex.Gamma (z / 2))
      (1 / 2 : ℂ)
      (Complex.Gamma (z / 2))
  have halfGammaNormBound :
      ‖(deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
          Complex.Gamma (z / 2)‖ ≤
        (‖(1 / 2 : ℂ)‖ * B) * (1 + ‖z.im‖) :=
    let productNormEquality :
        ‖gammaQuotient * (1 / 2 : ℂ)‖ =
          ‖gammaQuotient‖ * ‖(1 / 2 : ℂ)‖ :=
      norm_mul gammaQuotient (1 / 2 : ℂ)
    let productBound :
        ‖gammaQuotient‖ * ‖(1 / 2 : ℂ)‖ ≤
          (B * (1 + ‖z.im‖)) * ‖(1 / 2 : ℂ)‖ :=
      mul_le_mul_of_nonneg_right gammaQuotientLinearBound
        (norm_nonneg (1 / 2 : ℂ))
    let productReassociation :
        (B * (1 + ‖z.im‖)) * ‖(1 / 2 : ℂ)‖ =
          (‖(1 / 2 : ℂ)‖ * B) * (1 + ‖z.im‖) :=
      Eq.trans
        (mul_assoc B (1 + ‖z.im‖) ‖(1 / 2 : ℂ)‖)
        (Eq.trans
          (congrArg (fun value : ℝ => B * value)
            (mul_comm (1 + ‖z.im‖) ‖(1 / 2 : ℂ)‖))
          (Eq.trans
            (mul_assoc B ‖(1 / 2 : ℂ)‖ (1 + ‖z.im‖)).symm
            (congrArg (fun value : ℝ => value * (1 + ‖z.im‖))
              (mul_comm B ‖(1 / 2 : ℂ)‖))))
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤ (‖(1 / 2 : ℂ)‖ * B) * (1 + ‖z.im‖))
      halfGammaEquality.symm
      (Eq.subst
        (motive := fun value : ℝ =>
          value ≤ (‖(1 / 2 : ℂ)‖ * B) * (1 + ‖z.im‖))
        productNormEquality.symm
        (productBound.trans_eq productReassociation))
  have piTermNonnegative : 0 ≤ ‖piTerm‖ := norm_nonneg piTerm
  have piTermLinearBound :
      ‖piTerm‖ ≤ ‖piTerm‖ * (1 + ‖z.im‖) :=
    calc
      ‖piTerm‖ = ‖piTerm‖ * 1 :=
        (mul_one ‖piTerm‖).symm
      _ ≤ ‖piTerm‖ * (1 + ‖z.im‖) :=
        mul_le_mul_of_nonneg_left
          (Real.one_le_one_add_norm z.im) piTermNonnegative
  have inverseGammaDecomposition :=
    inverseGammaCompletionLogDeriv_eq_neg_pi_add_halfGamma_of_re_pos
      z realPartPositive
  have inverseGammaNormSplit :
      ‖inverseGammaCompletionLogDeriv z‖ ≤
        ‖piTerm‖ +
          ‖(deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2)‖ :=
    let decompositionNorm :
        ‖inverseGammaCompletionLogDeriv z‖ =
          ‖piTerm +
            (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
              Complex.Gamma (z / 2)‖ :=
      Eq.trans (congrArg norm inverseGammaDecomposition)
        (norm_neg
          (piTerm +
            (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
              Complex.Gamma (z / 2)))
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ ‖piTerm‖ +
          ‖(deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2)‖)
      decompositionNorm.symm
      (norm_add_le piTerm
        ((deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
          Complex.Gamma (z / 2)))
  have sumBound :
      ‖piTerm‖ +
          ‖(deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2)‖ ≤
        ‖piTerm‖ * (1 + ‖z.im‖) +
          (‖(1 / 2 : ℂ)‖ * B) * (1 + ‖z.im‖) :=
    add_le_add piTermLinearBound halfGammaNormBound
  have factorEquality :
      ‖piTerm‖ * (1 + ‖z.im‖) +
          (‖(1 / 2 : ℂ)‖ * B) * (1 + ‖z.im‖) =
        (‖piTerm‖ + ‖(1 / 2 : ℂ)‖ * B) *
          (1 + ‖z.im‖) :=
    (add_mul ‖piTerm‖ (‖(1 / 2 : ℂ)‖ * B)
      (1 + ‖z.im‖)).symm
  inverseGammaNormSplit.trans (sumBound.trans_eq factorEquality)

/-- The inverse-Gamma factor has one linear vertical bound throughout the
closed centered strip used by the regular contour. -/
theorem exists_regularInverseGamma_shiftedStrip_linear_bound
    (family : ExplicitFormulaContourFamily) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x T : ℝ,
        x ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖inverseGammaCompletionLogDeriv
            ((1 / 2 : ℂ) + (x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          C * (1 + ‖T‖) :=
  let lowerHalfRealPart : ℝ := (1 / 2 : ℝ) / 2
  let upperHalfRealPart : ℝ := family.c / 2
  have lowerHalfRealPartPositive : 0 < lowerHalfRealPart :=
    div_pos one_half_pos zero_lt_two
  match exists_uniform_GammaLogDerivative_constant_on_positive_Icc
      lowerHalfRealPart upperHalfRealPart lowerHalfRealPartPositive with
  | ⟨B, boundNonnegative, uniformGammaBound⟩ =>
      let C : ℝ :=
        ‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖ +
          ‖(1 / 2 : ℂ)‖ * B
      have CNonnegative : 0 ≤ C :=
        add_nonneg
          (norm_nonneg
            (Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))))
          (mul_nonneg (norm_nonneg (1 / 2 : ℂ)) boundNonnegative)
      ⟨C, CNonnegative, fun x T membership =>
        let shiftedPoint : ℂ :=
          (1 / 2 : ℂ) + (x : ℂ) + (T : ℂ) * Complex.I
        let halfRealPart : ℝ := shiftedPoint.re / 2
        let shiftedRealPartEquality :
            shiftedPoint.re = (1 / 2 : ℝ) + x :=
          regularInverseGamma_shiftedPoint_re x T
        let shiftedImaginaryPartEquality :
            shiftedPoint.im = T :=
          regularInverseGamma_shiftedPoint_im x T
        let shiftedRealPartPositive : 0 < shiftedPoint.re :=
          let positiveSum : 0 < (1 / 2 : ℝ) + x :=
            add_pos_of_pos_of_nonneg one_half_pos membership.1
          Eq.subst
            (motive := fun value : ℝ => 0 < value)
            shiftedRealPartEquality.symm positiveSum
        let lowerRealPartBound :
            (1 / 2 : ℝ) ≤ shiftedPoint.re :=
          let lowerSumBound :
              (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) + x :=
            le_add_of_nonneg_right membership.1
          Eq.subst
            (motive := fun value : ℝ => (1 / 2 : ℝ) ≤ value)
            shiftedRealPartEquality.symm lowerSumBound
        let upperRealPartBound : shiftedPoint.re ≤ family.c :=
          let xPlusHalfBound : x + (1 / 2 : ℝ) ≤ family.c :=
            (le_sub_iff_add_le).mp membership.2
          let halfPlusXBound : (1 / 2 : ℝ) + x ≤ family.c :=
            Eq.subst
              (motive := fun value : ℝ => value ≤ family.c)
              (add_comm x (1 / 2 : ℝ)) xPlusHalfBound
          Eq.subst
            (motive := fun value : ℝ => value ≤ family.c)
            shiftedRealPartEquality.symm halfPlusXBound
        let halfRealPartMembership :
            halfRealPart ∈
              Set.Icc lowerHalfRealPart upperHalfRealPart :=
          let lowerHalfBound :
              (1 / 2 : ℝ) / 2 ≤ shiftedPoint.re / 2 :=
            div_le_div_of_nonneg_right lowerRealPartBound zero_le_two
          let upperHalfBound :
              shiftedPoint.re / 2 ≤ family.c / 2 :=
            div_le_div_of_nonneg_right upperRealPartBound zero_le_two
          ⟨lowerHalfBound, upperHalfBound⟩
        let rawBound :=
          inverseGammaCompletionLogDeriv_linear_bound_of_uniform_halfStrip
            shiftedPoint lowerHalfRealPart upperHalfRealPart B
            shiftedRealPartPositive halfRealPartMembership boundNonnegative
            uniformGammaBound
        Eq.subst
          (motive := fun value : ℝ =>
            ‖inverseGammaCompletionLogDeriv shiftedPoint‖ ≤ C * (1 + ‖value‖))
          shiftedImaginaryPartEquality
          rawBound⟩

/-- The regular-strip inverse-Gamma estimate transported to a canonical top
horizontal path.  The shifted-coordinate membership is kept explicit here;
the rectangle owner supplies that membership separately. -/
theorem exists_regularInverseGamma_topPath_linear_bound
    (family : ExplicitFormulaContourFamily) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x T : ℝ),
        x - (1 / 2 : ℝ) ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaTopPath
              (family.rectangle T) x)‖ ≤
          C * (1 + ‖T‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_regularInverseGamma_shiftedStrip_linear_bound family
  refine ⟨C, hC, ?_⟩
  intro x T hx
  have hshifted := hbound (x - (1 / 2 : ℝ)) T hx
  have hpath :=
    regularInverseGamma_topPath_eq_shiftedCenteredPoint family x T
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖inverseGammaCompletionLogDeriv value‖ ≤ C * (1 + ‖T‖))
    hpath.symm
    hshifted

/- The scheduled factor package uses the derivative quotient itself.  The
regular-strip estimate is already stated for the definitionally identical
`inverseGammaCompletionLogDeriv`; this owner lemma exposes that transport
without reintroducing a magnitude estimate for reciprocal Gamma. -/
theorem inverseGammaFactor_topPath_linear_bound_of_shifted_mem
    (family : ExplicitFormulaContourFamily)
    {C : ℝ}
    (hbound :
      ∀ (x T : ℝ),
        x - (1 / 2 : ℝ) ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaTopPath
              (family.rectangle T) x)‖ ≤
          C * (1 + ‖T‖))
    {x T : ℝ}
    (hx : x - (1 / 2 : ℝ) ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ))) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (zetaCompletedExplicitFormulaTopPath (family.rectangle T) x) /
        (Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath (family.rectangle T) x))⁻¹‖ ≤
      C * (1 + ‖T‖) := by
  exact hbound x T hx

/-- Right-half horizontal coordinates are exactly the shifted coordinates of
the regular-strip owner estimate. -/
theorem exists_regularInverseGamma_topPath_rightHalf_linear_bound
    (family : ExplicitFormulaContourFamily) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x T : ℝ),
        x ∈ Set.Icc (1 / 2 : ℝ) family.c →
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaTopPath
              (family.rectangle T) x)‖ ≤
          C * (1 + ‖T‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_regularInverseGamma_topPath_linear_bound family
  refine ⟨C, hC, ?_⟩
  intro x T hx
  have hshift_lower : 0 ≤ x - (1 / 2 : ℝ) :=
    sub_nonneg.mpr hx.1
  have hshift_upper : x - (1 / 2 : ℝ) ≤ family.c - (1 / 2 : ℝ) := by
    exact sub_le_sub_right hx.2 (1 / 2 : ℝ)
  exact hbound x T ⟨hshift_lower, hshift_upper⟩

/-- The same regular-strip estimate on the lower horizontal path. -/
theorem exists_regularInverseGamma_bottomPath_linear_bound
    (family : ExplicitFormulaContourFamily) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x T : ℝ),
        x - (1 / 2 : ℝ) ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaBottomPath
              (family.rectangle T) x)‖ ≤
          C * (1 + ‖T‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_regularInverseGamma_shiftedStrip_linear_bound family
  refine ⟨C, hC, ?_⟩
  intro x T hx
  have hshifted := hbound (x - (1 / 2 : ℝ)) (-T) hx
  have hpath :=
    regularInverseGamma_bottomPath_eq_shiftedCenteredPoint family x T
  have hpathBound := Eq.subst
    (motive := fun value : ℂ =>
      ‖inverseGammaCompletionLogDeriv value‖ ≤ C * (1 + ‖-T‖))
    hpath.symm
    hshifted
  have hnorm : ‖-T‖ = ‖T‖ := norm_neg T
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            (family.rectangle T) x)‖ ≤ C * (1 + value))
    hnorm
    hpathBound

/-- The corresponding right-half transport for the lower horizontal path. -/
theorem exists_regularInverseGamma_bottomPath_rightHalf_linear_bound
    (family : ExplicitFormulaContourFamily) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (x T : ℝ),
        x ∈ Set.Icc (1 / 2 : ℝ) family.c →
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaBottomPath
              (family.rectangle T) x)‖ ≤
          C * (1 + ‖T‖) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_regularInverseGamma_bottomPath_linear_bound family
  refine ⟨C, hC, ?_⟩
  intro x T hx
  have hshift_lower : 0 ≤ x - (1 / 2 : ℝ) :=
    sub_nonneg.mpr hx.1
  have hshift_upper : x - (1 / 2 : ℝ) ≤ family.c - (1 / 2 : ℝ) := by
    exact sub_le_sub_right hx.2 (1 / 2 : ℝ)
  exact hbound x T ⟨hshift_lower, hshift_upper⟩

/-- Order-three Paley-Wiener decay in the exact centered coordinates of the
regular contour carrier. -/
theorem exists_regularInverseGamma_probe_strip_orderThree_bound
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily) :
    ∃ D : ℝ, 0 < D ∧
      ∀ x T : ℝ,
        x ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f)
            ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          D * (1 + ‖T‖) ^ (-(3 : ℤ)) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let width : ℝ := family.c - (1 / 2 : ℝ)
  match zetaLaplaceTransform_verticalStripRapidDecay_of_compactSupport_smooth
      probe 0 width 3 with
  | ⟨D, DPositive, transformBound⟩ =>
      ⟨D, DPositive, fun x T membership =>
        let point : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
        let pointRealPart : point.re = x :=
          ofReal_add_mul_I_re x T
        let pointImaginaryPart : point.im = T :=
          ofReal_add_mul_I_im x T
        let laplaceBound :
            ‖Boundary.zetaLaplaceTransform
                probe.toZetaTestFunction' point‖ ≤
              D * (1 + ‖point.im‖) ^ (-(3 : ℤ)) :=
          transformBound point
            (Eq.subst
              (motive := fun value : ℝ => 0 ≤ value)
              pointRealPart.symm membership.1)
            (Eq.subst
              (motive := fun value : ℝ => value ≤ width)
              pointRealPart.symm membership.2)
        let phiEquality :
            zetaCompletedExplicitFormulaPhi probe point =
              Boundary.zetaLaplaceTransform
                probe.toZetaTestFunction' point :=
          congrFun (zetaCompletedExplicitFormulaPhi_eq_laplace probe) point
        Eq.subst
          (motive := fun value : ℝ =>
            ‖zetaCompletedExplicitFormulaPhi probe point‖ ≤
              D * (1 + ‖value‖) ^ (-(3 : ℤ)))
          pointImaginaryPart
          (Eq.subst
            (motive := fun value : ℂ =>
              ‖value‖ ≤ D * (1 + ‖point.im‖) ^ (-(3 : ℤ)))
            phiEquality.symm laplaceBound)⟩

/-- The regular contour carrier is uniformly inverse-quadratic on both
horizontal edges of the centered strip. -/
theorem exists_regularInverseGammaContourCarrier_inverseQuadratic_bound
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x T : ℝ,
        x ∈ Set.Icc 0 (family.c - (1 / 2 : ℝ)) →
        ‖zetaCompletedRegularInverseGammaContourCarrier f
            ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
          K * (1 + ‖T‖) ^ (-(2 : ℤ)) :=
  match exists_regularInverseGamma_shiftedStrip_linear_bound family,
      exists_regularInverseGamma_probe_strip_orderThree_bound f family with
  | ⟨C, CNonnegative, inverseGammaBound⟩,
      ⟨D, DPositive, transformBound⟩ =>
      let K : ℝ := C * D
      have DNonnegative : 0 ≤ D := le_of_lt DPositive
      have KNonnegative : 0 ≤ K := mul_nonneg CNonnegative DNonnegative
      ⟨K, KNonnegative, fun x T membership =>
        let base : ℝ := 1 + ‖T‖
        let point : ℂ := (x : ℂ) + (T : ℂ) * Complex.I
        let inverseBound :
            ‖inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + point)‖ ≤
              C * base :=
          let pointAssoc :
              (1 / 2 : ℂ) + (x : ℂ) + (T : ℂ) * Complex.I =
                (1 / 2 : ℂ) + point :=
            add_assoc (1 / 2 : ℂ) (x : ℂ)
              ((T : ℂ) * Complex.I)
          Eq.subst
            (motive := fun value : ℂ =>
              ‖inverseGammaCompletionLogDeriv value‖ ≤ C * base)
            pointAssoc
            (inverseGammaBound x T membership)
        let phiBound :
            ‖zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) point‖ ≤
              D * base ^ (-(3 : ℤ)) :=
          transformBound x T membership
        let inverseNormNonnegative :
            0 ≤ ‖inverseGammaCompletionLogDeriv
              ((1 / 2 : ℂ) + point)‖ :=
          norm_nonneg
            (inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + point))
        let rightMajorantNonnegative :
            0 ≤ D * base ^ (-(3 : ℤ)) :=
          mul_nonneg DNonnegative
            (zpow_nonneg (Real.zero_le_one_add_norm T) (-(3 : ℤ)))
        let productBound :
            ‖inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + point)‖ *
                ‖zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) point‖ ≤
              (C * base) * (D * base ^ (-(3 : ℤ))) :=
          (mul_le_mul_of_nonneg_left phiBound inverseNormNonnegative).trans
            (mul_le_mul_of_nonneg_right inverseBound
              rightMajorantNonnegative)
        let exponentCollapse :
            base * base ^ (-(3 : ℤ)) =
              base ^ (-(2 : ℤ)) :=
          let collapseWithPower :
              base ^ (1 : ℕ) * base ^ (-(3 : ℤ)) =
                base ^ (-(2 : ℤ)) :=
            one_add_norm_pow_mul_zpow_dominated_eq_decay 1 1 T
          Eq.subst
            (motive := fun value : ℝ =>
              value * base ^ (-(3 : ℤ)) = base ^ (-(2 : ℤ)))
            (pow_one base) collapseWithPower
        let majorantReassociation :
            (C * base) * (D * base ^ (-(3 : ℤ))) =
              K * base ^ (-(2 : ℤ)) :=
          let firstReassociation :
              (C * base) * (D * base ^ (-(3 : ℤ))) =
                (C * D) * (base * base ^ (-(3 : ℤ))) :=
            let decay : ℝ := base ^ (-(3 : ℤ))
            let firstStep :
                (C * base) * (D * decay) =
                  C * (base * (D * decay)) :=
              mul_assoc C base (D * decay)
            let innerAssocLeft :
                base * (D * decay) = (base * D) * decay :=
              (mul_assoc base D decay).symm
            let innerCommute :
                (base * D) * decay = (D * base) * decay :=
              congrArg (fun value : ℝ => value * decay) (mul_comm base D)
            let innerAssocRight :
                (D * base) * decay = D * (base * decay) :=
              mul_assoc D base decay
            let innerReassociation :
                base * (D * decay) = D * (base * decay) :=
              Eq.trans innerAssocLeft
                (Eq.trans innerCommute innerAssocRight)
            let secondStep :
                C * (base * (D * decay)) =
                  C * (D * (base * decay)) :=
              congrArg (fun value : ℝ => C * value) innerReassociation
            let thirdStep :
                C * (D * (base * decay)) =
                  (C * D) * (base * decay) :=
              (mul_assoc C D (base * decay)).symm
            Eq.trans
              firstStep
              (Eq.trans secondStep thirdStep)
          Eq.trans firstReassociation
            (Eq.trans
              (congrArg (fun value : ℝ => (C * D) * value) exponentCollapse)
              (Eq.refl (K * base ^ (-(2 : ℤ)))))
        let carrierNormEquality :
            ‖zetaCompletedRegularInverseGammaContourCarrier f point‖ =
              ‖inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + point)‖ *
                ‖zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) point‖ :=
          norm_mul
            (inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + point))
            (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) point)
        Eq.subst
          (motive := fun value : ℝ =>
            value ≤ K * base ^ (-(2 : ℤ)))
          carrierNormEquality.symm
          (productBound.trans_eq majorantReassociation)⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
