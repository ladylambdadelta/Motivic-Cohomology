import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanBinet
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineBinetConjugationCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ArchimedeanHermitianKernel

/-!
# Completed affine archimedean seed transport

The autocorrelation transform is expanded before the paired finite-Binet
integral is evaluated.  This isolates the remaining analysis as a seed-level
modulation identity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The seed product representing the transform of an autocorrelation. -/
noncomputable def zetaCompletedArchimedeanSeedAutocorrelationTransform
    (f : ZetaAdmissibleFunction)
    (z : ℂ) : ℂ :=
  zetaCompletedExplicitFormulaPhi f z *
    star (zetaCompletedExplicitFormulaPhi f (-star z))

/-- The seed autocorrelation transform has the dagger reflection symmetry
forced by its two factors. -/
theorem zetaCompletedArchimedeanSeedAutocorrelationTransform_neg_star
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaCompletedArchimedeanSeedAutocorrelationTransform f (-star z) =
      star (zetaCompletedArchimedeanSeedAutocorrelationTransform f z) :=
  let reflectedArgument : -star (-star z) = z :=
    Eq.trans
      (congrArg Neg.neg (star_neg (star z)))
      (Eq.trans
        (congrArg (fun value : ℂ => -(-value)) (star_star z))
        (neg_neg z))
  let reflectedTransform :
      zetaCompletedArchimedeanSeedAutocorrelationTransform f (-star z) =
        zetaCompletedExplicitFormulaPhi f (-star z) *
          star (zetaCompletedExplicitFormulaPhi f z) :=
    congrArg
      (fun value : ℂ =>
        zetaCompletedExplicitFormulaPhi f (-star z) *
          star (zetaCompletedExplicitFormulaPhi f value))
      reflectedArgument
  let conjugatedTransform :
      star (zetaCompletedArchimedeanSeedAutocorrelationTransform f z) =
        star (zetaCompletedExplicitFormulaPhi f z) *
          zetaCompletedExplicitFormulaPhi f (-star z) :=
    Eq.trans
      (Eq.refl
        (star
          (zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z)))))
      (Eq.trans
        (star_mul
          (zetaCompletedExplicitFormulaPhi f z)
          (star (zetaCompletedExplicitFormulaPhi f (-star z))))
        (Eq.trans
          (congrArg
            (fun value : ℂ =>
              value * star (zetaCompletedExplicitFormulaPhi f z))
            (star_star (zetaCompletedExplicitFormulaPhi f (-star z))))
          (mul_comm
            (zetaCompletedExplicitFormulaPhi f (-star z))
            (star (zetaCompletedExplicitFormulaPhi f z)))))
  Eq.trans reflectedTransform
    (Eq.trans
      (mul_comm
        (zetaCompletedExplicitFormulaPhi f (-star z))
        (star (zetaCompletedExplicitFormulaPhi f z)))
      conjugatedTransform.symm)

/-- Opposite heights on the right centered affine line are complex
conjugates. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineLine_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaRightCenteredAffineLine family (-t) =
      star
        (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) :=
  let realEquality :
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family (-t)).re =
        (star
          (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)).re :=
    Eq.trans
      (zetaCompletedExplicitFormulaRightCenteredAffineLine_re family (-t))
      (Eq.trans
        (zetaCompletedExplicitFormulaRightCenteredAffineLine_re family t).symm
        (Eq.refl
          ((zetaCompletedExplicitFormulaRightCenteredAffineLine family t).re)))
  let imaginaryEquality :
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family (-t)).im =
        (star
          (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)).im :=
    Eq.trans
      (zetaCompletedExplicitFormulaRightCenteredAffineLine_im family (-t))
      (Eq.trans
        (congrArg Neg.neg
          (zetaCompletedExplicitFormulaRightCenteredAffineLine_im family t).symm)
        (Eq.refl
          (-(zetaCompletedExplicitFormulaRightCenteredAffineLine family t).im)))
  Complex.ext realEquality imaginaryEquality

/-- Opposite heights on the uncentered right affine line are complex
conjugates. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine family (-t) =
      star (zetaCompletedExplicitFormulaRightAffineLine family t) :=
  let realEquality :
      (zetaCompletedExplicitFormulaRightAffineLine family (-t)).re =
        (star (zetaCompletedExplicitFormulaRightAffineLine family t)).re :=
    Eq.trans
      (zetaCompletedExplicitFormulaRightAffineLine_re family (-t))
      (Eq.trans
        (zetaCompletedExplicitFormulaRightAffineLine_re family t).symm
        (Eq.refl
          ((zetaCompletedExplicitFormulaRightAffineLine family t).re)))
  let imaginaryEquality :
      (zetaCompletedExplicitFormulaRightAffineLine family (-t)).im =
        (star (zetaCompletedExplicitFormulaRightAffineLine family t)).im :=
    Eq.trans
      (zetaCompletedExplicitFormulaRightAffineLine_im family (-t))
      (Eq.trans
        (congrArg Neg.neg
          (zetaCompletedExplicitFormulaRightAffineLine_im family t).symm)
        (Eq.refl
          (-(zetaCompletedExplicitFormulaRightAffineLine family t).im)))
  Complex.ext realEquality imaginaryEquality

/-- The left centered affine fiber is the dagger reflection of the right
centered affine fiber at the same height. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_star_right
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaLeftCenteredAffineLine family t =
      -star
        (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) :=
  Eq.trans
    (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine
      family t)
    (congrArg Neg.neg
      (zetaCompletedExplicitFormulaRightCenteredAffineLine_neg_eq_star
        family t))

/-- The seed values on the two centered affine fibers are conjugate. -/
theorem zetaCompletedArchimedeanSeedAutocorrelationTransform_left_eq_star_right
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedArchimedeanSeedAutocorrelationTransform f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t) =
      star
        (zetaCompletedArchimedeanSeedAutocorrelationTransform f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)) :=
  Eq.trans
    (congrArg
      (zetaCompletedArchimedeanSeedAutocorrelationTransform f)
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_star_right
        family t))
    (zetaCompletedArchimedeanSeedAutocorrelationTransform_neg_star
      f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family t))

/-- The explicit seed-level paired affine finite-Binet kernel. -/
noncomputable def zetaCompletedAffineArchimedeanSeedPairedBinetKernel
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (zetaCompletedAffineArchimedeanRightBinetMainFactor family t *
      zetaCompletedArchimedeanSeedAutocorrelationTransform f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) +
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t *
      zetaCompletedArchimedeanSeedAutocorrelationTransform f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)) -
    ((-zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t)) *
        zetaCompletedArchimedeanSeedAutocorrelationTransform f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t) +
      (-zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t)) *
        zetaCompletedArchimedeanSeedAutocorrelationTransform f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t))

/-- The paired Binet kernel in one-fiber dagger normal form. -/
noncomputable def zetaCompletedAffineArchimedeanSeedDaggerBinetKernel
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  let rightSeed : ℂ :=
    zetaCompletedArchimedeanSeedAutocorrelationTransform f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)
  (zetaCompletedAffineArchimedeanRightBinetMainFactor family t * rightSeed +
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t *
      rightSeed) -
    ((-zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t)) *
        star rightSeed +
      (-zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t)) *
        star rightSeed)

/-- The combined scalar finite-Binet factor on the right affine line. -/
noncomputable def zetaCompletedAffineArchimedeanRightBinetFactor
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  zetaCompletedAffineArchimedeanRightBinetMainFactor family t +
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t

/-- The combined finite-Binet factor is the right affine archimedean
logarithmic derivative. -/
theorem zetaCompletedAffineArchimedeanRightBinetFactor_eq_logDerivative
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanRightBinetFactor family t =
      explicitFormulaArchimedeanLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine family t) :=
  (explicitFormulaArchimedeanLogDerivative_rightAffineLine_eq_binetFactors_shiftOwner
    family t).symm

/-- Opposite heights of the combined right finite-Binet scalar are
conjugates. -/
noncomputable def zetaCompletedAffineArchimedeanRightBinetCoreMainFactor
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalMain
        (family.c / 2) (t / 2))

/-- Opposite heights of the logarithmic finite-Binet main factor are
conjugates. -/
theorem zetaCompletedAffineArchimedeanRightBinetCoreMainFactor_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanRightBinetCoreMainFactor family (-t) =
      star
        (zetaCompletedAffineArchimedeanRightBinetCoreMainFactor family t) :=
  let sigma : ℝ := family.c / 2
  let height : ℝ := t / 2
  let gammaValue : ℂ :=
    Complex.GammaLogDerivativeFixedVerticalMain sigma height
  let sigmaPositive : 0 < sigma :=
    div_pos family.c_pos zero_lt_two
  let negativeHeight : (-t) / 2 = -height :=
    neg_div (2 : ℝ) t
  let gammaEquality :
      Complex.GammaLogDerivativeFixedVerticalMain sigma ((-t) / 2) =
        star gammaValue :=
    Eq.trans
      (congrArg
        (Complex.GammaLogDerivativeFixedVerticalMain sigma)
        negativeHeight)
      (gammaLogDerivativeFixedVerticalMain_neg_eq_star sigmaPositive)
  let halfStar : star (1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    Eq.trans (star_div₀ (1 : ℂ) (2 : ℂ))
      (congrArg₂ HDiv.hDiv
        (star_one (R := ℂ))
        (star_ofNat 2))
  let scaledGammaEquality :
      (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain sigma ((-t) / 2) =
        star ((1 / 2 : ℂ) * gammaValue) :=
    Eq.trans
      (congrArg (fun value : ℂ => (1 / 2 : ℂ) * value) gammaEquality)
      (Eq.trans
        (mul_comm (1 / 2 : ℂ) (star gammaValue))
        (Eq.trans
          (congrArg
            (fun value : ℂ => star gammaValue * value)
            halfStar.symm)
          (star_mul (1 / 2 : ℂ) gammaValue).symm))
  let piEquality :
      zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm =
        star zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm :=
    gammaRealPiLogDerivativeTerm_star.symm
  let sumEquality :
      zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain sigma ((-t) / 2) =
        star
          (zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) * gammaValue) :=
    Eq.trans
      (congrArg₂ HAdd.hAdd piEquality scaledGammaEquality)
      (star_add
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
        ((1 / 2 : ℂ) * gammaValue)).symm
  Eq.trans
    (congrArg Neg.neg sumEquality)
    (star_neg
      (zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) * gammaValue)).symm

/-- The elementary correction on opposite right affine heights is
conjugate. -/
theorem explicitFormulaCorrectionLogDerivative_rightAffineLine_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine family (-t)) =
      star
        (explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine family t)) :=
  Eq.trans
    (congrArg explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine_neg_eq_star family t))
    (explicitFormulaCorrectionLogDerivative_star_shiftOwner
      (zetaCompletedExplicitFormulaRightAffineLine family t)).symm

/-- Opposite heights of the combined right finite-Binet scalar are
conjugates. -/
theorem zetaCompletedAffineArchimedeanRightBinetMainFactor_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t) =
      star
        (zetaCompletedAffineArchimedeanRightBinetMainFactor family t) :=
  let coreEquality :
      zetaCompletedAffineArchimedeanRightBinetCoreMainFactor family (-t) =
        star
          (zetaCompletedAffineArchimedeanRightBinetCoreMainFactor family t) :=
    zetaCompletedAffineArchimedeanRightBinetCoreMainFactor_neg_eq_star
      family t
  let correctionEquality :
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine family (-t)) =
        star
          (explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine family t)) :=
    explicitFormulaCorrectionLogDerivative_rightAffineLine_neg_eq_star
      family t
  Eq.trans
    (congrArg₂ HSub.hSub coreEquality correctionEquality)
    (star_sub
      (zetaCompletedAffineArchimedeanRightBinetCoreMainFactor family t)
      (explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine family t))).symm

/-- Opposite heights of the differentiated Abel--Plana remainder factor are
conjugates. -/
theorem zetaCompletedAffineArchimedeanRightBinetRemainderFactor_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t) =
      star
        (zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t) :=
  let sigma : ℝ := family.c / 2
  let height : ℝ := t / 2
  let remainder : ℂ :=
    Complex.GammaLogDerivativeFixedVerticalRemainder sigma height
  let negativeHeight : (-t) / 2 = -height :=
    neg_div (2 : ℝ) t
  let remainderEquality :
      Complex.GammaLogDerivativeFixedVerticalRemainder sigma ((-t) / 2) =
        star remainder :=
    Eq.trans
      (congrArg
        (Complex.GammaLogDerivativeFixedVerticalRemainder sigma)
        negativeHeight)
      (gammaLogDerivativeFixedVerticalRemainder_neg_eq_star sigma height)
  let halfStar : star (1 / 2 : ℂ) = (1 / 2 : ℂ) :=
    Eq.trans (star_div₀ (1 : ℂ) (2 : ℂ))
      (congrArg₂ HDiv.hDiv
        (star_one (R := ℂ))
        (star_ofNat 2))
  let productEquality :
      (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder sigma ((-t) / 2) =
        star ((1 / 2 : ℂ) * remainder) :=
    Eq.trans
      (congrArg (fun value : ℂ => (1 / 2 : ℂ) * value)
        remainderEquality)
      (Eq.trans
        (mul_comm (1 / 2 : ℂ) (star remainder))
        (Eq.trans
          (congrArg
            (fun value : ℂ => star remainder * value)
            halfStar.symm)
          (star_mul (1 / 2 : ℂ) remainder).symm))
  Eq.trans
    (congrArg Neg.neg productEquality)
    (star_neg ((1 / 2 : ℂ) * remainder)).symm

/-- Opposite heights of the combined right finite-Binet scalar are
conjugates. -/
theorem zetaCompletedAffineArchimedeanRightBinetFactor_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanRightBinetFactor family (-t) =
      star (zetaCompletedAffineArchimedeanRightBinetFactor family t) :=
  let mainEquality :
      zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t) =
        star
          (zetaCompletedAffineArchimedeanRightBinetMainFactor family t) :=
    zetaCompletedAffineArchimedeanRightBinetMainFactor_neg_eq_star
      family t
  let remainderEquality :
      zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t) =
        star
          (zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t) :=
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor_neg_eq_star
      family t
  Eq.trans
    (congrArg₂ HAdd.hAdd mainEquality remainderEquality)
    (star_add
      (zetaCompletedAffineArchimedeanRightBinetMainFactor family t)
      (zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t)).symm

/-- The Hermitianized right-fiber seed kernel. -/
noncomputable def zetaCompletedAffineArchimedeanSeedHermitianRightKernel
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  let value : ℂ :=
    zetaCompletedAffineArchimedeanRightBinetFactor family t *
      zetaCompletedArchimedeanSeedAutocorrelationTransform f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)
  value + star value

/-- Four scalar terms regroup into a factor and its reflected factor. -/
theorem zetaCompletedAffineArchimedean_dagger_packet_regroup
    (main remainder reflectedMain reflectedRemainder seed : ℂ) :
    (main * seed + remainder * seed) -
        ((-reflectedMain) * star seed +
          (-reflectedRemainder) * star seed) =
      (main + remainder) * seed +
        (reflectedMain + reflectedRemainder) * star seed :=
  let rightRegroup :
      main * seed + remainder * seed =
        (main + remainder) * seed :=
    (add_mul main remainder seed).symm
  let reflectedRegroup :
      (-reflectedMain) * star seed +
          (-reflectedRemainder) * star seed =
        -((reflectedMain + reflectedRemainder) * star seed) :=
    Eq.trans
      (congrArg₂ HAdd.hAdd
          (neg_mul reflectedMain (star seed))
          (neg_mul reflectedRemainder (star seed)))
      (Eq.trans
        (neg_add
          (reflectedMain * star seed)
          (reflectedRemainder * star seed)).symm
        (congrArg Neg.neg
          (add_mul reflectedMain reflectedRemainder (star seed)).symm))
  Eq.trans
    (congrArg₂ HSub.hSub rightRegroup reflectedRegroup)
    (sub_neg_eq_add
        ((main + remainder) * seed)
        ((reflectedMain + reflectedRemainder) * star seed))

/-- The one-fiber dagger packet is pointwise the Hermitianized right-fiber
kernel. -/
theorem zetaCompletedAffineArchimedeanSeedDaggerBinetKernel_eq_hermitianRight
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanSeedDaggerBinetKernel f family t =
      zetaCompletedAffineArchimedeanSeedHermitianRightKernel
        f family t :=
  let seed : ℂ :=
    zetaCompletedArchimedeanSeedAutocorrelationTransform f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)
  let factor : ℂ :=
    zetaCompletedAffineArchimedeanRightBinetFactor family t
  let regrouped :
      zetaCompletedAffineArchimedeanSeedDaggerBinetKernel f family t =
        factor * seed +
          zetaCompletedAffineArchimedeanRightBinetFactor family (-t) *
            star seed :=
    zetaCompletedAffineArchimedean_dagger_packet_regroup
      (zetaCompletedAffineArchimedeanRightBinetMainFactor family t)
      (zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t)
      (zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t))
      (zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t))
      seed
  let reflectedFactor :
      zetaCompletedAffineArchimedeanRightBinetFactor family (-t) =
        star factor :=
    zetaCompletedAffineArchimedeanRightBinetFactor_neg_eq_star family t
  let reflectedProduct :
      zetaCompletedAffineArchimedeanRightBinetFactor family (-t) *
          star seed =
        star (factor * seed) :=
    Eq.trans
      (congrArg (fun value : ℂ => value * star seed) reflectedFactor)
      (Eq.trans
        (mul_comm (star factor) (star seed))
        (star_mul factor seed).symm)
  Eq.trans regrouped
    (congrArg
      (fun value : ℂ => factor * seed + value)
      reflectedProduct)

/-- The two-fiber seed packet is pointwise its one-fiber dagger normal form. -/
theorem zetaCompletedAffineArchimedeanSeedPairedBinetKernel_eq_dagger
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanSeedPairedBinetKernel f family t =
      zetaCompletedAffineArchimedeanSeedDaggerBinetKernel f family t :=
  let rightSeed : ℂ :=
    zetaCompletedArchimedeanSeedAutocorrelationTransform f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)
  let leftSeed :
      zetaCompletedArchimedeanSeedAutocorrelationTransform f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine family t) =
        star rightSeed :=
    zetaCompletedArchimedeanSeedAutocorrelationTransform_left_eq_star_right
      f family t
  congrArg
    (fun reflectedSeed : ℂ =>
      (zetaCompletedAffineArchimedeanRightBinetMainFactor family t *
          rightSeed +
        zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t *
          rightSeed) -
        ((-zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t)) *
            reflectedSeed +
          (-zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t)) *
            reflectedSeed))
    leftSeed

/-- The paired autocorrelation Binet kernel unfolds to the seed-level paired
kernel. -/
theorem zetaCompletedAffineArchimedeanPairedBinetKernel_convolutionAutocorrelation_eq_seed
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanPairedBinetKernel
        (convolutionAutocorrelation f) family t =
      zetaCompletedAffineArchimedeanSeedPairedBinetKernel
        f family t :=
  let rightPoint : ℂ :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine family t
  let leftPoint : ℂ :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine family t
  let rightTransform :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) rightPoint =
        zetaCompletedArchimedeanSeedAutocorrelationTransform
          f rightPoint :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
      f rightPoint
  let leftTransform :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) leftPoint =
        zetaCompletedArchimedeanSeedAutocorrelationTransform
          f leftPoint :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
      f leftPoint
  let rightMain : ℂ :=
    zetaCompletedAffineArchimedeanRightBinetMainFactor family t
  let rightRemainder : ℂ :=
    zetaCompletedAffineArchimedeanRightBinetRemainderFactor family t
  let reflectedMain : ℂ :=
    -zetaCompletedAffineArchimedeanRightBinetMainFactor family (-t)
  let reflectedRemainder : ℂ :=
    -zetaCompletedAffineArchimedeanRightBinetRemainderFactor family (-t)
  congrArg₂ HSub.hSub
    (congrArg₂ HAdd.hAdd
      (congrArg (fun value : ℂ => rightMain * value) rightTransform)
      (congrArg
        (fun value : ℂ => rightRemainder * value)
        rightTransform))
    (congrArg₂ HAdd.hAdd
      (congrArg (fun value : ℂ => reflectedMain * value) leftTransform)
      (congrArg
        (fun value : ℂ => reflectedRemainder * value)
        leftTransform))

/-- The seed-level centered archimedean integrand. -/
noncomputable def zetaCompletedCenteredArchimedeanSeedIntegrand
    (f : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  explicitFormulaArchimedeanLogDerivative
      (zetaCompletedCenteredSpectralLine t) *
    (zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
      star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)))

/-- The centered autocorrelation archimedean integrand is its seed-level Gram
integrand. -/
theorem zetaCompletedArchimedeanCenteredIntegrand_convolutionAutocorrelation_eq_seed
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedArchimedeanCenteredIntegrand
        (convolutionAutocorrelation f) t =
      zetaCompletedCenteredArchimedeanSeedIntegrand f t :=
  let transformEquality :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (t * Complex.I) =
        zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
          star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_imaginary
      f t
  congrArg
    (fun value : ℂ =>
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedCenteredSpectralLine t) * value)
    transformEquality

/-- The seed-level Hermitian archimedean Gram integrand. -/
noncomputable def zetaCompletedHermitianArchimedeanSeedIntegrand
    (f : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  zetaCompletedArchimedeanHermitianKernel t *
    (zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
      star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)))

/-- The Hermitian autocorrelation integrand is its seed-level Gram
integrand. -/
theorem zetaCompletedArchimedeanHermitianIntegrand_convolutionAutocorrelation_eq_seed
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedArchimedeanHermitianIntegrand
        (convolutionAutocorrelation f) t =
      zetaCompletedHermitianArchimedeanSeedIntegrand f t :=
  let transformEquality :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (t * Complex.I) =
        zetaCompletedExplicitFormulaPhi f (t * Complex.I) *
          star (zetaCompletedExplicitFormulaPhi f (t * Complex.I)) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_imaginary
      f t
  congrArg
    (fun value : ℂ =>
      zetaCompletedArchimedeanHermitianKernel t * value)
    transformEquality

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
