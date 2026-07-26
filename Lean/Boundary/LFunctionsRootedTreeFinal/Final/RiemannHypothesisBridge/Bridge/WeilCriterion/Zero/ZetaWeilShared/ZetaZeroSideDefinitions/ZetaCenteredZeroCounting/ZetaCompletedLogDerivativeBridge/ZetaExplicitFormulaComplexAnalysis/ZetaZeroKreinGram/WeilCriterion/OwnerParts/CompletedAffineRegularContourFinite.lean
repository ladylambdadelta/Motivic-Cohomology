import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanSeedTransport

/-!
# Finite regular inverse-Gamma contour

This file owns the finite-strip Cauchy transport and horizontal-edge decay.
The whole-line transport is assembled in the downstream transport owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The one-sided critical-line inverse-Gamma seed kernel. -/
noncomputable def zetaCompletedCriticalInverseGammaSeedKernel
    (f : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  inverseGammaCompletionLogDeriv
      (zetaCompletedCenteredSpectralLine t) *
    zetaCompletedArchimedeanSeedAutocorrelationTransform f
      (t * Complex.I)

/-- The holomorphic carrier whose vertical restrictions are the affine and
critical one-sided inverse-Gamma kernels. -/
noncomputable def zetaCompletedRegularInverseGammaContourCarrier
    (f : ZetaAdmissibleFunction)
    (z : ℂ) : ℂ :=
  inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + z) *
    zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z

/-- The finite symmetric window of the one-sided affine right kernel. -/
noncomputable def zetaCompletedAffineInverseGammaRightWindow
    (f : ZetaAdmissibleFunction)
    (T : ℝ) : ℂ :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  ∫ t in Set.Icc (-T) T,
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family t

/-- The finite symmetric window of the one-sided critical kernel. -/
noncomputable def zetaCompletedCriticalInverseGammaWindow
    (f : ZetaAdmissibleFunction)
    (T : ℝ) : ℂ :=
  ∫ t in Set.Icc (-T) T,
    zetaCompletedCriticalInverseGammaSeedKernel f t

/-- The oriented horizontal-edge defect in the regular inverse-Gamma strip
rectangle. -/
noncomputable def zetaCompletedRegularInverseGammaHorizontalDefect
    (f : ZetaAdmissibleFunction)
    (T : ℝ) : ℂ :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  (-Complex.I) *
    ((∫ x in Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)),
        zetaCompletedRegularInverseGammaContourCarrier f
          ((x : ℂ) + (T : ℂ) * Complex.I)) -
      ∫ x in Set.Icc (0 : ℝ) (family.c - (1 / 2 : ℝ)),
        zetaCompletedRegularInverseGammaContourCarrier f
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))

/-- The reciprocal-Gamma logarithmic derivative is holomorphic throughout
the positive real half-plane. -/
theorem inverseGammaCompletionLogDeriv_differentiableAt_of_re_pos
    (s : ℂ)
    (realPartPositive : 0 < s.re) :
    DifferentiableAt ℂ inverseGammaCompletionLogDeriv s :=
  let reciprocalGamma : ℂ → ℂ := fun z : ℂ => (Complex.Gammaℝ z)⁻¹
  let reciprocalGammaDifferentiable :
      Differentiable ℂ reciprocalGamma :=
    Complex.differentiable_Gammaℝ_inv
  let reciprocalGammaAnalytic :
      AnalyticOnNhd ℂ reciprocalGamma Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      reciprocalGammaDifferentiable
  let derivativeAnalytic :
      AnalyticOnNhd ℂ (deriv reciprocalGamma) Set.univ :=
    reciprocalGammaAnalytic.deriv
  let gammaNonzero : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos realPartPositive
  let reciprocalGammaNonzero : reciprocalGamma s ≠ 0 :=
    inv_ne_zero gammaNonzero
  let quotientAnalytic :
      AnalyticAt ℂ
        (fun z : ℂ => deriv reciprocalGamma z / reciprocalGamma z)
        s :=
    (derivativeAnalytic s (Set.mem_univ s)).div
      (reciprocalGammaAnalytic s (Set.mem_univ s))
      reciprocalGammaNonzero
  let quotientDifferentiable :
      DifferentiableAt ℂ
        (fun z : ℂ => deriv reciprocalGamma z / reciprocalGamma z)
        s :=
    quotientAnalytic.differentiableAt
  Eq.subst
    (motive := fun candidate : ℂ → ℂ => DifferentiableAt ℂ candidate s)
    (funext
      (fun z : ℂ => inverseGammaCompletionLogDeriv_eq z)).symm
    quotientDifferentiable

/-- The regular inverse-Gamma contour carrier is holomorphic wherever the
shifted spectral coordinate has positive real part. -/
theorem zetaCompletedRegularInverseGammaContourCarrier_differentiableAt
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (z : ℂ)
    (shiftedRealPartPositive : 0 < (((1 / 2 : ℂ) + z).re)) :
    DifferentiableAt ℂ
      (zetaCompletedRegularInverseGammaContourCarrier f)
      z :=
  let shiftDifferentiable :
      DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    differentiableAt_const (c := (1 / 2 : ℂ)).add differentiableAt_id
  let inverseGammaDifferentiable :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          inverseGammaCompletionLogDeriv ((1 / 2 : ℂ) + w))
        z :=
    (inverseGammaCompletionLogDeriv_differentiableAt_of_re_pos
      ((1 / 2 : ℂ) + z) shiftedRealPartPositive).comp
      z shiftDifferentiable
  let transformDifferentiable :
      DifferentiableAt ℂ
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f))
        z :=
    hPhi.differentiableAt z
  inverseGammaDifferentiable.mul transformDifferentiable

/-- A set integral over an ordered closed real interval equals the
corresponding oriented interval integral. -/
theorem regularInverseGamma_setIntegral_Icc_eq_intervalIntegral
    (integrand : ℝ → ℂ)
    (a b : ℝ)
    (ordered : a ≤ b) :
    (∫ x in Set.Icc a b, integrand x) =
      ∫ x : ℝ in a..b, integrand x :=
  let intervalEquality :
      (∫ x : ℝ in a..b, integrand x) =
        ∫ x in Set.Ioc a b, integrand x :=
    intervalIntegral.integral_of_le ordered
  let endpointEquality :
      (∫ x in Set.Icc a b, integrand x) =
        ∫ x in Set.Ioc a b, integrand x :=
    MeasureTheory.integral_Icc_eq_integral_Ioc
  Eq.trans endpointEquality intervalEquality.symm

/-- A nonnegative height orders its symmetric interval. -/
theorem regularInverseGamma_neg_le_self
    (T : ℝ)
    (heightNonnegative : 0 ≤ T) :
    -T ≤ T :=
  le_trans (neg_nonpos.mpr heightNonnegative) heightNonnegative

/-- The centered width of a completed contour family is positive. -/
theorem regularInverseGamma_centeredWidth_positive
    (family : ExplicitFormulaContourFamily) :
    0 < family.c - (1 / 2 : ℝ) :=
  let oneLessThanC : (1 : ℝ) < family.c :=
    sub_neg.mp family.one_sub_c_neg
  let halfLessThanOne : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  sub_pos.mpr (lt_trans halfLessThanOne oneLessThanC)

/-- Shifting the centered affine right coordinate by one half gives the
ordinary affine right coordinate. -/
theorem regularInverseGamma_shiftedRightCenteredLine
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    (1 / 2 : ℂ) +
        (((family.c : ℂ) - (1 / 2 : ℂ)) +
          (t : ℂ) * Complex.I) =
      (family.c : ℂ) + (t : ℂ) * Complex.I :=
  let scalarCancellation :
      (1 / 2 : ℂ) + ((family.c : ℂ) - (1 / 2 : ℂ)) =
        (family.c : ℂ) :=
    Eq.trans
      (add_comm (1 / 2 : ℂ) ((family.c : ℂ) - (1 / 2 : ℂ)))
      (sub_add_cancel (family.c : ℂ) (1 / 2 : ℂ))
  Eq.trans
    (add_assoc
      (1 / 2 : ℂ)
      ((family.c : ℂ) - (1 / 2 : ℂ))
      ((t : ℂ) * Complex.I)).symm
    (congrArg
      (fun value : ℂ => value + (t : ℂ) * Complex.I)
      scalarCancellation)

/-- The regular contour carrier restricts on the right vertical edge to the
one-sided affine inverse-Gamma kernel. -/
theorem zetaCompletedRegularInverseGammaContourCarrier_rightEdge
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedRegularInverseGammaContourCarrier f
        (((family.c : ℂ) - (1 / 2 : ℂ)) +
          (t : ℂ) * Complex.I) =
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        (convolutionAutocorrelation f) family t :=
  let centeredPoint : ℂ :=
    ((family.c : ℂ) - (1 / 2 : ℂ)) + (t : ℂ) * Complex.I
  let shiftedPoint :
      (1 / 2 : ℂ) + centeredPoint =
        zetaCompletedExplicitFormulaRightAffineLine family t :=
    regularInverseGamma_shiftedRightCenteredLine family t
  let centeredPointEquality :
      centeredPoint =
        zetaCompletedExplicitFormulaRightCenteredAffineLine family t :=
    rfl
  congrArg₂ HMul.hMul
    (congrArg inverseGammaCompletionLogDeriv shiftedPoint)
    (congrArg
      (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f))
      centeredPointEquality)

/-- The regular contour carrier restricts on the critical vertical edge to
the one-sided critical seed kernel. -/
theorem zetaCompletedRegularInverseGammaContourCarrier_criticalEdge
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedRegularInverseGammaContourCarrier f
        ((t : ℂ) * Complex.I) =
      zetaCompletedCriticalInverseGammaSeedKernel f t :=
  let shiftedPoint :
      (1 / 2 : ℂ) + (t : ℂ) * Complex.I =
        zetaCompletedCenteredSpectralLine t :=
    rfl
  let transformEquality :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) ((t : ℂ) * Complex.I) =
        zetaCompletedArchimedeanSeedAutocorrelationTransform f
          ((t : ℂ) * Complex.I) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
      f ((t : ℂ) * Complex.I)
  congrArg₂ HMul.hMul
    (congrArg inverseGammaCompletionLogDeriv shiftedPoint)
    transformEquality

/-- Nonnegative centered real coordinate places the shifted carrier in the
positive real half-plane. -/
theorem regularInverseGamma_shifted_re_positive_of_re_nonnegative
    (z : ℂ)
    (realPartNonnegative : 0 ≤ z.re) :
    0 < (((1 / 2 : ℂ) + z).re) :=
  let halfAsOfReal : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) :=
    (Complex.ofReal_div (1 : ℝ) (2 : ℝ)).symm
  let halfRealPart : (1 / 2 : ℂ).re = (1 / 2 : ℝ) :=
    Eq.trans
      (congrArg Complex.re halfAsOfReal)
      (Complex.ofReal_re (1 / 2 : ℝ))
  let realPartEquality :
      (((1 / 2 : ℂ) + z).re) = (1 / 2 : ℝ) + z.re :=
    Eq.trans
      (Complex.add_re (1 / 2 : ℂ) z)
      (congrArg
        (fun value : ℝ => value + z.re)
        halfRealPart)
  let positiveSum : 0 < (1 / 2 : ℝ) + z.re :=
    add_pos_of_pos_of_nonneg one_half_pos realPartNonnegative
  Eq.subst
    (motive := fun value : ℝ => 0 < value)
    realPartEquality.symm
    positiveSum

/-- Every point of the finite centered strip rectangle has nonnegative real
coordinate. -/
theorem regularInverseGamma_rectangle_re_nonnegative
    (family : ExplicitFormulaContourFamily)
    (T : ℝ)
    (z : ℂ)
    (membership :
      z ∈
        (Set.uIcc
            ((Complex.mk 0 (-T)).re)
            ((Complex.mk (family.c - (1 / 2 : ℝ)) T).re) ×ℂ
          Set.uIcc
            ((Complex.mk 0 (-T)).im)
            ((Complex.mk (family.c - (1 / 2 : ℝ)) T).im))) :
    0 ≤ z.re :=
  let width : ℝ := family.c - (1 / 2 : ℝ)
  let widthNonnegative : 0 ≤ width :=
    le_of_lt (regularInverseGamma_centeredWidth_positive family)
  let realMembership : z.re ∈ Set.uIcc 0 width :=
    membership.1
  let orderedInterval : Set.uIcc 0 width = Set.Icc 0 width :=
    Set.uIcc_of_le widthNonnegative
  let orderedMembership : z.re ∈ Set.Icc 0 width :=
    Eq.subst
      (motive := fun interval : Set ℝ => z.re ∈ interval)
      orderedInterval
      realMembership
  orderedMembership.1

/-- The regular carrier is differentiable on the closed finite strip
rectangle. -/
theorem zetaCompletedRegularInverseGammaContourCarrier_differentiableOn_rectangle
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (family : ExplicitFormulaContourFamily)
    (T : ℝ) :
    DifferentiableOn ℂ
      (zetaCompletedRegularInverseGammaContourCarrier f)
      (Set.uIcc
          ((Complex.mk 0 (-T)).re)
          ((Complex.mk (family.c - (1 / 2 : ℝ)) T).re) ×ℂ
        Set.uIcc
          ((Complex.mk 0 (-T)).im)
          ((Complex.mk (family.c - (1 / 2 : ℝ)) T).im)) :=
  fun z membership =>
  let realPartNonnegative : 0 ≤ z.re :=
    regularInverseGamma_rectangle_re_nonnegative
      family T z membership
  let shiftedRealPartPositive : 0 < (((1 / 2 : ℂ) + z).re) :=
    regularInverseGamma_shifted_re_positive_of_re_nonnegative
      z realPartNonnegative
  (zetaCompletedRegularInverseGammaContourCarrier_differentiableAt
    f hPhi z shiftedRealPartPositive).differentiableWithinAt

/-- Cauchy-Goursat gives the oriented boundary equation for the finite
centered strip rectangle. -/
theorem zetaCompletedRegularInverseGamma_rectangleBoundary_eq_zero
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (family : ExplicitFormulaContourFamily)
    (T : ℝ) :
    (∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
        zetaCompletedRegularInverseGammaContourCarrier f
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
        zetaCompletedRegularInverseGammaContourCarrier f
          ((x : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I •
        (∫ t : ℝ in (-T)..T,
          zetaCompletedRegularInverseGammaContourCarrier f
            (((family.c : ℂ) - (1 / 2 : ℂ)) +
              (t : ℂ) * Complex.I)) -
      Complex.I •
        (∫ t : ℝ in (-T)..T,
          zetaCompletedRegularInverseGammaContourCarrier f
            ((t : ℂ) * Complex.I)) =
      0 :=
  let lowerLeft : ℂ := Complex.mk 0 (-T)
  let upperRight : ℂ :=
    Complex.mk (family.c - (1 / 2 : ℝ)) T
  let rawBottom : ℂ :=
    ∫ x : ℝ in lowerLeft.re..upperRight.re,
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + (lowerLeft.im : ℂ) * Complex.I)
  let rawTop : ℂ :=
    ∫ x : ℝ in lowerLeft.re..upperRight.re,
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + (upperRight.im : ℂ) * Complex.I)
  let rawRight : ℂ :=
    ∫ t : ℝ in lowerLeft.im..upperRight.im,
      zetaCompletedRegularInverseGammaContourCarrier f
        ((upperRight.re : ℂ) + (t : ℂ) * Complex.I)
  let rawLeft : ℂ :=
    ∫ t : ℝ in lowerLeft.im..upperRight.im,
      zetaCompletedRegularInverseGammaContourCarrier f
        ((lowerLeft.re : ℂ) + (t : ℂ) * Complex.I)
  let bottom : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  let top : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + (T : ℂ) * Complex.I)
  let right : ℂ :=
    ∫ t : ℝ in (-T)..T,
      zetaCompletedRegularInverseGammaContourCarrier f
        (((family.c : ℂ) - (1 / 2 : ℂ)) +
          (t : ℂ) * Complex.I)
  let left : ℂ :=
    ∫ t : ℝ in (-T)..T,
      zetaCompletedRegularInverseGammaContourCarrier f
        ((t : ℂ) * Complex.I)
  let differentiableRectangle :
      DifferentiableOn ℂ
        (zetaCompletedRegularInverseGammaContourCarrier f)
        (Set.uIcc lowerLeft.re upperRight.re ×ℂ
          Set.uIcc lowerLeft.im upperRight.im) :=
    zetaCompletedRegularInverseGammaContourCarrier_differentiableOn_rectangle
      f hPhi family T
  let rawBoundary :
      rawBottom - rawTop + Complex.I • rawRight - Complex.I • rawLeft = 0 :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (zetaCompletedRegularInverseGammaContourCarrier f)
      lowerLeft upperRight differentiableRectangle
  let lowerLeftRe : lowerLeft.re = 0 := rfl
  let lowerLeftIm : lowerLeft.im = -T := rfl
  let upperRightRe : upperRight.re = family.c - (1 / 2 : ℝ) := rfl
  let upperRightIm : upperRight.im = T := rfl
  let upperRightReComplex :
      (upperRight.re : ℂ) = (family.c : ℂ) - (1 / 2 : ℂ) :=
    let halfAsComplex : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) :=
      Complex.ofReal_div (1 : ℝ) (2 : ℝ)
    Eq.trans
      (congrArg (fun value : ℝ => (value : ℂ)) upperRightRe)
      (Eq.trans
        (Complex.ofReal_sub family.c (1 / 2 : ℝ))
        (congrArg
          (fun value : ℂ => (family.c : ℂ) - value)
          halfAsComplex))
  let bottomEquality : rawBottom = bottom :=
    congrArg
      (fun edge : ℝ → ℂ => ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)), edge x)
      (funext
        (fun x : ℝ =>
          congrArg
            (zetaCompletedRegularInverseGammaContourCarrier f)
            (congrArg₂ HAdd.hAdd
              rfl
              (congrArg
                (fun value : ℂ => value * Complex.I)
                (congrArg (fun value : ℝ => (value : ℂ)) lowerLeftIm)))))
  let topEquality : rawTop = top :=
    congrArg
      (fun edge : ℝ → ℂ => ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)), edge x)
      (funext
        (fun x : ℝ =>
          congrArg
            (zetaCompletedRegularInverseGammaContourCarrier f)
            (congrArg₂ HAdd.hAdd
              rfl
              (congrArg
                (fun value : ℂ => value * Complex.I)
                (congrArg (fun value : ℝ => (value : ℂ)) upperRightIm)))))
  let rightEquality : rawRight = right :=
    congrArg
      (fun edge : ℝ → ℂ => ∫ t : ℝ in (-T)..T, edge t)
      (funext
        (fun t : ℝ =>
          congrArg
            (zetaCompletedRegularInverseGammaContourCarrier f)
            (congrArg₂ HAdd.hAdd upperRightReComplex rfl)))
  let leftEquality : rawLeft = left :=
    congrArg
      (fun edge : ℝ → ℂ => ∫ t : ℝ in (-T)..T, edge t)
      (funext
        (fun t : ℝ =>
          congrArg
            (zetaCompletedRegularInverseGammaContourCarrier f)
            (Eq.trans
              (congrArg₂ HAdd.hAdd
                (congrArg (fun value : ℝ => (value : ℂ)) lowerLeftRe)
                rfl)
              (zero_add ((t : ℂ) * Complex.I)))))
  let boundaryNormalization :
      bottom - top + Complex.I • right - Complex.I • left =
        rawBottom - rawTop + Complex.I • rawRight - Complex.I • rawLeft :=
    congrArg₂ HSub.hSub
      (congrArg₂ HAdd.hAdd
        (congrArg₂ HSub.hSub bottomEquality.symm topEquality.symm)
        (congrArg (fun value : ℂ => Complex.I • value) rightEquality.symm))
      (congrArg (fun value : ℂ => Complex.I • value) leftEquality.symm)
  Eq.trans boundaryNormalization rawBoundary

/-- The standard tangent-oriented rectangle equation solves for the ordinary
right vertical integral. -/
theorem regularInverseGamma_right_eq_left_add_horizontal_of_boundary_eq_zero
    (bottom top right left : ℂ)
    (boundaryEquality :
      bottom - top + Complex.I • right - Complex.I • left = 0) :
    right =
      left + (-Complex.I) • (top - bottom) :=
  let tangentAddEquality :
      (bottom - top) + Complex.I • right =
        Complex.I • left :=
    sub_eq_zero.mp boundaryEquality
  let rightTangentEquality :
      Complex.I • right =
        Complex.I • left - (bottom - top) :=
    eq_sub_of_add_eq' tangentAddEquality
  let horizontalNegation :
      -(bottom - top) = top - bottom :=
    neg_sub bottom top
  let rightTangentRegroup :
      Complex.I • right =
        Complex.I • left + (top - bottom) :=
    Eq.trans rightTangentEquality
      (Eq.trans
        (sub_eq_add_neg (Complex.I • left) (bottom - top))
        (congrArg
          (fun value : ℂ => Complex.I • left + value)
          horizontalNegation))
  let inverseCoefficient :
      (-Complex.I) * Complex.I = (1 : ℂ) :=
    Eq.trans
      (neg_mul Complex.I Complex.I)
      (Eq.trans
        (congrArg Neg.neg Complex.I_mul_I)
        (neg_neg (1 : ℂ)))
  let rotatedEquality :
      (-Complex.I) • (Complex.I • right) =
        (-Complex.I) •
          (Complex.I • left + (top - bottom)) :=
    congrArg (fun value : ℂ => (-Complex.I) • value)
      rightTangentRegroup
  let rotatedRight :
      (-Complex.I) • (Complex.I • right) = right :=
    Eq.trans
      (smul_smul (-Complex.I) Complex.I right)
      (Eq.trans
        (congrArg (fun coefficient : ℂ => coefficient • right)
          inverseCoefficient)
        (one_smul ℂ right))
  let rotatedLeft :
      (-Complex.I) • (Complex.I • left) = left :=
    Eq.trans
      (smul_smul (-Complex.I) Complex.I left)
      (Eq.trans
        (congrArg (fun coefficient : ℂ => coefficient • left)
          inverseCoefficient)
        (one_smul ℂ left))
  let rotatedSum :
      (-Complex.I) •
          (Complex.I • left + (top - bottom)) =
        left + (-Complex.I) • (top - bottom) :=
    Eq.trans
      (smul_add (-Complex.I) (Complex.I • left) (top - bottom))
      (congrArg
        (fun value : ℂ =>
          value + (-Complex.I) • (top - bottom))
        rotatedLeft)
  Eq.trans rotatedRight.symm
    (Eq.trans rotatedEquality rotatedSum)

/-- The affine set window is the right-edge interval integral of the regular
carrier. -/
theorem zetaCompletedAffineInverseGammaRightWindow_eq_carrierInterval
    (f : ZetaAdmissibleFunction)
    (T : ℝ)
    (heightNonnegative : 0 ≤ T) :
    zetaCompletedAffineInverseGammaRightWindow f T =
      ∫ t : ℝ in (-T)..T,
        zetaCompletedRegularInverseGammaContourCarrier f
          ((((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c : ℂ) -
              (1 / 2 : ℂ)) +
            (t : ℂ) * Complex.I) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let carrierEdge : ℝ → ℂ := fun t : ℝ =>
    zetaCompletedRegularInverseGammaContourCarrier f
      (((family.c : ℂ) - (1 / 2 : ℂ)) +
        (t : ℂ) * Complex.I)
  let ordered : -T ≤ T :=
    regularInverseGamma_neg_le_self T heightNonnegative
  let setToInterval :
      (∫ t in Set.Icc (-T) T, rightKernel t) =
        ∫ t : ℝ in (-T)..T, rightKernel t :=
    regularInverseGamma_setIntegral_Icc_eq_intervalIntegral
      rightKernel (-T) T ordered
  let edgeFunctionEquality : carrierEdge = rightKernel :=
    funext
      (fun t : ℝ =>
        zetaCompletedRegularInverseGammaContourCarrier_rightEdge
          f family t)
  let intervalTransport :
      (∫ t : ℝ in (-T)..T, rightKernel t) =
        ∫ t : ℝ in (-T)..T, carrierEdge t :=
    congrArg
      (fun integrand : ℝ → ℂ =>
        ∫ t : ℝ in (-T)..T, integrand t)
      edgeFunctionEquality.symm
  Eq.trans setToInterval intervalTransport

/-- The critical set window is the left-edge interval integral of the regular
carrier. -/
theorem zetaCompletedCriticalInverseGammaWindow_eq_carrierInterval
    (f : ZetaAdmissibleFunction)
    (T : ℝ)
    (heightNonnegative : 0 ≤ T) :
    zetaCompletedCriticalInverseGammaWindow f T =
      ∫ t : ℝ in (-T)..T,
        zetaCompletedRegularInverseGammaContourCarrier f
          ((t : ℂ) * Complex.I) :=
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let carrierEdge : ℝ → ℂ := fun t : ℝ =>
    zetaCompletedRegularInverseGammaContourCarrier f
      ((t : ℂ) * Complex.I)
  let ordered : -T ≤ T :=
    regularInverseGamma_neg_le_self T heightNonnegative
  let setToInterval :
      (∫ t in Set.Icc (-T) T, criticalKernel t) =
        ∫ t : ℝ in (-T)..T, criticalKernel t :=
    regularInverseGamma_setIntegral_Icc_eq_intervalIntegral
      criticalKernel (-T) T ordered
  let edgeFunctionEquality : carrierEdge = criticalKernel :=
    funext
      (fun t : ℝ =>
        zetaCompletedRegularInverseGammaContourCarrier_criticalEdge
          f t)
  let intervalTransport :
      (∫ t : ℝ in (-T)..T, criticalKernel t) =
        ∫ t : ℝ in (-T)..T, carrierEdge t :=
    congrArg
      (fun integrand : ℝ → ℂ =>
        ∫ t : ℝ in (-T)..T, integrand t)
      edgeFunctionEquality.symm
  Eq.trans setToInterval intervalTransport

/-- The named horizontal defect is the tangent-rotated difference of the top
and bottom interval integrals. -/
theorem zetaCompletedRegularInverseGammaHorizontalDefect_eq_carrierIntervals
    (f : ZetaAdmissibleFunction)
    (T : ℝ) :
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    zetaCompletedRegularInverseGammaHorizontalDefect f T =
      (-Complex.I) •
        ((∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
            zetaCompletedRegularInverseGammaContourCarrier f
              ((x : ℂ) + (T : ℂ) * Complex.I)) -
          ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
            zetaCompletedRegularInverseGammaContourCarrier f
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let width : ℝ := family.c - (1 / 2 : ℝ)
  let topEdge : ℝ → ℂ := fun x : ℝ =>
    zetaCompletedRegularInverseGammaContourCarrier f
      ((x : ℂ) + (T : ℂ) * Complex.I)
  let bottomEdge : ℝ → ℂ := fun x : ℝ =>
    zetaCompletedRegularInverseGammaContourCarrier f
      ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  let widthOrdered : 0 ≤ width :=
    le_of_lt (regularInverseGamma_centeredWidth_positive family)
  let topConversion :
      (∫ x in Set.Icc (0 : ℝ) width, topEdge x) =
        ∫ x : ℝ in (0 : ℝ)..width, topEdge x :=
    regularInverseGamma_setIntegral_Icc_eq_intervalIntegral
      topEdge 0 width widthOrdered
  let bottomConversion :
      (∫ x in Set.Icc (0 : ℝ) width, bottomEdge x) =
        ∫ x : ℝ in (0 : ℝ)..width, bottomEdge x :=
    regularInverseGamma_setIntegral_Icc_eq_intervalIntegral
      bottomEdge 0 width widthOrdered
  let differenceConversion :
      (∫ x in Set.Icc (0 : ℝ) width, topEdge x) -
          (∫ x in Set.Icc (0 : ℝ) width, bottomEdge x) =
        (∫ x : ℝ in (0 : ℝ)..width, topEdge x) -
          ∫ x : ℝ in (0 : ℝ)..width, bottomEdge x :=
    congrArg₂ HSub.hSub topConversion bottomConversion
  Eq.trans
    (congrArg
      (fun value : ℂ => (-Complex.I) * value)
      differenceConversion)
    (Algebra.id.smul_eq_mul
      (-Complex.I)
      ((∫ x : ℝ in (0 : ℝ)..width, topEdge x) -
        ∫ x : ℝ in (0 : ℝ)..width, bottomEdge x)).symm

/-- Cauchy-Goursat on the finite regular strip rectangle expresses the affine
window as the critical window plus its two horizontal edges. -/
theorem zetaCompletedRegularInverseGamma_finiteWindow_eq_critical_add_horizontal
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (T : ℝ)
    (heightNonnegative : 0 ≤ T) :
    zetaCompletedAffineInverseGammaRightWindow f T =
      zetaCompletedCriticalInverseGammaWindow f T +
        zetaCompletedRegularInverseGammaHorizontalDefect f T :=
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let bottom : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
  let top : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..(family.c - (1 / 2 : ℝ)),
      zetaCompletedRegularInverseGammaContourCarrier f
        ((x : ℂ) + (T : ℂ) * Complex.I)
  let right : ℂ :=
    ∫ t : ℝ in (-T)..T,
      zetaCompletedRegularInverseGammaContourCarrier f
        (((family.c : ℂ) - (1 / 2 : ℂ)) +
          (t : ℂ) * Complex.I)
  let left : ℂ :=
    ∫ t : ℝ in (-T)..T,
      zetaCompletedRegularInverseGammaContourCarrier f
        ((t : ℂ) * Complex.I)
  let boundaryEquality :
      bottom - top + Complex.I • right - Complex.I • left = 0 :=
    zetaCompletedRegularInverseGamma_rectangleBoundary_eq_zero
      f hPhi family T
  let solvedBoundary :
      right = left + (-Complex.I) • (top - bottom) :=
    regularInverseGamma_right_eq_left_add_horizontal_of_boundary_eq_zero
      bottom top right left boundaryEquality
  let rightWindow :
      zetaCompletedAffineInverseGammaRightWindow f T = right :=
    zetaCompletedAffineInverseGammaRightWindow_eq_carrierInterval
      f T heightNonnegative
  let criticalWindow :
      zetaCompletedCriticalInverseGammaWindow f T = left :=
    zetaCompletedCriticalInverseGammaWindow_eq_carrierInterval
      f T heightNonnegative
  let horizontalDefect :
      zetaCompletedRegularInverseGammaHorizontalDefect f T =
        (-Complex.I) • (top - bottom) :=
    zetaCompletedRegularInverseGammaHorizontalDefect_eq_carrierIntervals
      f T
  Eq.trans rightWindow
    (Eq.trans solvedBoundary
      (congrArg₂ HAdd.hAdd
        criticalWindow.symm horizontalDefect.symm))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
