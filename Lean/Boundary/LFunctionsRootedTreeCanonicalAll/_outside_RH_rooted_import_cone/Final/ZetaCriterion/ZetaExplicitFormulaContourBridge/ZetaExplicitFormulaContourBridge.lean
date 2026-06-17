import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.ZetaCompletedExplicitFormulaAssembly.ZetaCompletedExplicitFormulaAssembly
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.ExplicitFormula.ZetaCompletedExplicitFormulaAssembly.ZetaExplicitFormulaBoundaryTransport.ZetaExplicitFormulaBoundaryTransport
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.Final.ZetaCriterion.ZetaExplicitFormulaContourBridge.ZetaExplicitFormulaFinalTarget.ZetaExplicitFormulaFinalTarget
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaNormalizationBridge.ZetaExplicitFormulaNormalizationBridge

/-!
# Boundary explicit-formula contour bridge

This file is the owner-level wrapper for the completed contour-shift theorem
in the current repository normalization. The analytic content is carried by
the class-free transport theorem; this file keeps the exact final theorem
shape available in the contour namespace.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- If adding a debt scalar to a zero-side scalar gives the same target as the zero-side
scalar alone, then the debt scalar is zero. -/
theorem real_debt_eq_zero_of_add_eq_of_left_eq
    {Z D H : ℝ} (hadd : Z + D = H) (hleft : Z = H) :
    D = 0 := by
  have hZD : Z + D = Z := hadd.trans hleft.symm
  calc
    D = Z + D - Z := by
      exact (add_sub_cancel_left Z D).symm
    _ = Z - Z := by
      exact congrArg (fun x : ℝ => x - Z) hZD
    _ = 0 := by
      exact sub_self Z

/-- If the debt scalar is zero, a debt-corrected equality descends to the raw zero-side
scalar. -/
theorem real_left_eq_of_add_eq_of_debt_eq_zero
    {Z D H : ℝ} (hadd : Z + D = H) (hdebt : D = 0) :
    Z = H := by
  calc
    Z = Z + 0 := by
      exact (add_zero Z).symm
    _ = Z + D := by
      exact congrArg (fun x : ℝ => Z + x) hdebt.symm
    _ = H := hadd

/-- The completed explicit-formula target actually used by the quadratic/autocorrelation
positivity lane. -/
def zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f

/-- The autocorrelation target unfolds to the seed-Krein boundary equality. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget_iff
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget f ↔
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  rfl

/-- The completed explicit-formula contour bridge for convolution-autocorrelation probes, using
the holographic boundary normalization. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hshift : explicitFormulaContourShiftTarget g ⟨1, 1⟩ :=
    explicitFormulaContourShiftTarget_of_rectangle g ⟨1, 1⟩
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) :=
    zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum f
  exact
    zetaCompletedZeroKreinGram_eq_realBoundary_of_contourShiftTarget
      g ⟨1, 1⟩
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)
      hshift
      hboundary

/-- The completed explicit-formula contour bridge after descent to the completed
ordered-heart scalar.  This is the true payoff theorem for the GNS-positive route: the
contour-side zero sum lands directly in the ordered-heart quotient scalar, not in the raw
time-side representative. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
        f := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hshift : explicitFormulaContourShiftTarget g ⟨1, 1⟩ :=
    explicitFormulaContourShiftTarget_of_rectangle g ⟨1, 1⟩
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic g +
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) := by
    exact
      zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_orderedHeartScalar
        f
  have hcomplex :
      zetaCompletedResidueBoundarySumComplex g +
          (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) := by
    exact Eq.trans
      (congrArg
        (fun z : ℂ =>
          z + (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ))
        hshift)
      hboundary
  have hre :
      Complex.re
          (zetaCompletedResidueBoundarySumComplex g +
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)) =
        Complex.re
          (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) :=
    congrArg Complex.re hcomplex
  calc
    zetaCompletedZeroKreinGram
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        Complex.re (zetaCompletedResidueBoundarySumComplex g) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
      rfl
    _ =
        Complex.re
          (zetaCompletedResidueBoundarySumComplex g +
            (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)) := by
      exact (Complex.add_re
        (zetaCompletedResidueBoundarySumComplex g)
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) : ℂ)).symm
    _ =
        Complex.re
          (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f : ℂ) :=
      hre
    _ =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f :=
      Complex.ofReal_re
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f)

/-- The zero-side ordered-heart realization class for an autocorrelation seed.

The contour side must land in this quotient class, not in a raw real scalar obtained by
deleting the diagonal-debt term. -/
def zetaCompletedZeroSideAutocorrelationOrderedHeartClass
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryOrderedHeartClass :=
  completedFinitePartBoundaryOrderedHeartQuotientClass f

/-- The scalar of the zero-side ordered-heart realization is the finite-part quotient scalar. -/
theorem zetaCompletedZeroSideAutocorrelationOrderedHeartClass_scalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (zetaCompletedZeroSideAutocorrelationOrderedHeartClass f) =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
  rfl

/-- The quotient-normalized zero-side scalar for an autocorrelation seed.

This is the zero-side scalar that actually lands in the completed ordered heart: the raw
zero-side Krein scalar together with the diagonal-debt coordinate required by the
weight-triangular realization. -/
noncomputable def zetaCompletedZeroSideAutocorrelationOrderedHeartScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)

/-- The zero-side ordered-heart scalar is the raw zero-side Krein scalar plus the real
prime diagonal-debt coordinate. -/
theorem zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_zeroKrein_add_debt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
  rfl

/-- The quotient-normalized zero-side scalar is the scalar of the zero-side ordered-heart
realization class. -/
theorem zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_classScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
      completedBoundaryOrderedHeartClassScalar
        (zetaCompletedZeroSideAutocorrelationOrderedHeartClass f) := by
  have hbridge :
      zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
    calc
      zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
          zetaCompletedZeroKreinGram
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
        exact zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_zeroKrein_add_debt f
      _ =
          zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
        exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart f
  exact hbridge.trans
    (zetaCompletedZeroSideAutocorrelationOrderedHeartClass_scalar f).symm

/-- The quotient-normalized zero-side scalar is the completed ordered-heart scalar. -/
theorem zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
  calc
    zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
        zetaCompletedZeroKreinGram
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
      exact zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_zeroKrein_add_debt f
    _ =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f := by
      exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart f

/-- The quotient-normalized zero-side scalar is nonnegative by ordered-heart positivity. -/
theorem zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f := by
  have hordered :
      0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar f :=
    zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar_nonnegative f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_orderedHeartScalar f).symm
    hordered

/-- If the zero-side contour realization descends to the ordered-heart scalar, then the
diagonal-debt scalar is zero in the zero-side realization. -/
theorem zetaCompletedPrimeDiagonalDebt_re_eq_zero_of_orderedHeart_descent
    (f : ZetaAdmissibleFunction)
    (hdescent :
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
          f) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    real_debt_eq_zero_of_add_eq_of_left_eq
      (zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart f)
      hdescent

/-- If the diagonal-debt scalar is zero in the zero-side realization, then the zero-side
contour realization descends to the completed ordered-heart scalar. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart_descent_of_primeDiagonalDebt_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (hdebt : Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
        f := by
  exact
    real_left_eq_of_add_eq_of_debt_eq_zero
      (zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart f)
      hdebt

/-- The raw scalar ordered-heart descent is equivalent to vanishing of the prime diagonal-debt
real scalar.

This is an obstruction theorem, not the intended final theorem: with the current raw
zero-side scalar normalization, descending directly to the ordered-heart scalar would force the
diagonal debt to vanish as a real number. -/
theorem zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart_descent_iff_primeDiagonalDebt_re_eq_zero
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
          f) ↔
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    ⟨zetaCompletedPrimeDiagonalDebt_re_eq_zero_of_orderedHeart_descent f,
      zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation_orderedHeart_descent_of_primeDiagonalDebt_re_eq_zero
        f⟩

/-- Historical debt-visible name for the ordered-heart autocorrelation contour bridge. -/
theorem zetaCompletedExplicitFormulaContourBridge_autocorrelation_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroSideAutocorrelationOrderedHeartScalar f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryOrderedHeartScalar
        f := by
  exact zetaCompletedZeroSideAutocorrelationOrderedHeartScalar_eq_orderedHeartScalar f

/-- Historical name for the convolution-autocorrelation contour bridge. -/
theorem zetaCompletedExplicitFormulaContourBridge_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f

/-- The completed contour bridge proves the named autocorrelation target. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget_of_contourBridge
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionAutocorrelationTarget f := by
  exact zetaCompletedExplicitFormulaContourBridge_convolutionAutocorrelation f

/-- A contour-shift target proves the completed explicit-formula contour bridge once the analytic
boundary sum has been normalized to the signed real boundary sum. -/
theorem zetaCompletedExplicitFormulaContourBridge_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift : explicitFormulaContourShiftTarget f r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        (zetaCompletedExplicitFormulaBoundarySum f : ℂ)) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f :=
  zetaCompletedZeroKreinGram_eq_realBoundary_of_contourShiftTarget
    f r
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f)
    hshift
    hboundary

/-- A proved contour bridge is exactly the completed explicit-formula target. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_of_contourBridge
    (f : ZetaAdmissibleFunction)
    (hbridge :
      zetaCompletedZeroKreinGram f =
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f :=
  hbridge

/-- The contour-shift theorem plus boundary normalization proves the completed explicit-formula
target. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift : explicitFormulaContourShiftTarget f r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic f =
        (zetaCompletedExplicitFormulaBoundarySum f : ℂ)) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f :=
  zetaCompletedExplicitFormulaAutocorrelationTarget_of_contourBridge f
    (zetaCompletedExplicitFormulaContourBridge_of_contourShiftTarget
      f r hshift hboundary)

/-- Convolution-autocorrelation specialization of the completed explicit-formula contour bridge
with the seed packet Krein normalization. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationSeedKrein_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift :
      explicitFormulaContourShiftTarget
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ)) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f :=
  zetaCompletedZeroKreinGram_eq_realBoundary_of_contourShiftTarget
    (ZetaAdmissibleFunction.convolutionAutocorrelation f) r
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)
    hshift
    hboundary

/-- Historical name for the convolution-autocorrelation contour-shift specialization. -/
theorem zetaCompletedExplicitFormulaAutocorrelationSeedKrein_of_contourShiftTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hshift :
      explicitFormulaContourShiftTarget
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) r)
    (hboundary :
      zetaCompletedExplicitFormulaBoundarySumAnalytic
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ)) :
    zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationSeedKrein_of_contourShiftTarget
    f r hshift hboundary

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
