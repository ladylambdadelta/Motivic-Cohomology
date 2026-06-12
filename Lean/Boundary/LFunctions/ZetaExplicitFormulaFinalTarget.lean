import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaExplicitFormulaResidueBridge

/-!
# Boundary explicit-formula final target

This file owns the final zero-side contour-shift target. The pure contour
geometry file intentionally does not import the zero-side Krein form, because
the zero-side chain already depends downstream on the complex-analysis contour
layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The full contour-shift target for the explicit formula. -/
def explicitFormulaContourShiftTarget
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedZeroKreinGram f =
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The contour-shift target is the final public explicit-formula statement. -/
theorem explicitFormulaContourShiftTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
  Iff.rfl

/-- The zero-side Krein sum is the completed residue boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_completedResidueBoundarySum
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    (zetaCompletedZeroKreinGram f : ℂ) =
      (zetaCompletedResidueBoundarySum f : ℂ) := by
  exact congrArg (fun x : ℝ => (x : ℂ))
    (zetaCompletedZeroKreinGram_eq_residueBoundarySum f)

/-- After horizontal decay, the completed residue boundary sum is the limiting vertical side
difference. -/
theorem completedResidueBoundarySum_eq_verticalDifference_of_horizontalDecay
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    (zetaCompletedResidueBoundarySum f : ℂ) =
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r := by
  sorry

/-- The zero side is the limiting vertical-difference side of the completed contour shift.

This is the residue/horizontal-decay cut: its proof must combine the completed
log-derivative residue theorem with vanishing of the horizontal sides, then identify the
resulting zero sum with `zetaCompletedZeroKreinGram`. -/
theorem zetaCompletedZeroKreinGram_eq_verticalDifference_of_residue_horizontalDecay
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r := by
  exact
    (zetaCompletedZeroKreinGram_eq_completedResidueBoundarySum f r).trans
      (completedResidueBoundarySum_eq_verticalDifference_of_horizontalDecay f r)

/-- The vertical side difference of the completed contour. -/
noncomputable def explicitFormulaVerticalDifference
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r -
    zetaCompletedExplicitFormulaLeftLineIntegral f r

/-- The prime channel of the vertical decomposition. -/
noncomputable def explicitFormulaVerticalPrimeContribution
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f

/-- The archimedean channel of the vertical decomposition. -/
noncomputable def explicitFormulaVerticalArchimedeanContribution
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanContribution f

/-- The correction channel of the vertical decomposition. -/
noncomputable def explicitFormulaVerticalCorrectionContribution
    (f : ZetaAdmissibleFunction) (_r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionContribution f

/-- The vertical side difference decomposes into prime, archimedean, and correction channels. -/
theorem explicitFormulaVerticalDifference_decomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalDifference f r =
      explicitFormulaVerticalPrimeContribution f r +
        explicitFormulaVerticalArchimedeanContribution f r +
        explicitFormulaVerticalCorrectionContribution f r := by
  sorry

/-- The prime part of the vertical contour difference is the prime explicit-formula boundary
contribution. -/
theorem explicitFormulaVerticalPrimeDecomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalPrimeContribution f r =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  rfl

/-- The archimedean part of the vertical contour difference is the archimedean explicit-formula
boundary contribution. -/
theorem explicitFormulaVerticalArchimedeanDecomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalArchimedeanContribution f r =
      zetaCompletedExplicitFormulaArchimedeanContribution f := by
  rfl

/-- The correction part of the vertical contour difference is the pole-correction
explicit-formula boundary contribution. -/
theorem explicitFormulaVerticalCorrectionDecomposition
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalCorrectionContribution f r =
      zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

/-- The vertical side difference assembles from the prime, archimedean, and correction channel
decompositions. -/
theorem explicitFormulaVerticalDifference_eq_boundarySum_of_components
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (_hprime :
      explicitFormulaVerticalPrimeContribution f r =
        zetaCompletedExplicitFormulaPrimeContribution f)
    (_harch :
      explicitFormulaVerticalArchimedeanContribution f r =
        zetaCompletedExplicitFormulaArchimedeanContribution f)
    (_hcorrection :
      explicitFormulaVerticalCorrectionContribution f r =
        zetaCompletedExplicitFormulaCorrectionContribution f) :
    zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  have hvertical :
      explicitFormulaVerticalDifference f r =
        explicitFormulaVerticalPrimeContribution f r +
          explicitFormulaVerticalArchimedeanContribution f r +
          explicitFormulaVerticalCorrectionContribution f r :=
    explicitFormulaVerticalDifference_decomposition f r
  calc
    zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r =
        explicitFormulaVerticalDifference f r := by
      rfl
    _ =
        explicitFormulaVerticalPrimeContribution f r +
          explicitFormulaVerticalArchimedeanContribution f r +
          explicitFormulaVerticalCorrectionContribution f r := hvertical
    _ =
        zetaCompletedExplicitFormulaPrimeContribution f +
          zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionContribution f := by
      exact congrArg₂ (fun a b : ℂ => a + b)
        (congrArg₂ (fun a b : ℂ => a + b) _hprime _harch)
        _hcorrection
    _ = zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
      (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq f).symm

/-- The vertical side difference is the analytic explicit-formula boundary sum.

This is the vertical-decomposition cut: its proof must unfold the completed logarithmic
derivative into prime, archimedean, and pole-correction pieces and identify the resulting
line-integral decomposition with `zetaCompletedExplicitFormulaBoundarySumAnalytic`. -/
theorem explicitFormulaVerticalDecompositionTarget_of_rectangle
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalDecompositionTarget f r := by
  exact explicitFormulaVerticalDifference_eq_boundarySum_of_components f r
    (explicitFormulaVerticalPrimeDecomposition f r)
    (explicitFormulaVerticalArchimedeanDecomposition f r)
    (explicitFormulaVerticalCorrectionDecomposition f r)

/-- The contour-shift target follows from the zero/vertical identification and the vertical
decomposition. -/
theorem explicitFormulaContourShiftTarget_of_verticalDifference
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (hzero :
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaRightLineIntegral f r -
          zetaCompletedExplicitFormulaLeftLineIntegral f r)
    (hvertical : explicitFormulaVerticalDecompositionTarget f r) :
    explicitFormulaContourShiftTarget f r := by
  have hv :
      zetaCompletedExplicitFormulaRightLineIntegral f r -
          zetaCompletedExplicitFormulaLeftLineIntegral f r =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
    (explicitFormulaVerticalDecompositionTarget_iff f r).mp hvertical
  exact hzero.trans hv

/-- The completed contour-shift theorem in the repository's analytic normalization.

This is the owner target for the contour argument. Its proof must assemble the completed
log-derivative residue theorem, horizontal decay, and vertical decomposition to identify the
zero-side Krein sum with the analytic explicit-formula boundary sum. -/
theorem explicitFormulaContourShiftTarget_of_rectangle
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r := by
  exact explicitFormulaContourShiftTarget_of_verticalDifference f r
    (zetaCompletedZeroKreinGram_eq_verticalDifference_of_residue_horizontalDecay f r)
    (explicitFormulaVerticalDecompositionTarget_of_rectangle f r)

/-- A complex zero statement for the real zero-side Krein form descends to a real zero statement. -/
theorem zetaCompletedZeroKreinGram_eq_zero_of_complex_zero
    (f : ZetaAdmissibleFunction)
    (h : (zetaCompletedZeroKreinGram f : ℂ) = 0) :
    zetaCompletedZeroKreinGram f = 0 :=
  Complex.ofReal_injective h

/-- A real zero statement for the zero-side Krein form ascends to a complex zero statement. -/
theorem zetaCompletedZeroKreinGram_complex_zero_of_eq_zero
    (f : ZetaAdmissibleFunction)
    (h : zetaCompletedZeroKreinGram f = 0) :
    (zetaCompletedZeroKreinGram f : ℂ) = 0 :=
  congrArg (fun x : ℝ => (x : ℂ)) h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
