import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaZeroKreinGram

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

/-- Replacing the analytic boundary sum by zero sends the contour-shift target to zero. -/
theorem contourShiftTarget_to_zero
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (h : explicitFormulaContourShiftTarget f r) :
    zetaCompletedZeroKreinGram f = 0 :=
  h.trans (zetaCompletedExplicitFormulaBoundarySumAnalytic_zero f)

/-- Replacing zero by the analytic boundary sum rebuilds the contour-shift target. -/
theorem contourShiftTarget_of_zero
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (h : zetaCompletedZeroKreinGram f = 0) :
    explicitFormulaContourShiftTarget f r :=
  h.trans (zetaCompletedExplicitFormulaBoundarySumAnalytic_zero f).symm

/-- The final contour-shift target is equivalent to zero in the current normalization. -/
theorem explicitFormulaContourShiftTarget_iff_zero
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget f r ↔
      zetaCompletedZeroKreinGram f = 0 :=
  Iff.intro
    (contourShiftTarget_to_zero f r)
    (contourShiftTarget_of_zero f r)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
