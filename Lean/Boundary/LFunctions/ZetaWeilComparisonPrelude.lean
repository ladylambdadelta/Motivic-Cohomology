import Boundary.LFunctions.WeilCriterion

/-!
# Boundary zeta Weil comparison prelude

This file packages the definitional equalities around the completed Weil form
so later comparison theorems can work from a narrow owner surface. It does not
attempt the missing analytic bridge to the boundary-defect Gram.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaProbe

/-- The completed Weil form is the completed spectral Weil form. -/
theorem zetaWeilFormCompleted_eq_completedSpectralWeilForm
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedSpectralWeilForm φ := by
  rfl

/-- The completed spectral Weil form is the completed zero-side sum. -/
theorem zetaCompletedSpectralWeilForm_eq_zeroSide
    (φ : ZetaProbe) :
    zetaCompletedSpectralWeilForm φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed Weil form is definitionally the completed zero-side sum. -/
theorem zetaWeilFormCompleted_eq_zeroSide
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedZeroSideRe φ := by
  rw [zetaWeilFormCompleted_def, zetaCompletedSpectralWeilForm_def]

end ZetaProbe

end
end LFunctions
end Boundary
