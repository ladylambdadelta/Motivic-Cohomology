import Mathlib.Data.Real.Basic

/-!
# Boundary explicit-formula rectangle API

This file owns the rectangle type used by the explicit-formula contour
construction. It is intentionally minimal: the geometric and analytic layers
import it, but it imports nothing from them.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The closed rectangle used in the contour argument. -/
structure ExplicitFormulaRectangle where
  c : ℝ
  T : ℝ

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
