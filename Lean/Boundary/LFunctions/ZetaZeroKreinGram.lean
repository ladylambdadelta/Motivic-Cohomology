import Boundary.LFunctions.WeilCriterion

/-!
# Boundary zeta zero Krein form

This file owns the zero-side Krein form used as the first analytic target in
the completed explicit-formula chain. It lives on the probe carrier and is
definitionally the completed zero-side real form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zero-side Krein form attached to a probe. -/
noncomputable def zetaCompletedZeroKreinGram (φ : ZetaProbe) : ℝ :=
  zetaCompletedZeroSideRe φ

/-- The completed Weil form is the zero-side Krein form. -/
theorem zetaWeilFormCompleted_eq_zeroKreinGram (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedZeroKreinGram φ := by
  rfl

/-- The zero-side Krein form is definitionally the completed zero-side form. -/
theorem zetaCompletedZeroKreinGram_eq_zeroSide
    (φ : ZetaProbe) :
    zetaCompletedZeroKreinGram φ = zetaCompletedZeroSideRe φ := by
  rfl

end
end LFunctions
end Boundary
