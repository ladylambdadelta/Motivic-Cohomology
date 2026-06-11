import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport

/-!
# Boundary explicit-formula residue bridge

This file owns the intermediate residue-shaped packaging between the zero-side
Krein form and the signed boundary transport form. It is intentionally narrow:
it records the ladder-shaped targets the explicit-formula argument needs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed residue boundary sum attached to an admissible probe. -/
noncomputable def zetaCompletedResidueBoundarySum (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedZeroKreinGram f

/-- The zero-side Krein form is the completed residue boundary sum. -/
theorem zetaCompletedZeroKreinGram_eq_residueBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      zetaCompletedResidueBoundarySum f := by
  rfl

/-- The remaining residue-to-boundary identity target. -/
def zetaCompletedResidueBoundarySum_eq_explicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) :
    Prop :=
    zetaCompletedResidueBoundarySum f =
      zetaCompletedExplicitFormulaBoundarySum f

/-- The residue-to-boundary target is the completed explicit-formula autocorrelation target. -/
theorem zetaCompletedResidueBoundarySum_eq_explicitFormulaBoundarySum_iff
    (f : ZetaAdmissibleFunction) :
    zetaCompletedResidueBoundarySum_eq_explicitFormulaBoundarySum f ↔
      zetaCompletedExplicitFormulaAutocorrelationTarget f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
