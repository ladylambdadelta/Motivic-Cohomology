import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport

/-!
# Boundary explicit-formula residue scalar

This file owns the residue-shaped scalar name used by the contour-shift
assembly. The comparison with the analytic boundary scalar is proved in the
final contour-shift target by uniqueness of the residue-side and vertical-side
limits.
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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
