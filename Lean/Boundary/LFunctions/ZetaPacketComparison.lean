import Boundary.LFunctions.ZetaCompletedBoundaryDefect

/-!
# Boundary zeta packet comparison

This file compares the packet reconstruction norm square with the completed
boundary-defect Gram form. It does not attempt the final Weil-form bridge; it
only isolates the owner-level packet identity already present in the
reconstruction layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed packet norm square is the completed boundary-defect Gram norm. -/
theorem zetaCompletedPacketNormSq_eq_boundaryDefectGram (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq f = zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The completed boundary-defect Gram norm is the completed packet norm square. -/
theorem zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f := by
  rfl

/-- The completed packet norm square is nonnegative via the boundary-defect Gram. -/
theorem zetaCompletedPacketNormSq_nonnegative_of_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPacketNormSq f := by
  exact zetaCompletedBoundaryDefectGram_nonnegative f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
