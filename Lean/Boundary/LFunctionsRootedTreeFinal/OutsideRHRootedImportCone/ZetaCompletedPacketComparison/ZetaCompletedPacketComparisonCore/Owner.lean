import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.ExplicitFormula.ZetaCompletedExplicitFormulaAssembly.ZetaExplicitFormulaBoundaryTransport.Owner

/-!
# Boundary completed packet comparison core

This file packages the core comparison chain in a small helper API:

`zero Krein → explicit boundary sum → boundary-defect Gram → packet norm square`

The canonical public theorems still live in the transport layer; this file
provides named helper lemmas with a cleaner dependency surface for downstream
use.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper: the explicit-formula boundary sum is the centered packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_packetNormSq_helper
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedPacketNormSq f 0 := by
  exact zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f

/-- Helper: the boundary-defect Gram is the centered packet norm square. -/
theorem zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq_helper
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram f = zetaCompletedPacketNormSq f 0 := by
  exact zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- Helper: the explicit-formula boundary sum is nonnegative. -/
theorem zetaCompletedExplicitFormulaBoundarySum_nonnegative_helper
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaBoundarySum f := by
  exact zetaCompletedExplicitFormulaBoundarySum_nonnegative f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
