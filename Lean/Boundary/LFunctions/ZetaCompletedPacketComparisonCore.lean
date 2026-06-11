import Boundary.LFunctions.ZetaExplicitFormulaBoundaryTransport

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

/-- Helper: completed Weil form of an autocorrelation is the packet norm square. -/
theorem zetaWeilFormCompleted_eq_packetNormSq_helper
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) =
      zetaCompletedPacketNormSq f := by
  exact zetaWeilFormCompleted_eq_packetNormSq_classFree f

/-- Helper: the zero-side Krein form is the packet norm square. -/
theorem zetaCompletedZeroKreinGram_eq_completedPacketNormSq_helper
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f = zetaCompletedPacketNormSq f := by
  exact zetaCompletedZeroKreinGram_eq_completedPacketNormSq_classFree f

/-- Helper: completed Weil form of an autocorrelation is nonnegative. -/
theorem zetaWeilFormCompleted_autocorrelation_nonnegative_helper
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaWeilFormCompleted_autocorrelation_nonnegative_classFree f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
