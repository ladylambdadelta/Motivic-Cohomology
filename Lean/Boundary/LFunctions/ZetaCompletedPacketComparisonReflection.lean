import Boundary.LFunctions.ZetaCompletedPacketComparisonCore

/-!
# Boundary completed packet comparison reflection helpers

This file isolates the reflected-autocorrelation helper lemmas. It keeps the
reflection bookkeeping separate from the core comparison chain.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper: reflected autocorrelation has the same boundary-defect Gram. -/
theorem zetaCompletedBoundaryDefectGram_autocorrelation_reflect_helper
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  rfl

/-- Helper: reflected autocorrelation has the same packet norm square. -/
theorem zetaCompletedPacketNormSq_autocorrelation_reflect_helper
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedPacketNormSq_autocorrelation_reflect f

/-- Helper: reflected autocorrelation Weil form equals the packet norm square. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_helper
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_classFree f

/-- Helper: reflected autocorrelation Weil form is nonnegative. -/
theorem zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_helper
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  exact zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_classFree f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
