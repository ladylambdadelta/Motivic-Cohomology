import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.ZetaCompletedPacketComparison.ZetaCompletedPacketComparisonCore.ZetaCompletedPacketComparisonCore

/-!
# Boundary completed packet comparison reflection helpers

This file isolates the reflected-autocorrelation helper lemmas. It keeps the
reflection bookkeeping separate from the core comparison chain.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper target: reflected autocorrelation has the same boundary-defect Gram. -/
def zetaCompletedBoundaryDefectGram_autocorrelation_reflect_helper
    (f : ZetaAdmissibleFunction) :
    Prop :=
    zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f)

/-- Helper target: reflected autocorrelation has the same packet norm square. -/
def zetaCompletedPacketNormSq_autocorrelation_reflect_helper
    (f : ZetaAdmissibleFunction) :
    Prop :=
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) 0 =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) 0

/-- Helper target: reflected autocorrelation Weil form equals the packet norm square. -/
def zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq_helper
    (f : ZetaAdmissibleFunction) :
    Prop :=
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) 0

/-- Helper target: reflected autocorrelation Weil form is nonnegative. -/
def zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_helper
    (f : ZetaAdmissibleFunction) :
    Prop :=
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
