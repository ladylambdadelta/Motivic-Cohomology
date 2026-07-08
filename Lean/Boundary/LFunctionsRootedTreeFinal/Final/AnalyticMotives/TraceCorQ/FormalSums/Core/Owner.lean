import Mathlib.Data.List.Perm.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Core.Basic.Owner

/-!
# Core formal Q-linear trace correspondences

This file owns additive and scalar certificate-payload accounting for finite
formal sums before composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Formal-sum addition appends analytic certificate ledgers. -/
theorem TraceCorQFormalSum.add_certificateLedger
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.certificateLedger
        right.certificateLedger :=
  match left with
  | [] =>
      Eq.symm
        (ResidueChannelCertificateLedger.empty_append
          right.certificateLedger)
  | term :: tail =>
      Eq.trans
        (congrArg
          (fun certificateLedger =>
            ResidueChannelCertificateLedger.append
              term.certificateLedger
              certificateLedger)
          (TraceCorQFormalSum.add_certificateLedger tail right))
        (Eq.symm
          (ResidueChannelCertificateLedger.append_assoc
            term.certificateLedger
            (TraceCorQFormalSum.certificateLedger tail)
            right.certificateLedger))

/-- Formal-sum addition adds imported finite-rectangle payload. -/
theorem TraceCorQFormalSum.add_importedRectangleCount
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).importedRectangleCount =
      left.importedRectangleCount +
        right.importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      left.certificateLedger
      right.certificateLedger)

/-- Formal-sum addition concatenates imported finite-rectangle lists. -/
theorem TraceCorQFormalSum.add_importedRectangles
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).importedRectangles =
      left.importedRectangles ++
        right.importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceCorQFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_importedRectangles
      left.certificateLedger
      right.certificateLedger)

/-- Formal-sum addition adds internal trace-bookkeeping payload. -/
theorem TraceCorQFormalSum.add_traceBookkeepingCount
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).traceBookkeepingCount =
      left.traceBookkeepingCount +
        right.traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceCorQFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      left.certificateLedger
      right.certificateLedger)

/-- Formal-sum addition adds explicit rewrite-step payload. -/
theorem TraceCorQFormalSum.add_rewriteStepCount
    (left right : TraceCorQFormalSum) :
    (TraceCorQFormalSum.add left right).rewriteStepCount =
      left.rewriteStepCount +
        right.rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceCorQFormalSum.add_certificateLedger left right))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      left.certificateLedger
      right.certificateLedger)

/-- Scalar multiplication preserves the analytic certificate ledger of a formal sum. -/
theorem TraceCorQFormalSum.smul_certificateLedger
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).certificateLedger =
      formalSum.certificateLedger :=
  match formalSum with
  | [] => rfl
  | term :: tail =>
      congrArg
        (fun certificateLedger =>
            ResidueChannelCertificateLedger.append
              term.certificateLedger
              certificateLedger)
        (TraceCorQFormalSum.smul_certificateLedger coefficient tail)

/-- Scalar multiplication preserves imported finite-rectangle payload. -/
theorem TraceCorQFormalSum.smul_importedRectangleCount
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).importedRectangleCount =
      formalSum.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceCorQFormalSum.smul_certificateLedger coefficient formalSum)

/-- Scalar multiplication preserves imported finite-rectangle lists. -/
theorem TraceCorQFormalSum.smul_importedRectangles
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).importedRectangles =
      formalSum.importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceCorQFormalSum.smul_certificateLedger coefficient formalSum)

/-- Scalar multiplication preserves internal trace-bookkeeping payload. -/
theorem TraceCorQFormalSum.smul_traceBookkeepingCount
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).traceBookkeepingCount =
      formalSum.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceCorQFormalSum.smul_certificateLedger coefficient formalSum)

/-- Scalar multiplication preserves explicit rewrite-step payload. -/
theorem TraceCorQFormalSum.smul_rewriteStepCount
    (coefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    (TraceCorQFormalSum.smul coefficient formalSum).rewriteStepCount =
      formalSum.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceCorQFormalSum.smul_certificateLedger coefficient formalSum)

end AnalyticMotives
end LFunctions
end Boundary
