import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Owner

/-!
# Two-step filtrations of transport defects

This file records the first associated-graded form of the transport-defect
calculus.  For a two-step composite, the associated graded defect ledger is the
append of the first transport defect layer and the second transport defect
layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The associated-graded defect ledger for a two-step transport composite. -/
def TraceTransport.twoStepAssociatedGradedDefect
    (first second : TraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    (TraceTransport.compFirstDefectLayer first second)
    (TraceTransport.compSecondDefectLayer first second)

/-- The two-step associated-graded defect is the append of the two path defects. -/
theorem TraceTransport.twoStepAssociatedGradedDefect_eq_append
    (first second : TraceTransport) :
    TraceTransport.twoStepAssociatedGradedDefect first second =
      ResidueChannelCertificateLedger.append
        first.defectLedger
        second.defectLedger :=
  rfl

/-- The first associated-graded layer has the first transport path's rewrite count. -/
theorem TraceTransport.compFirstDefectLayer_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.compFirstDefectLayer first second).rewriteStepCount =
      first.path.stepCount + 0 :=
  rfl

/-- The second associated-graded layer has the second transport path's rewrite count. -/
theorem TraceTransport.compSecondDefectLayer_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.compSecondDefectLayer first second).rewriteStepCount =
      second.path.stepCount + 0 :=
  rfl

/-- The two-step associated-graded defect rewrite count is the sum of the two
layer rewrite counts. -/
theorem TraceTransport.twoStepAssociatedGradedDefect_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.twoStepAssociatedGradedDefect
      first
      second).rewriteStepCount =
      (TraceTransport.compFirstDefectLayer first second).rewriteStepCount +
        (TraceTransport.compSecondDefectLayer first second).rewriteStepCount :=
  ResidueChannelCertificateLedger.append_rewriteStepCount
    (TraceTransport.compFirstDefectLayer first second)
    (TraceTransport.compSecondDefectLayer first second)

/-- The two-step associated-graded defect imported-rectangle count is the sum
of the two layer imported-rectangle counts. -/
theorem TraceTransport.twoStepAssociatedGradedDefect_importedRectangleCount
    (first second : TraceTransport) :
    (TraceTransport.twoStepAssociatedGradedDefect
      first
      second).importedRectangleCount =
      (TraceTransport.compFirstDefectLayer first second).importedRectangleCount +
        (TraceTransport.compSecondDefectLayer first second).importedRectangleCount :=
  ResidueChannelCertificateLedger.append_importedRectangleCount
    (TraceTransport.compFirstDefectLayer first second)
    (TraceTransport.compSecondDefectLayer first second)

/-- The two-step associated-graded defect rectangle list is the append of the
two layer rectangle lists. -/
theorem TraceTransport.twoStepAssociatedGradedDefect_importedRectangles
    (first second : TraceTransport) :
    (TraceTransport.twoStepAssociatedGradedDefect
      first
      second).importedRectangles =
      (TraceTransport.compFirstDefectLayer first second).importedRectangles ++
        (TraceTransport.compSecondDefectLayer first second).importedRectangles :=
  ResidueChannelCertificateLedger.append_importedRectangles
    (TraceTransport.compFirstDefectLayer first second)
    (TraceTransport.compSecondDefectLayer first second)

/-- The two-step associated-graded defect bookkeeping count is the sum of the
two layer bookkeeping counts. -/
theorem TraceTransport.twoStepAssociatedGradedDefect_traceBookkeepingCount
    (first second : TraceTransport) :
    (TraceTransport.twoStepAssociatedGradedDefect
      first
      second).traceBookkeepingCount =
      (TraceTransport.compFirstDefectLayer first second).traceBookkeepingCount +
        (TraceTransport.compSecondDefectLayer first second).traceBookkeepingCount :=
  ResidueChannelCertificateLedger.append_traceBookkeepingCount
    (TraceTransport.compFirstDefectLayer first second)
    (TraceTransport.compSecondDefectLayer first second)

end AnalyticMotives
end LFunctions
end Boundary
