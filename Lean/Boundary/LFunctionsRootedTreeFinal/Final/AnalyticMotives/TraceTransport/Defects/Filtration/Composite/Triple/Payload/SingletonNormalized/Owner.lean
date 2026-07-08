import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.Composite.Triple.Payload.Right.Owner

/-!
# Singleton-normalized triple composite payload formulas

This file rewrites the singleton finite-chain terms in the triple payload
formulas to the concrete defect ledgers of the three transports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A singleton finite-chain defect has the transport defect rewrite-step count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount
    (transport : TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect [transport]).rewriteStepCount =
      transport.defectLedger.rewriteStepCount :=
  congrArg
    ResidueChannelCertificateLedger.rewriteStepCount
    (TraceTransport.finiteChainAssociatedGradedDefect_singleton transport)

/-- A singleton finite-chain defect has the transport defect imported-rectangle count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount
    (transport : TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect [transport]).importedRectangleCount =
      transport.defectLedger.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceTransport.finiteChainAssociatedGradedDefect_singleton transport)

/-- A singleton finite-chain defect has the transport defect rectangle list. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles
    (transport : TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect [transport]).importedRectangles =
      transport.defectLedger.importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceTransport.finiteChainAssociatedGradedDefect_singleton transport)

/-- A singleton finite-chain defect has the transport defect bookkeeping count. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount
    (transport : TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect [transport]).traceBookkeepingCount =
      transport.defectLedger.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceTransport.finiteChainAssociatedGradedDefect_singleton transport)

/-- The left-associated triple defect rewrite-step count is the right-associated
sum of the three concrete transport defect rewrite-step counts. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_rewriteStepCount_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).rewriteStepCount =
      first.defectLedger.rewriteStepCount +
        (second.defectLedger.rewriteStepCount +
          third.defectLedger.rewriteStepCount) :=
  Eq.trans
    (TraceTransport.leftTripleAssociatedGradedDefect_rewriteStepCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).rewriteStepCount +
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).rewriteStepCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount first))
      (Eq.trans
        (congrArg
          (fun count =>
            first.defectLedger.rewriteStepCount +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).rewriteStepCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount second))
        (congrArg
          (fun count =>
            first.defectLedger.rewriteStepCount +
              (second.defectLedger.rewriteStepCount + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount third))))

/-- The left-associated triple defect imported-rectangle count is the
right-associated sum of the three concrete transport defect imported-rectangle counts. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_importedRectangleCount_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).importedRectangleCount =
      first.defectLedger.importedRectangleCount +
        (second.defectLedger.importedRectangleCount +
          third.defectLedger.importedRectangleCount) :=
  Eq.trans
    (TraceTransport.leftTripleAssociatedGradedDefect_importedRectangleCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangleCount +
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangleCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount first))
      (Eq.trans
        (congrArg
          (fun count =>
            first.defectLedger.importedRectangleCount +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangleCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount second))
        (congrArg
          (fun count =>
            first.defectLedger.importedRectangleCount +
              (second.defectLedger.importedRectangleCount + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount third))))

/-- The left-associated triple defect rectangle list is the right-associated
append of the three concrete transport defect rectangle lists. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_importedRectangles_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).importedRectangles =
      first.defectLedger.importedRectangles ++
        (second.defectLedger.importedRectangles ++
          third.defectLedger.importedRectangles) :=
  Eq.trans
    (TraceTransport.leftTripleAssociatedGradedDefect_importedRectangles
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun rectangles =>
          rectangles ++
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangles ++
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangles))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles first))
      (Eq.trans
        (congrArg
          (fun rectangles =>
            first.defectLedger.importedRectangles ++
              (rectangles ++
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangles))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles second))
        (congrArg
          (fun rectangles =>
            first.defectLedger.importedRectangles ++
              (second.defectLedger.importedRectangles ++ rectangles))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles third))))

/-- The left-associated triple defect bookkeeping count is the right-associated
sum of the three concrete transport defect bookkeeping counts. -/
theorem TraceTransport.leftTripleAssociatedGradedDefect_traceBookkeepingCount_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.leftTripleAssociatedGradedDefect
      first
      second
      third).traceBookkeepingCount =
      first.defectLedger.traceBookkeepingCount +
        (second.defectLedger.traceBookkeepingCount +
          third.defectLedger.traceBookkeepingCount) :=
  Eq.trans
    (TraceTransport.leftTripleAssociatedGradedDefect_traceBookkeepingCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).traceBookkeepingCount +
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).traceBookkeepingCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount first))
      (Eq.trans
        (congrArg
          (fun count =>
            first.defectLedger.traceBookkeepingCount +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).traceBookkeepingCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount second))
        (congrArg
          (fun count =>
            first.defectLedger.traceBookkeepingCount +
              (second.defectLedger.traceBookkeepingCount + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount third))))

/-- The right-associated triple defect rewrite-step count is the right-associated
sum of the three concrete transport defect rewrite-step counts. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_rewriteStepCount_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).rewriteStepCount =
      first.defectLedger.rewriteStepCount +
        (second.defectLedger.rewriteStepCount +
          third.defectLedger.rewriteStepCount) :=
  Eq.trans
    (TraceTransport.rightTripleAssociatedGradedDefect_rewriteStepCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).rewriteStepCount +
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).rewriteStepCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount first))
      (Eq.trans
        (congrArg
          (fun count =>
            first.defectLedger.rewriteStepCount +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).rewriteStepCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount second))
        (congrArg
          (fun count =>
            first.defectLedger.rewriteStepCount +
              (second.defectLedger.rewriteStepCount + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_rewriteStepCount third))))

/-- The right-associated triple defect imported-rectangle count is the
right-associated sum of the three concrete transport defect imported-rectangle counts. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_importedRectangleCount_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).importedRectangleCount =
      first.defectLedger.importedRectangleCount +
        (second.defectLedger.importedRectangleCount +
          third.defectLedger.importedRectangleCount) :=
  Eq.trans
    (TraceTransport.rightTripleAssociatedGradedDefect_importedRectangleCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangleCount +
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangleCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount first))
      (Eq.trans
        (congrArg
          (fun count =>
            first.defectLedger.importedRectangleCount +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangleCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount second))
        (congrArg
          (fun count =>
            first.defectLedger.importedRectangleCount +
              (second.defectLedger.importedRectangleCount + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangleCount third))))

/-- The right-associated triple defect rectangle list is the right-associated
append of the three concrete transport defect rectangle lists. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_importedRectangles_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).importedRectangles =
      first.defectLedger.importedRectangles ++
        (second.defectLedger.importedRectangles ++
          third.defectLedger.importedRectangles) :=
  Eq.trans
    (TraceTransport.rightTripleAssociatedGradedDefect_importedRectangles
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun rectangles =>
          rectangles ++
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).importedRectangles ++
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangles))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles first))
      (Eq.trans
        (congrArg
          (fun rectangles =>
            first.defectLedger.importedRectangles ++
              (rectangles ++
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).importedRectangles))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles second))
        (congrArg
          (fun rectangles =>
            first.defectLedger.importedRectangles ++
              (second.defectLedger.importedRectangles ++ rectangles))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_importedRectangles third))))

/-- The right-associated triple defect bookkeeping count is the right-associated
sum of the three concrete transport defect bookkeeping counts. -/
theorem TraceTransport.rightTripleAssociatedGradedDefect_traceBookkeepingCount_defectLedger
    (first second third : TraceTransport) :
    (TraceTransport.rightTripleAssociatedGradedDefect
      first
      second
      third).traceBookkeepingCount =
      first.defectLedger.traceBookkeepingCount +
        (second.defectLedger.traceBookkeepingCount +
          third.defectLedger.traceBookkeepingCount) :=
  Eq.trans
    (TraceTransport.rightTripleAssociatedGradedDefect_traceBookkeepingCount
      first
      second
      third)
    (Eq.trans
      (congrArg
        (fun count =>
          count +
            ((TraceTransport.finiteChainAssociatedGradedDefect [second]).traceBookkeepingCount +
              (TraceTransport.finiteChainAssociatedGradedDefect [third]).traceBookkeepingCount))
        (TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount first))
      (Eq.trans
        (congrArg
          (fun count =>
            first.defectLedger.traceBookkeepingCount +
              (count +
                (TraceTransport.finiteChainAssociatedGradedDefect [third]).traceBookkeepingCount))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount second))
        (congrArg
          (fun count =>
            first.defectLedger.traceBookkeepingCount +
              (second.defectLedger.traceBookkeepingCount + count))
          (TraceTransport.finiteChainAssociatedGradedDefect_singleton_traceBookkeepingCount third))))

end AnalyticMotives
end LFunctions
end Boundary
