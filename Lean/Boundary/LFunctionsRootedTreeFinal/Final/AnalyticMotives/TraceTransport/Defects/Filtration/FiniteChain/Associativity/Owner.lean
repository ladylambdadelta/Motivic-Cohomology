import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Defects.Filtration.FiniteChain.Append.Owner

/-!
# Associativity for finite-chain defect filtrations

This file records the three-block associativity law for finite transport-chain
associated-graded defect ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The associated-graded defect ledger of three concatenated transport chains
is the right-associated append of the three associated-graded defect ledgers. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc
    (first second third : List TraceTransport) :
    TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third) =
      ResidueChannelCertificateLedger.append
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)) :=
  Eq.trans
    (TraceTransport.finiteChainAssociatedGradedDefect_append
      (first ++ second)
      third)
    (Eq.trans
      (congrArg
        (fun ledger =>
          ResidueChannelCertificateLedger.append
            ledger
            (TraceTransport.finiteChainAssociatedGradedDefect third))
        (TraceTransport.finiteChainAssociatedGradedDefect_append
          first
          second))
      (ResidueChannelCertificateLedger.append_assoc
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (TraceTransport.finiteChainAssociatedGradedDefect second)
        (TraceTransport.finiteChainAssociatedGradedDefect third)))

/-- The rewrite-step payload of a three-block associated-graded defect ledger is
the right-associated sum of the three block payloads. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_rewriteStepCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).rewriteStepCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).rewriteStepCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).rewriteStepCount) :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc
        first
        second
        third))
    (Eq.trans
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)))
      (congrArg
        (fun count =>
          (TraceTransport.finiteChainAssociatedGradedDefect first).rewriteStepCount +
            count)
        (ResidueChannelCertificateLedger.append_rewriteStepCount
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third))))

/-- The imported-rectangle payload of a three-block associated-graded defect
ledger is the right-associated sum of the three block payloads. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangleCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangleCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangleCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangleCount) :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc
        first
        second
        third))
    (Eq.trans
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)))
      (congrArg
        (fun count =>
          (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangleCount +
            count)
        (ResidueChannelCertificateLedger.append_importedRectangleCount
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third))))

/-- The rectangle-list payload of a three-block associated-graded defect ledger
is the right-associated append of the three block payloads. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_importedRectangles
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).importedRectangles =
      (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
        ((TraceTransport.finiteChainAssociatedGradedDefect second).importedRectangles ++
          (TraceTransport.finiteChainAssociatedGradedDefect third).importedRectangles) :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc
        first
        second
        third))
    (Eq.trans
      (ResidueChannelCertificateLedger.append_importedRectangles
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)))
      (congrArg
        (fun rectangles =>
          (TraceTransport.finiteChainAssociatedGradedDefect first).importedRectangles ++
            rectangles)
        (ResidueChannelCertificateLedger.append_importedRectangles
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third))))

/-- The bookkeeping payload of a three-block associated-graded defect ledger is
the right-associated sum of the three block payloads. -/
theorem TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc_traceBookkeepingCount
    (first second third : List TraceTransport) :
    (TraceTransport.finiteChainAssociatedGradedDefect
      ((first ++ second) ++ third)).traceBookkeepingCount =
      (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
        ((TraceTransport.finiteChainAssociatedGradedDefect second).traceBookkeepingCount +
          (TraceTransport.finiteChainAssociatedGradedDefect third).traceBookkeepingCount) :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceTransport.finiteChainAssociatedGradedDefect_append_append_assoc
        first
        second
        third))
    (Eq.trans
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (TraceTransport.finiteChainAssociatedGradedDefect first)
        (ResidueChannelCertificateLedger.append
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third)))
      (congrArg
        (fun count =>
          (TraceTransport.finiteChainAssociatedGradedDefect first).traceBookkeepingCount +
            count)
        (ResidueChannelCertificateLedger.append_traceBookkeepingCount
          (TraceTransport.finiteChainAssociatedGradedDefect second)
          (TraceTransport.finiteChainAssociatedGradedDefect third))))

end AnalyticMotives
end LFunctions
end Boundary
