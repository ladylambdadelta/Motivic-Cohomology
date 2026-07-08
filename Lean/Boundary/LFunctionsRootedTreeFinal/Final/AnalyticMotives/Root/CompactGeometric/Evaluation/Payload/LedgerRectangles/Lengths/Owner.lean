import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Payload.LedgerRectangles.Lengths.Owner

/-!
# Top-root compact evaluation ledger rectangle lengths

This file exposes the count-as-length fact for the certificate-ledger rectangle
list carried by a compact evaluation point.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The evaluation certificate-ledger rectangle list has the evaluation imported count. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_certificateLedgerRectangles_length_root
    (generator : TraceAnalyticGeometricGenerator) :
    generator.certificateLedger.importedRectangleCount =
      generator.certificateLedger.importedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_evaluation_certificateLedgerRectangles_length_root
    generator

end AnalyticMotives
end LFunctions
end Boundary
