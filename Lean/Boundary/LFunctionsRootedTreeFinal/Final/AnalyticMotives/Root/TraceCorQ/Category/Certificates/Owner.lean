import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Certificates.Owner

/-!
# Public category-shape certificate ledgers

This file exposes the concrete support-witness certificate ledger attached to
typed trace-correspondence associativity and identity coherence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the concrete support-witness category-shape ledger. -/
def AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessCertificateLedger
    (first second third : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
    first
    second
    third

/-- The top root exposes the support-witness category-shape imported rectangle count. -/
def AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangleCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount
    first
    second
    third

/-- The top root exposes the support-witness category-shape imported rectangles. -/
def AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangles
    (first second third : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles
    first
    second
    third

/-- The top root exposes the support-witness category-shape bookkeeping count. -/
def AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessTraceBookkeepingCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount
    first
    second
    third

/-- The top root exposes the support-witness category-shape ledger decomposition. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessCertificateLedger_eq
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessCertificateLedger
      first
      second
      third =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.associativitySupportWitness
          first
          second
          third).certificateLedger
        (ResidueChannelCertificateLedger.append
          (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
          (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger) :=
  LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_eq
    first
    second
    third

/-- The top root exposes the support-witness imported rectangle count formula. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangleCount_eq
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangleCount
      first
      second
      third =
      (LedgeredTraceTransport.associativitySupportWitness
        first
        second
        third).importedRectangleCount +
        ((LedgeredTraceTransport.leftIdentitySupportWitness
          first).importedRectangleCount +
          (LedgeredTraceTransport.rightIdentitySupportWitness
            third).importedRectangleCount) :=
  LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount_eq
    first
    second
    third

/-- The top root exposes the support-witness imported rectangles formula. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangles_eq
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangles
      first
      second
      third =
      (LedgeredTraceTransport.associativitySupportWitness
        first
        second
        third).importedRectangles ++
        ((LedgeredTraceTransport.leftIdentitySupportWitness
          first).importedRectangles ++
          (LedgeredTraceTransport.rightIdentitySupportWitness
            third).importedRectangles) :=
  LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles_eq
    first
    second
    third

/-- The top root exposes the support-witness bookkeeping count formula. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessTraceBookkeepingCount_eq
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessTraceBookkeepingCount
      first
      second
      third =
      (LedgeredTraceTransport.associativitySupportWitness
        first
        second
        third).traceBookkeepingCount +
        ((LedgeredTraceTransport.leftIdentitySupportWitness
          first).traceBookkeepingCount +
          (LedgeredTraceTransport.rightIdentitySupportWitness
            third).traceBookkeepingCount) :=
  LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount_eq
    first
    second
    third

/-- The top root exposes normalization to the canonical category-shape ledger. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessCertificateLedger_normalized
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessCertificateLedger
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeCertificateLedger
        first
        second
        third :=
  LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_normalized
    first
    second
    third

/-- The top root exposes normalization of imported rectangle counts. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangleCount_normalized
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangleCount
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeImportedRectangleCount
        first
        second
        third :=
  LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount_normalized
    first
    second
    third

/-- The top root exposes normalization of imported rectangle lists. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangles_normalized
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessImportedRectangles
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeImportedRectangles
        first
        second
        third :=
  LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles_normalized
    first
    second
    third

/-- The top root exposes normalization of bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessTraceBookkeepingCount_normalized
    (first second third : LedgeredTraceTransport) :
    AnalyticMotivesRoot.traceTransportCategoryShapeSupportWitnessTraceBookkeepingCount
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeTraceBookkeepingCount
        first
        second
        third :=
  LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount_normalized
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary
