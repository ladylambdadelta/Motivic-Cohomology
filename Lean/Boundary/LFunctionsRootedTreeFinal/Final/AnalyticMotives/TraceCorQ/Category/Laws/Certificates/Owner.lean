import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.AssociativitySupport.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Certificates.Owner

/-!
# Category-law certificate ledgers

This file connects the category-shape certificate ledger for ledgered
transports to the concrete quotient support witnesses used to impose
associativity and identity relations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The category-shape certificate ledger obtained from concrete support witnesses. -/
def LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
    (first second third : LedgeredTraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    (LedgeredTraceTransport.associativitySupportWitness
      first
      second
      third).certificateLedger
    (ResidueChannelCertificateLedger.append
      (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
      (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger)

/-- Imported finite-rectangle payload of the concrete support-witness category-shape ledger. -/
def LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
    first
    second
    third).importedRectangleCount

/-- Imported finite rectangles of the concrete support-witness category-shape ledger. -/
def LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles
    (first second third : LedgeredTraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  (LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
    first
    second
    third).importedRectangles

/-- Internal trace-bookkeeping payload of the concrete support-witness category-shape ledger. -/
def LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount
    (first second third : LedgeredTraceTransport) :
    Nat :=
  (LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
    first
    second
    third).traceBookkeepingCount

/-- The support-witness category-shape ledger is the append of the three support witness ledgers. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
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
  rfl

/-- Support-witness category-shape imported payload is the three support witness payloads. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount
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
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      (LedgeredTraceTransport.associativitySupportWitness
        first
        second
        third).certificateLedger
      (ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
        (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger))
    (congrArg
      (fun count =>
        (LedgeredTraceTransport.associativitySupportWitness
          first
          second
          third).importedRectangleCount +
          count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
        (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger))

/-- Support-witness category-shape imported rectangles are the three support witness rectangle lists. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles
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
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangles
      (LedgeredTraceTransport.associativitySupportWitness
        first
        second
        third).certificateLedger
      (ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
        (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger))
    (congrArg
      (fun rectangles =>
        (LedgeredTraceTransport.associativitySupportWitness
          first
          second
          third).importedRectangles ++
          rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
        (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
        (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger))

/-- Support-witness category-shape bookkeeping payload is the three support witness payloads. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount_eq
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount
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
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      (LedgeredTraceTransport.associativitySupportWitness
        first
        second
        third).certificateLedger
      (ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
        (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger))
    (congrArg
      (fun count =>
        (LedgeredTraceTransport.associativitySupportWitness
          first
          second
          third).traceBookkeepingCount +
          count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (LedgeredTraceTransport.leftIdentitySupportWitness first).certificateLedger
        (LedgeredTraceTransport.rightIdentitySupportWitness third).certificateLedger))

/-- Remove singleton-empty tails from three appended certificate ledgers. -/
theorem ResidueChannelCertificateLedger.append_three_singleton_empty
    (first second third : ResidueChannelCertificateLedger) :
    ResidueChannelCertificateLedger.append
      (ResidueChannelCertificateLedger.append
        first
        ResidueChannelCertificateLedger.empty)
      (ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          second
          ResidueChannelCertificateLedger.empty)
        (ResidueChannelCertificateLedger.append
          third
          ResidueChannelCertificateLedger.empty)) =
      ResidueChannelCertificateLedger.append
        first
        (ResidueChannelCertificateLedger.append second third) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_assoc
      first
      ResidueChannelCertificateLedger.empty
      (ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          second
          ResidueChannelCertificateLedger.empty)
        (ResidueChannelCertificateLedger.append
          third
          ResidueChannelCertificateLedger.empty)))
    (Eq.trans
      (congrArg
        (ResidueChannelCertificateLedger.append first)
        (ResidueChannelCertificateLedger.empty_append
          (ResidueChannelCertificateLedger.append
            (ResidueChannelCertificateLedger.append
              second
              ResidueChannelCertificateLedger.empty)
            (ResidueChannelCertificateLedger.append
              third
              ResidueChannelCertificateLedger.empty))))
      (congrArg
        (ResidueChannelCertificateLedger.append first)
        (Eq.trans
          (ResidueChannelCertificateLedger.append_assoc
            second
            ResidueChannelCertificateLedger.empty
            (ResidueChannelCertificateLedger.append
              third
              ResidueChannelCertificateLedger.empty))
          (Eq.trans
            (congrArg
              (ResidueChannelCertificateLedger.append second)
              (ResidueChannelCertificateLedger.empty_append
                (ResidueChannelCertificateLedger.append
                  third
                  ResidueChannelCertificateLedger.empty)))
            (congrArg
              (ResidueChannelCertificateLedger.append second)
              (ResidueChannelCertificateLedger.append_empty third))))))

/--
The concrete support-witness certificate ledger is the category-shape
certificate ledger.
-/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_normalized
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeCertificateLedger
        first
        second
        third :=
  Eq.trans
    (congrArg₂
      ResidueChannelCertificateLedger.append
      (LedgeredTraceTransport.associativitySupportWitness_certificateLedger
        first
        second
        third)
      (congrArg₂
        ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentitySupportWitness_certificateLedger
          first)
        (LedgeredTraceTransport.rightIdentitySupportWitness_certificateLedger
          third)))
    (ResidueChannelCertificateLedger.append_three_singleton_empty
      (LedgeredTraceTransport.associativityCertificateLedger
        first
        second
        third)
      (LedgeredTraceTransport.leftIdentityCertificateLedger first)
      (LedgeredTraceTransport.rightIdentityCertificateLedger third))

/-- The concrete support-witness imported payload is the category-shape imported payload. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount_normalized
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangleCount
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeImportedRectangleCount
        first
        second
        third :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_normalized
      first
      second
      third)

/-- The concrete support-witness imported rectangles are the category-shape imported rectangles. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles_normalized
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessImportedRectangles
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeImportedRectangles
        first
        second
        third :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_normalized
      first
      second
      third)

/-- The concrete support-witness bookkeeping payload is the category-shape bookkeeping payload. -/
theorem LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount_normalized
    (first second third : LedgeredTraceTransport) :
    LedgeredTraceTransport.categoryShapeSupportWitnessTraceBookkeepingCount
      first
      second
      third =
      LedgeredTraceTransport.categoryShapeTraceBookkeepingCount
        first
        second
        third :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (LedgeredTraceTransport.categoryShapeSupportWitnessCertificateLedger_normalized
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary
