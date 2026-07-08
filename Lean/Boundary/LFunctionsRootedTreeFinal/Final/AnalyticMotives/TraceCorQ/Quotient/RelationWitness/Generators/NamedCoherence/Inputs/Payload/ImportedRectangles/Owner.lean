import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.CertificateLedgers.Owner

/-!
# Imported-rectangle payload for named-coherence support inputs

This file records the imported finite-rectangle payload carried by named
coherence support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support input splits imported-rectangle count into support and ledger payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.fubini source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportInput source target support)

/-- A schedule-exchange support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput source target support)

/-- A residue-channel support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportInput source target support)

/-- A Stokes-residue support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportInput source target support)

/-- A refinement support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.refinement source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportInput source target support)

/-- An associativity support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.associativity source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportInput source target support)

/-- A left-identity support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportInput source target support)

/-- A right-identity support input splits imported-rectangle count. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).importedRectangleCount =
      support.importedRectangleCount +
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangleCount :=
  TraceCorQQuotientInput.importedRectangleCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportInput source target support)

/-- A Fubini support input splits imported rectangles into support and ledger rectangles. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.fubini source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportInput source target support)

/-- A schedule-exchange support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput source target support)

/-- A residue-channel support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.residueChannel source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportInput source target support)

/-- A Stokes-residue support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.stokesResidue source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportInput source target support)

/-- A refinement support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.refinement source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportInput source target support)

/-- An associativity support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.associativity source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportInput source target support)

/-- A left-identity support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.leftIdentity source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportInput source target support)

/-- A right-identity support input splits imported rectangles. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).importedRectangles =
      support.importedRectangles ++
        (TraceCorQRelationLedger.rightIdentity source target support).importedRectangles :=
  TraceCorQQuotientInput.importedRectangles_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportInput source target support)

end AnalyticMotives
end LFunctions
end Boundary
