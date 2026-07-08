import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.CertificateLedgers.Owner

/-!
# Imported-rectangle payload for named-coherence support witnesses

This file exposes imported finite-rectangle accounting carried by the canonical
witnesses generated from named coherence relations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support witness carries no imported finite rectangles. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.fubini source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support)

/-- A schedule-exchange support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support)

/-- A residue-channel support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.residueChannel source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support)

/-- A Stokes-residue support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.stokesResidue source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support)

/-- A refinement support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.refinement source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.refinementSupportWitness source target support)

/-- An associativity support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.associativity source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.associativitySupportWitness source target support)

/-- A left-identity support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.leftIdentity source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support)

/-- A right-identity support witness carries the ledger imported-rectangle count. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_importedRectangleCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).importedRectangleCount =
      (TraceCorQRelationLedger.rightIdentity source target support).importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support)

/-- A Fubini support witness exposes the Fubini ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.fubini source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support)

/-- A schedule-exchange support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.scheduleExchange source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support)

/-- A residue-channel support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.residueChannel source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support)

/-- A Stokes-residue support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.stokesResidue source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support)

/-- A refinement support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.refinement source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.refinementSupportWitness source target support)

/-- An associativity support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.associativity source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.associativitySupportWitness source target support)

/-- A left-identity support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.leftIdentity source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support)

/-- A right-identity support witness exposes the ledger imported rectangles. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_importedRectangles
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).importedRectangles =
      (TraceCorQRelationLedger.rightIdentity source target support).importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support)

end AnalyticMotives
end LFunctions
end Boundary
