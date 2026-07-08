import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.Representative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RawQuotientRelation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner

/-!
# Relation-witness carriers for analytic effective realization

This file exposes concrete typed witnesses between trace hom representatives.
These witnesses are the data used later to prove that a representative-level
effective realization is well-defined on quotient homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessCarrier
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHomRelationWitness left right :=
  witness

/-- The relation ledger carried by a typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQRelationLedger :=
  witness.ledger

/-- The analytic certificate ledger carried by a typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessCertificateLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  witness.certificateLedger

/-- The imported finite-rectangle count carried by a typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangleCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  witness.importedRectangleCount

/-- The imported finite rectangles carried by a typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  witness.importedRectangles

/-- The trace-bookkeeping count carried by a typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessTraceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  witness.traceBookkeepingCount

/-- The rewrite-step count carried by a typed hom relation witness. -/
def TraceAnalyticEffectiveRealization.traceHomRelationWitnessRewriteStepCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  witness.rewriteStepCount

/-- A typed relation witness induces the proof-valued typed hom relation. -/
def TraceAnalyticEffectiveRealization.traceHomRelationOfWitness
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHomRelation left right :=
  TraceCorQHomRelation.ofWitness witness

/-- The relation-witness carrier is definitionally the supplied witness. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationWitnessCarrier_eq
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationWitnessCarrier witness =
      witness :=
  rfl

/-- A typed relation witness carries exactly its relation ledger's certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationWitnessCertificateLedger_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationWitnessCertificateLedger witness =
      (TraceAnalyticEffectiveRealization.traceHomRelationWitnessLedger
        witness).certificateLedger :=
  TraceCorQHomRelationWitness.certificateLedger_eq_ledger
    witness

/-- A typed relation witness imports exactly its relation ledger's rectangles. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangles_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangles witness =
      (TraceAnalyticEffectiveRealization.traceHomRelationWitnessLedger
        witness).importedRectangles :=
  TraceCorQHomRelationWitness.importedRectangles_eq_ledger
    witness

/-- A typed relation witness's imported count is the length of its rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangleCount witness =
      (TraceAnalyticEffectiveRealization.traceHomRelationWitnessImportedRectangles
        witness).length :=
  TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    witness

/-- A reflexive typed relation witness carries the empty certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationWitnessRefl_certificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomRelationWitnessCertificateLedger
      (TraceCorQHomRelationWitness.refl representative) =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQHomRelationWitness.refl_certificateLedger
    representative

end AnalyticMotives
end LFunctions
end Boundary
