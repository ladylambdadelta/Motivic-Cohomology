import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Classes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Typed hom relation witnesses

This file keeps the data-bearing version of typed hom equality.  The setoid
relation on typed hom representatives is proof-valued, but before quotienting
we can retain the concrete finite relation witness and its analytic certificate
ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A concrete typed witness relating two hom representatives. -/
abbrev TraceCorQHomRelationWitness
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :=
  TraceCorQRelationWitness left.rawCandidate right.rawCandidate

/-- The finite relation ledger carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQRelationLedger :=
  TraceCorQRelationWitness.ledger witness

/-- The analytic certificate ledger carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.certificateLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  TraceCorQRelationWitness.certificateLedger witness

/-- The imported finite-rectangle payload carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.importedRectangleCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.importedRectangleCount witness

/-- The internal trace-bookkeeping payload carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.traceBookkeepingCount witness

/-- A typed hom relation witness induces the proof-valued typed hom relation. -/
def TraceCorQHomRelation.ofWitness
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHomRelation left right :=
  TraceCorQQuotientRelation.ofWitness witness

/-- Reflexive typed hom relation witness. -/
def TraceCorQHomRelationWitness.refl
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomRelationWitness representative representative :=
  TraceCorQRelationWitness.refl representative.rawCandidate

/-- Symmetry for typed hom relation witnesses. -/
def TraceCorQHomRelationWitness.symm
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHomRelationWitness right left :=
  TraceCorQRelationWitness.symm witness

/-- Transitivity for typed hom relation witnesses. -/
def TraceCorQHomRelationWitness.trans
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    TraceCorQHomRelationWitness left right :=
  TraceCorQRelationWitness.trans first second

/-- A typed witness built by reflexivity carries the empty certificate ledger. -/
theorem TraceCorQHomRelationWitness.refl_certificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationWitness.refl_certificateLedger representative.rawCandidate

/-- A typed witness built by reflexivity carries no imported finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.refl_importedRectangleCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).importedRectangleCount =
      0 :=
  TraceCorQRelationWitness.refl_importedRectangleCount representative.rawCandidate

/-- A typed witness built by reflexivity carries no internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.refl_traceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).traceBookkeepingCount =
      0 :=
  TraceCorQRelationWitness.refl_traceBookkeepingCount representative.rawCandidate

/-- Symmetry preserves typed witness certificate ledgers. -/
theorem TraceCorQHomRelationWitness.symm_certificateLedger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).certificateLedger =
      witness.certificateLedger :=
  TraceCorQRelationWitness.symm_certificateLedger witness

/-- Symmetry preserves typed witness imported finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.symm_importedRectangleCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).importedRectangleCount =
      witness.importedRectangleCount :=
  TraceCorQRelationWitness.symm_importedRectangleCount witness

/-- Symmetry preserves typed witness internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.symm_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQRelationWitness.symm_traceBookkeepingCount witness

/-- Transitivity appends typed witness certificate ledgers. -/
theorem TraceCorQHomRelationWitness.trans_certificateLedger
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  TraceCorQRelationWitness.trans_certificateLedger first second

/-- Transitivity adds typed witness imported finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.trans_importedRectangleCount
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  TraceCorQRelationWitness.trans_importedRectangleCount first second

/-- Transitivity adds typed witness internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.trans_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  TraceCorQRelationWitness.trans_traceBookkeepingCount first second

/-- Soundness for data-bearing typed hom relation witnesses. -/
theorem TraceCorQHom.soundWitness
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    TraceCorQHom.ofRepresentative left =
      TraceCorQHom.ofRepresentative right :=
  TraceCorQHom.sound
    (TraceCorQHomRelation.ofWitness witness)

end AnalyticMotives
end LFunctions
end Boundary
