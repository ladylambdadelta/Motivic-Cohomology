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

/-- The imported finite explicit-formula rectangles carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.importedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceCorQRelationWitness.importedRectangles witness

/-- The internal trace-bookkeeping payload carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.traceBookkeepingCount witness

/-- The explicit rewrite-step payload carried by a typed hom relation witness. -/
def TraceCorQHomRelationWitness.rewriteStepCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    Nat :=
  TraceCorQRelationWitness.rewriteStepCount witness

/-- A typed hom relation witness has the same ledger as the underlying raw witness. -/
theorem TraceCorQHomRelationWitness.ledger_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.ledger =
      TraceCorQRelationWitness.ledger witness :=
  rfl

/-- A typed hom relation witness has the same certificate ledger as the raw witness. -/
theorem TraceCorQHomRelationWitness.certificateLedger_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.certificateLedger =
      TraceCorQRelationWitness.certificateLedger witness :=
  rfl

/-- A typed hom relation witness imports the same payload as the raw witness. -/
theorem TraceCorQHomRelationWitness.importedRectangleCount_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      TraceCorQRelationWitness.importedRectangleCount witness :=
  rfl

/-- A typed hom relation witness exposes the same imported rectangles as the raw witness. -/
theorem TraceCorQHomRelationWitness.importedRectangles_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangles =
      TraceCorQRelationWitness.importedRectangles witness :=
  rfl

/-- A typed hom relation witness keeps the same bookkeeping payload as the raw witness. -/
theorem TraceCorQHomRelationWitness.traceBookkeepingCount_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.traceBookkeepingCount =
      TraceCorQRelationWitness.traceBookkeepingCount witness :=
  rfl

/-- A typed hom relation witness keeps the same rewrite-step payload as the raw witness. -/
theorem TraceCorQHomRelationWitness.rewriteStepCount_eq_raw
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.rewriteStepCount =
      TraceCorQRelationWitness.rewriteStepCount witness :=
  rfl

/-- A typed hom relation witness carries exactly its ledger's certificates. -/
theorem TraceCorQHomRelationWitness.certificateLedger_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.certificateLedger =
      witness.ledger.certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger witness

/-- A typed hom relation witness imports exactly its ledger's finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.importedRectangleCount_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      witness.ledger.importedRectangleCount :=
  TraceCorQRelationWitness.importedRectangleCount_eq_ledger witness

/-- A typed hom relation witness exposes exactly its ledger's imported rectangles. -/
theorem TraceCorQHomRelationWitness.importedRectangles_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangles =
      witness.ledger.importedRectangles :=
  TraceCorQRelationWitness.importedRectangles_eq_ledger witness

/-- A typed hom relation witness's imported count is the length of its rectangle list. -/
theorem TraceCorQHomRelationWitness.importedRectangleCount_eq_length_importedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.importedRectangleCount =
      witness.importedRectangles.length :=
  TraceCorQRelationWitness.importedRectangleCount_eq_length_importedRectangles
    witness

/-- A typed hom relation witness keeps exactly its ledger's bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.traceBookkeepingCount_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.traceBookkeepingCount =
      witness.ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger witness

/-- A typed hom relation witness keeps exactly its ledger's rewrite-step payload. -/
theorem TraceCorQHomRelationWitness.rewriteStepCount_eq_ledger
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    witness.rewriteStepCount =
      witness.ledger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger witness

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

/-- A typed witness built by reflexivity exposes no imported finite explicit-formula rectangles. -/
theorem TraceCorQHomRelationWitness.refl_importedRectangles
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).importedRectangles =
      [] :=
  TraceCorQRelationWitness.refl_importedRectangles representative.rawCandidate

/-- A typed witness built by reflexivity carries no internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.refl_traceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).traceBookkeepingCount =
      0 :=
  TraceCorQRelationWitness.refl_traceBookkeepingCount representative.rawCandidate

/-- A typed witness built by reflexivity carries no explicit rewrite-step payload. -/
theorem TraceCorQHomRelationWitness.refl_rewriteStepCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.refl representative).rewriteStepCount =
      0 :=
  TraceCorQRelationWitness.refl_rewriteStepCount representative.rawCandidate

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

/-- Symmetry preserves typed witness imported finite explicit-formula rectangles. -/
theorem TraceCorQHomRelationWitness.symm_importedRectangles
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).importedRectangles =
      witness.importedRectangles :=
  TraceCorQRelationWitness.symm_importedRectangles witness

/-- Symmetry preserves typed witness internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.symm_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  TraceCorQRelationWitness.symm_traceBookkeepingCount witness

/-- Symmetry preserves typed witness explicit rewrite-step payload. -/
theorem TraceCorQHomRelationWitness.symm_rewriteStepCount
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (witness : TraceCorQHomRelationWitness left right) :
    (TraceCorQHomRelationWitness.symm witness).rewriteStepCount =
      witness.rewriteStepCount :=
  TraceCorQRelationWitness.symm_rewriteStepCount witness

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

/-- Transitivity concatenates typed witness imported finite explicit-formula rectangles. -/
theorem TraceCorQHomRelationWitness.trans_importedRectangles
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).importedRectangles =
      first.importedRectangles ++
        second.importedRectangles :=
  TraceCorQRelationWitness.trans_importedRectangles first second

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

/-- Transitivity adds typed witness explicit rewrite-step payload. -/
theorem TraceCorQHomRelationWitness.trans_rewriteStepCount
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelationWitness left middle)
    (second : TraceCorQHomRelationWitness middle right) :
    (TraceCorQHomRelationWitness.trans first second).rewriteStepCount =
      first.rewriteStepCount +
        second.rewriteStepCount :=
  TraceCorQRelationWitness.trans_rewriteStepCount first second

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
