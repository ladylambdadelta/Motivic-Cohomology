import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Relation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner

/-!
# Typed trace-correspondence hom classes

This file owns the typed quotient of formal sums whose terms have a common
source and target.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A typed hom representative is a typed formal sum together with a relation ledger. -/
abbrev TraceCorQHomRepresentative
    (source target : TraceCorQObject) :=
  TraceCorQHomFormalSum source target × TraceCorQRelationLedger

/-- The typed formal sum carried by a hom representative. -/
def TraceCorQHomRepresentative.formalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomFormalSum source target :=
  representative.1

/-- The relation ledger carried by a hom representative. -/
def TraceCorQHomRepresentative.ledger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQRelationLedger :=
  representative.2

/-- The raw quotient candidate underlying a typed hom representative. -/
def TraceCorQHomRepresentative.rawCandidate
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.ofFormalSumLedger
    representative.formalSum.raw
    representative.ledger

/-- The analytic certificate ledger carried by a typed hom representative. -/
def TraceCorQHomRepresentative.certificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    ResidueChannelCertificateLedger :=
  representative.rawCandidate.certificateLedger

/-- Build a typed hom representative from a formal sum and ledger. -/
def TraceCorQHomRepresentative.ofFormalSumLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQHomRepresentative source target :=
  (formalSum, ledger)

/-- The raw candidate of a built representative has the raw formal sum. -/
theorem TraceCorQHomRepresentative.ofFormalSumLedger_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      formalSum
      ledger).rawCandidate.formalSum =
      formalSum.raw :=
  rfl

/-- The raw candidate of a built representative has the supplied ledger. -/
theorem TraceCorQHomRepresentative.ofFormalSumLedger_rawCandidate_ledger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      formalSum
      ledger).rawCandidate.ledger =
      ledger :=
  rfl

/-- The certificate ledger of a built representative records formal-sum and relation certificates. -/
theorem TraceCorQHomRepresentative.ofFormalSumLedger_certificateLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      formalSum
      ledger).certificateLedger =
      ResidueChannelCertificateLedger.append
        formalSum.certificateLedger
        ledger.certificateLedger :=
  rfl

/-- The typed hom relation induced by the ambient quotient relation. -/
abbrev TraceCorQHomRelation
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :=
  TraceCorQQuotientRelation left.rawCandidate right.rawCandidate

/-- The typed hom relation is reflexive. -/
def TraceCorQHomRelation.refl
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomRelation representative representative :=
  TraceCorQQuotientRelation.refl representative.rawCandidate

/-- The typed hom relation is symmetric. -/
def TraceCorQHomRelation.symm
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (relation : TraceCorQHomRelation left right) :
    TraceCorQHomRelation right left :=
  TraceCorQQuotientRelation.symm relation

/-- The typed hom relation is transitive. -/
def TraceCorQHomRelation.trans
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelation left middle)
    (second : TraceCorQHomRelation middle right) :
    TraceCorQHomRelation left right :=
  TraceCorQQuotientRelation.trans first second

/-- The setoid on typed hom representatives. -/
def TraceCorQHomSetoid
    (source target : TraceCorQObject) :
    Setoid (TraceCorQHomRepresentative source target) where
  r := TraceCorQHomRelation
  iseqv := {
    refl := TraceCorQHomRelation.refl
    symm := fun relation => TraceCorQHomRelation.symm relation
    trans := fun first second => TraceCorQHomRelation.trans first second
  }

/-- The typed hom quotient from source to target. -/
abbrev TraceCorQHom
    (source target : TraceCorQObject) :=
  Quotient (TraceCorQHomSetoid source target)

/-- The typed hom class represented by a typed representative. -/
def TraceCorQHom.ofRepresentative
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHom source target :=
  Quotient.mk (TraceCorQHomSetoid source target) representative

/-- The typed hom class represented by a typed formal sum and ledger. -/
def TraceCorQHom.ofFormalSumLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQHom source target :=
  TraceCorQHom.ofRepresentative
    (TraceCorQHomRepresentative.ofFormalSumLedger formalSum ledger)

/-- The typed hom class represented by a typed formal sum with empty ledger. -/
def TraceCorQHom.ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom source target :=
  TraceCorQHom.ofFormalSumLedger
    formalSum
    TraceCorQRelationLedger.empty

/-- The zero typed hom class. -/
def TraceCorQHom.zero
    (source target : TraceCorQObject) :
    TraceCorQHom source target :=
  TraceCorQHom.ofFormalSum
    (TraceCorQHomFormalSum.zero source target)

/-- The singleton typed hom class. -/
def TraceCorQHom.singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom source target :=
  TraceCorQHom.ofFormalSum
    (TraceCorQHomFormalSum.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq)

/-- The ambient quotient class underlying a typed representative. -/
def TraceCorQHomRepresentative.ambientClass
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate representative.rawCandidate

/-- A typed relation gives equality of typed hom classes. -/
theorem TraceCorQHom.sound
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (relation : TraceCorQHomRelation left right) :
    TraceCorQHom.ofRepresentative left =
      TraceCorQHom.ofRepresentative right :=
  Quotient.sound relation

/-- Ambient equality of representatives gives the induced typed hom relation. -/
def TraceCorQHomRelation.ofAmbientEq
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (ambient_eq : left.ambientClass = right.ambientClass) :
    TraceCorQHomRelation left right :=
  Quotient.exact ambient_eq

/-- The zero typed hom is represented by the zero typed formal sum. -/
theorem TraceCorQHom.zero_eq_ofFormalSum_zero
    (source target : TraceCorQObject) :
    TraceCorQHom.zero source target =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.zero source target) :=
  rfl

/-- The singleton typed hom is represented by the singleton typed formal sum. -/
theorem TraceCorQHom.singleton_eq_ofFormalSum_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.singleton
      source
      target
      coefficient
      generator
      source_eq
      target_eq =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.singleton
          source
          target
          coefficient
          generator
          source_eq
          target_eq) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
