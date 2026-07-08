import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner

/-!
# Public typed trace-correspondence hom classes

This file exposes representative constructors, typed quotient relations, and
the ambient forgetful map for typed trace-correspondence hom classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes built representative raw formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_ofFormalSumLedger_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      formalSum
      ledger).rawCandidate.formalSum =
      formalSum.raw :=
  TraceCorQHomRepresentative.ofFormalSumLedger_rawCandidate_formalSum
    formalSum
    ledger

/-- The top root exposes built representative raw ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_ofFormalSumLedger_rawCandidate_ledger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      formalSum
      ledger).rawCandidate.ledger =
      ledger :=
  TraceCorQHomRepresentative.ofFormalSumLedger_rawCandidate_ledger
    formalSum
    ledger

/-- The top root exposes built representative certificate-ledger splitting. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_ofFormalSumLedger_certificateLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQHomRepresentative.ofFormalSumLedger
      formalSum
      ledger).certificateLedger =
      ResidueChannelCertificateLedger.append
        formalSum.certificateLedger
        ledger.certificateLedger :=
  TraceCorQHomRepresentative.ofFormalSumLedger_certificateLedger
    formalSum
    ledger

/-- The top root exposes reflexivity of the typed hom relation. -/
def AnalyticMotivesRoot.traceCorQHomRelationRefl
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomRelation representative representative :=
  TraceCorQHomRelation.refl
    representative

/-- The top root exposes symmetry of the typed hom relation. -/
def AnalyticMotivesRoot.traceCorQHomRelationSymm
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (relation : TraceCorQHomRelation left right) :
    TraceCorQHomRelation right left :=
  TraceCorQHomRelation.symm
    relation

/-- The top root exposes transitivity of the typed hom relation. -/
def AnalyticMotivesRoot.traceCorQHomRelationTrans
    {source target : TraceCorQObject}
    {left middle right : TraceCorQHomRepresentative source target}
    (first : TraceCorQHomRelation left middle)
    (second : TraceCorQHomRelation middle right) :
    TraceCorQHomRelation left right :=
  TraceCorQHomRelation.trans
    first
    second

/-- The top root exposes equality soundness for typed hom relations. -/
theorem AnalyticMotivesRoot.traceCorQHom_sound
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (relation : TraceCorQHomRelation left right) :
    TraceCorQHom.ofRepresentative left =
      TraceCorQHom.ofRepresentative right :=
  TraceCorQHom.sound
    relation

/-- The top root exposes the typed relation induced by ambient equality. -/
def AnalyticMotivesRoot.traceCorQHomRelationOfAmbientEq
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (ambient_eq : left.ambientClass = right.ambientClass) :
    TraceCorQHomRelation left right :=
  TraceCorQHomRelation.ofAmbientEq
    ambient_eq

/-- The top root exposes zero typed homs as zero typed formal-sum classes. -/
theorem AnalyticMotivesRoot.traceCorQHom_zero_eq_ofFormalSum_zero_class
    (source target : TraceCorQObject) :
    TraceCorQHom.zero source target =
      TraceCorQHom.ofFormalSum
        (TraceCorQHomFormalSum.zero source target) :=
  TraceCorQHom.zero_eq_ofFormalSum_zero
    source
    target

/-- The top root exposes singleton typed homs as singleton typed formal-sum classes. -/
theorem AnalyticMotivesRoot.traceCorQHom_singleton_eq_ofFormalSum_singleton_class
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
  TraceCorQHom.singleton_eq_ofFormalSum_singleton
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes the ambient quotient of a representative class. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_ofRepresentative
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofRepresentative representative) =
      representative.ambientClass :=
  TraceCorQHom.ambient_ofRepresentative
    representative

/-- The top root exposes ambient classes of formal-sum-and-ledger typed homs. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_ofFormalSumLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofFormalSumLedger formalSum ledger) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger formalSum.raw ledger) :=
  TraceCorQHom.ambient_ofFormalSumLedger
    formalSum
    ledger

/-- The top root exposes ambient classes of typed formal-sum homs. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_ofFormalSum
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.ofFormalSum formalSum) =
      TraceCorQQuotient.ofFormalSum formalSum.raw :=
  TraceCorQHom.ambient_ofFormalSum
    formalSum

/-- The top root exposes the ambient class of typed zero homs. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_zero_class
    (source target : TraceCorQObject) :
    TraceCorQHom.ambient
      (TraceCorQHom.zero source target) =
      TraceCorQQuotient.zero :=
  TraceCorQHom.ambient_zero
    source
    target

/-- The top root exposes the ambient class of typed singleton homs. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_singleton
    (source target : TraceCorQObject)
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (source_eq : generator.source = source)
    (target_eq : generator.target = target) :
    TraceCorQHom.ambient
      (TraceCorQHom.singleton
        source
        target
        coefficient
        generator
        source_eq
        target_eq) =
      TraceCorQQuotient.singleton coefficient generator :=
  TraceCorQHom.ambient_singleton
    source
    target
    coefficient
    generator
    source_eq
    target_eq

/-- The top root exposes reflection of typed hom equality from ambient equality. -/
theorem AnalyticMotivesRoot.traceCorQHom_eq_of_ambient_eq
    {source target : TraceCorQObject}
    {left right : TraceCorQHom source target}
    (ambient_eq :
      TraceCorQHom.ambient left =
        TraceCorQHom.ambient right) :
    left = right :=
  TraceCorQHom.eq_of_ambient_eq
    ambient_eq

end AnalyticMotives
end LFunctions
end Boundary
