import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Classes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Owner

/-!
# Composition of typed hom representatives and classes

This file descends typed formal-sum composition to typed hom quotients.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compose typed hom representatives by composing formal sums and appending ledgers. -/
def TraceCorQHomRepresentative.comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceCorQHomRepresentative source target :=
  TraceCorQHomRepresentative.ofFormalSumLedger
    (TraceCorQHomFormalSum.comp left.formalSum right.formalSum)
    (TraceCorQRelationLedger.append left.ledger right.ledger)

/-- The raw candidate of representative composition has raw formal composition. -/
theorem TraceCorQHomRepresentative.comp_rawCandidate_formalSum
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).rawCandidate.formalSum =
      TraceCorQFormalSum.comp
        left.rawCandidate.formalSum
        right.rawCandidate.formalSum :=
  TraceCorQHomFormalSum.comp_raw left.formalSum right.formalSum

/-- The raw candidate of representative composition has appended ledger. -/
theorem TraceCorQHomRepresentative.comp_rawCandidate_ledger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).rawCandidate.ledger =
      TraceCorQRelationLedger.append
        left.rawCandidate.ledger
        right.rawCandidate.ledger :=
  rfl

/-- Representative composition records composed formal and relation certificates. -/
theorem TraceCorQHomRepresentative.comp_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum.raw right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQQuotientCandidate.comp_certificateLedger
    left.rawCandidate
    right.rawCandidate

/-- Representative composition is compatible with the typed hom relation. -/
def TraceCorQHomRelation.compCongr
    {source middle target : TraceCorQObject}
    {left₁ left₂ : TraceCorQHomRepresentative source middle}
    {right₁ right₂ : TraceCorQHomRepresentative middle target}
    (leftRelation : TraceCorQHomRelation left₁ left₂)
    (rightRelation : TraceCorQHomRelation right₁ right₂) :
    TraceCorQHomRelation
      (TraceCorQHomRepresentative.comp left₁ right₁)
      (TraceCorQHomRepresentative.comp left₂ right₂) :=
  TraceCorQQuotientRelation.trans
    (TraceCorQQuotientRelation.sameFormalSum
      (TraceCorQRelationLedger.append
        left₁.rawCandidate.ledger
        right₁.rawCandidate.ledger)
      (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
        left₁
        right₁))
    (TraceCorQQuotientRelation.trans
      (TraceCorQQuotientRelation.compCongr
        leftRelation
        rightRelation)
      (TraceCorQQuotientRelation.symm
        (TraceCorQQuotientRelation.sameFormalSum
          (TraceCorQRelationLedger.append
            left₂.rawCandidate.ledger
            right₂.rawCandidate.ledger)
          (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
            left₂
            right₂))))

/-- Composition of typed hom classes. -/
def TraceCorQHom.comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom source target :=
  Quotient.liftOn₂
    left
    right
    (fun leftRepresentative rightRepresentative =>
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp
          leftRepresentative
          rightRepresentative))
    (fun left₁ right₁ left₂ right₂ leftRelation rightRelation =>
      TraceCorQHom.sound
        (TraceCorQHomRelation.compCongr
          leftRelation
          rightRelation))

/-- Typed hom composition agrees with representative composition. -/
theorem TraceCorQHom.comp_ofRepresentative
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.ofRepresentative left)
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.comp left right) :=
  rfl

/-- The ambient map sends typed hom composition to ambient quotient composition. -/
theorem TraceCorQHom.ambient_comp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right : TraceCorQHom middle target) :
    TraceCorQHom.ambient
      (TraceCorQHom.comp left right) =
      TraceCorQQuotient.comp
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  Quotient.inductionOn₂
    left
    right
    (fun leftRepresentative rightRepresentative =>
      Eq.trans
        (TraceCorQHom.ambient_ofRepresentative
          (TraceCorQHomRepresentative.comp
            leftRepresentative
            rightRepresentative))
        (Eq.trans
          (TraceCorQQuotient.sound_sameFormalSum
            (TraceCorQRelationLedger.append
              leftRepresentative.rawCandidate.ledger
              rightRepresentative.rawCandidate.ledger)
            (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
              leftRepresentative
              rightRepresentative))
          (Eq.symm
            (TraceCorQQuotient.comp_ofCandidate
              leftRepresentative.rawCandidate
              rightRepresentative.rawCandidate))))

end AnalyticMotives
end LFunctions
end Boundary
