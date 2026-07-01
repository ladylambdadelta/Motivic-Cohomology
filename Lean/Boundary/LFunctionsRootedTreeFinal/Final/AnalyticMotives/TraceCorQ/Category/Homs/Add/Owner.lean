import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner

/-!
# Addition of typed trace-correspondence hom classes

This file owns addition in each typed hom quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Add typed hom representatives by adding their formal sums and ledgers. -/
def TraceCorQHomRepresentative.add
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    TraceCorQHomRepresentative source target :=
  TraceCorQHomRepresentative.ofFormalSumLedger
    (TraceCorQHomFormalSum.add left.formalSum right.formalSum)
    (TraceCorQRelationLedger.append left.ledger right.ledger)

/-- The raw candidate of representative addition has concatenated raw formal sum. -/
theorem TraceCorQHomRepresentative.add_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).rawCandidate.formalSum =
      TraceCorQFormalSum.add
        left.rawCandidate.formalSum
        right.rawCandidate.formalSum :=
  TraceCorQHomFormalSum.add_raw left.formalSum right.formalSum

/-- The raw candidate of representative addition has appended ledger. -/
theorem TraceCorQHomRepresentative.add_rawCandidate_ledger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).rawCandidate.ledger =
      TraceCorQRelationLedger.append
        left.rawCandidate.ledger
        right.rawCandidate.ledger :=
  rfl

/-- Representative addition is compatible with the typed hom relation. -/
def TraceCorQHomRelation.addCongr
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftRelation : TraceCorQHomRelation left₁ left₂)
    (rightRelation : TraceCorQHomRelation right₁ right₂) :
    TraceCorQHomRelation
      (TraceCorQHomRepresentative.add left₁ right₁)
      (TraceCorQHomRepresentative.add left₂ right₂) :=
  TraceCorQQuotientRelation.trans
    (TraceCorQQuotientRelation.sameFormalSum
      (TraceCorQRelationLedger.append
        left₁.rawCandidate.ledger
        right₁.rawCandidate.ledger)
      (TraceCorQHomRepresentative.add_rawCandidate_formalSum
        left₁
        right₁))
    (TraceCorQQuotientRelation.trans
      (TraceCorQQuotientRelation.addCongr
        leftRelation
        rightRelation)
      (TraceCorQQuotientRelation.symm
        (TraceCorQQuotientRelation.sameFormalSum
          (TraceCorQRelationLedger.append
            left₂.rawCandidate.ledger
            right₂.rawCandidate.ledger)
          (TraceCorQHomRepresentative.add_rawCandidate_formalSum
            left₂
            right₂))))

/-- Addition of typed hom classes. -/
def TraceCorQHom.add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom source target :=
  Quotient.liftOn₂
    left
    right
    (fun leftRepresentative rightRepresentative =>
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.add
          leftRepresentative
          rightRepresentative))
    (fun left₁ right₁ left₂ right₂ leftRelation rightRelation =>
      TraceCorQHom.sound
        (TraceCorQHomRelation.addCongr
          leftRelation
          rightRelation))

/-- Typed hom addition agrees with representative addition. -/
theorem TraceCorQHom.add_ofRepresentative
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    TraceCorQHom.add
      (TraceCorQHom.ofRepresentative left)
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.add left right) :=
  rfl

/-- The ambient map sends typed hom addition to ambient quotient addition. -/
theorem TraceCorQHom.ambient_add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.add left right) =
      TraceCorQQuotient.add
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  Quotient.inductionOn₂
    left
    right
    (fun leftRepresentative rightRepresentative =>
      Eq.trans
        (TraceCorQHom.ambient_ofRepresentative
          (TraceCorQHomRepresentative.add
            leftRepresentative
            rightRepresentative))
        (Eq.trans
          (TraceCorQQuotient.sound_sameFormalSum
            (TraceCorQRelationLedger.append
              leftRepresentative.rawCandidate.ledger
              rightRepresentative.rawCandidate.ledger)
            (TraceCorQHomRepresentative.add_rawCandidate_formalSum
              leftRepresentative
              rightRepresentative))
          (Eq.symm
            (TraceCorQQuotient.add_ofCandidate
              leftRepresentative.rawCandidate
              rightRepresentative.rawCandidate))))

/-- A cons typed formal sum is the sum of its singleton head and formal-sum tail. -/
theorem TraceCorQHom.ofFormalSum_cons
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target)
    (tail : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ofFormalSum (term :: tail) =
      TraceCorQHom.add
        (TraceCorQHom.singleton
          source
          target
          term.coefficient
          term.generator
          (TraceCorQHomTerm.generator_source term)
          (TraceCorQHomTerm.generator_target term))
        (TraceCorQHom.ofFormalSum tail) :=
  Eq.symm
    (Eq.trans
      (TraceCorQHom.add_ofRepresentative
        (TraceCorQHomRepresentative.ofFormalSumLedger
          (TraceCorQHomFormalSum.singleton
            source
            target
            term.coefficient
            term.generator
            (TraceCorQHomTerm.generator_source term)
            (TraceCorQHomTerm.generator_target term))
          TraceCorQRelationLedger.empty)
        (TraceCorQHomRepresentative.ofFormalSumLedger
          tail
          TraceCorQRelationLedger.empty))
      (TraceCorQHom.sound
        (TraceCorQQuotientRelation.sameFormalSum
          TraceCorQRelationLedger.empty
          rfl)))

end AnalyticMotives
end LFunctions
end Boundary
