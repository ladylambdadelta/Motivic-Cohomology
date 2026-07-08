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

/-- Representative addition records summed formal and relation certificates. -/
theorem TraceCorQHomRepresentative.add_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  Eq.trans
    (TraceCorQHomRepresentative.ofFormalSumLedger_certificateLedger
      (TraceCorQHomFormalSum.add left.formalSum right.formalSum)
      (TraceCorQRelationLedger.append left.ledger right.ledger))
    (Eq.trans
      (congrArg₂
        ResidueChannelCertificateLedger.append
        (TraceCorQHomFormalSum.add_certificateLedger
          left.formalSum
          right.formalSum)
        (TraceCorQRelationLedger.append_certificateLedger
          left.ledger
          right.ledger))
      rfl)

/-- Representative addition records formal and relation imported payload. -/
theorem TraceCorQHomRepresentative.add_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).importedRectangleCount =
      (left.formalSum.importedRectangleCount +
        right.formalSum.importedRectangleCount) +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangleCount
        (TraceCorQHomRepresentative.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Representative addition records formal and relation imported rectangles. -/
theorem TraceCorQHomRepresentative.add_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).importedRectangles =
      (left.formalSum.importedRectangles ++
        right.formalSum.importedRectangles) ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangles
        (TraceCorQHomRepresentative.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangles
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      List.append
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Representative addition records formal and relation bookkeeping payload. -/
theorem TraceCorQHomRepresentative.add_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).traceBookkeepingCount =
      (left.formalSum.traceBookkeepingCount +
        right.formalSum.traceBookkeepingCount) +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.traceBookkeepingCount
        (TraceCorQHomRepresentative.add_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.formalSum.certificateLedger
        right.formalSum.certificateLedger)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

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
      (Eq.trans
        (TraceCorQHomRepresentative.add_rawCandidate_formalSum
          left₁
          right₁)
        (Eq.symm
          (TraceCorQQuotientCandidate.add_formalSum
            left₁.rawCandidate
            right₁.rawCandidate))))
    (TraceCorQQuotientRelation.trans
      (TraceCorQQuotientRelation.addCongr
        leftRelation
        rightRelation)
        (TraceCorQQuotientRelation.symm
        (TraceCorQQuotientRelation.sameFormalSum
          (TraceCorQRelationLedger.append
            left₂.rawCandidate.ledger
            right₂.rawCandidate.ledger)
          (Eq.trans
            (TraceCorQHomRepresentative.add_rawCandidate_formalSum
              left₂
              right₂)
            (Eq.symm
              (TraceCorQQuotientCandidate.add_formalSum
                left₂.rawCandidate
                right₂.rawCandidate))))))

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
            (Eq.trans
              (TraceCorQHomRepresentative.add_rawCandidate_formalSum
                leftRepresentative
                rightRepresentative)
              (Eq.symm
                (TraceCorQQuotientCandidate.add_formalSum
                  leftRepresentative.rawCandidate
                  rightRepresentative.rawCandidate))))
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
