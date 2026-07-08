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
  Eq.trans
    (TraceCorQHomRepresentative.ofFormalSumLedger_certificateLedger
      (TraceCorQHomFormalSum.comp left.formalSum right.formalSum)
      (TraceCorQRelationLedger.append left.ledger right.ledger))
    (congrArg₂
      ResidueChannelCertificateLedger.append
      (TraceCorQHomFormalSum.comp_certificateLedger
        left.formalSum
        right.formalSum)
      (TraceCorQRelationLedger.append_certificateLedger
        left.ledger
        right.ledger))

/-- Representative composition records composed formal and relation imported payload. -/
theorem TraceCorQHomRepresentative.comp_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangleCount
        (TraceCorQHomRepresentative.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).importedRectangleCount +
          count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Representative composition records composed formal and relation imported rectangles. -/
theorem TraceCorQHomRepresentative.comp_importedRectangles
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangles
        (TraceCorQHomRepresentative.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_importedRectangles
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun rectangles =>
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).importedRectangles ++
          rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Representative composition records composed formal and relation bookkeeping payload. -/
theorem TraceCorQHomRepresentative.comp_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.traceBookkeepingCount
        (TraceCorQHomRepresentative.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).traceBookkeepingCount +
          count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

/-- Representative composition records composed formal and relation rewrite-step payload. -/
theorem TraceCorQHomRepresentative.comp_rewriteStepCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRepresentative.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum.raw
        right.formalSum.raw).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.rewriteStepCount
        (TraceCorQHomRepresentative.comp_certificateLedger left right))
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger)))
    (congrArg
      (fun count =>
        (TraceCorQFormalSum.comp
          left.formalSum.raw
          right.formalSum.raw).rewriteStepCount +
          count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        left.ledger.certificateLedger
        right.ledger.certificateLedger))

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
      (Eq.trans
        (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
          left₁
          right₁)
        (Eq.symm
          (TraceCorQQuotientCandidate.comp_formalSum
            left₁.rawCandidate
            right₁.rawCandidate))))
    (TraceCorQQuotientRelation.trans
      (TraceCorQQuotientRelation.compCongr
        leftRelation
        rightRelation)
        (TraceCorQQuotientRelation.symm
        (TraceCorQQuotientRelation.sameFormalSum
          (TraceCorQRelationLedger.append
            left₂.rawCandidate.ledger
            right₂.rawCandidate.ledger)
          (Eq.trans
            (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
              left₂
              right₂)
            (Eq.symm
              (TraceCorQQuotientCandidate.comp_formalSum
                left₂.rawCandidate
                right₂.rawCandidate))))))

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
            (Eq.trans
              (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
                leftRepresentative
                rightRepresentative)
              (Eq.symm
                (TraceCorQQuotientCandidate.comp_formalSum
                  leftRepresentative.rawCandidate
                  rightRepresentative.rawCandidate))))
          (Eq.symm
            (TraceCorQQuotient.comp_ofCandidate
              leftRepresentative.rawCandidate
              rightRepresentative.rawCandidate))))

end AnalyticMotives
end LFunctions
end Boundary
