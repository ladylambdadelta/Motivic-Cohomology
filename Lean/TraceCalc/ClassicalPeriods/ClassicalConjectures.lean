import TraceCalc.ClassicalPeriods.PeriodConjectureTarget

universe u v w

namespace TraceCalc
namespace ClassicalPeriods
namespace ClassicalConjectures

/-- Scaffold scalar period-faithfulness statement attached to a supplied target record.

This is not the unconditional classical Grothendieck period conjecture.  It is the theorem target
for one explicit target package, and should not be cited as a completed formalization of the
classical conjecture. -/
def TargetRecordScalarPeriodFaithfulness
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.scalarShadow.equalityRelation
      (target.scalarShadowOf f)
      (target.scalarShadowOf g) →
    f = g

/-- Scaffold framed period-faithfulness statement attached to a supplied target record.

This is not the unconditional classical framed Grothendieck period conjecture.  It is the theorem
target for one explicit framed target package. -/
def TargetRecordFramedPeriodFaithfulness
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g) →
    f = g

/-- The packaged scalar target statement is definitionally the scaffold target-record statement. -/
theorem scalar_target_statement_iff_target_record_scalar_period_faithfulness
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    ClassicalGrothendieckPeriodFaithfulnessStatement target ↔
      TargetRecordScalarPeriodFaithfulness target := by
  rfl

/-- The packaged framed target statement is definitionally the scaffold target-record statement. -/
theorem framed_target_statement_iff_target_record_framed_period_faithfulness
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    ClassicalFramedPeriodConjectureStatement target ↔
      TargetRecordFramedPeriodFaithfulness target := by
  rfl

/-- Target-record scalar period faithfulness from the existing scaffold package. -/
theorem target_record_scalar_period_faithfulness
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    TargetRecordScalarPeriodFaithfulness target := by
  exact ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement_of_reflection target

/-- Target-record framed period faithfulness from the existing scaffold package. -/
theorem target_record_framed_period_faithfulness
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    TargetRecordFramedPeriodFaithfulness target := by
  exact FramedPeriodConjectureTarget.faithfulnessStatement_of_reflection target

/-- Marker for the missing unconditional classical scalar Grothendieck period conjecture.

The repository currently contains scaffold target statements and bridge obligations, not a proof of
the classical conjecture itself. -/
def GrothendieckPeriodConjectureNotYetFormalized : Prop := False

/-- Marker for the missing unconditional classical framed Grothendieck period conjecture.

The repository currently contains scaffold target statements and bridge obligations, not a proof of
the classical framed conjecture itself. -/
def GrothendieckFramedPeriodConjectureNotYetFormalized : Prop := False

end ClassicalConjectures
end ClassicalPeriods
end TraceCalc