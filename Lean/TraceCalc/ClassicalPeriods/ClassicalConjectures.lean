import TraceCalc.ClassicalPeriods.PeriodConjectureTarget

universe u v w

namespace TraceCalc
namespace ClassicalPeriods
namespace ClassicalConjectures

/-- Locked scalar Grothendieck period conjecture attached to a concrete classical target. -/
def GrothendieckPeriodConjecture
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.MotiveCategory} (f g : X ⟶ Y),
    target.scalarShadow.equalityRelation
      (target.scalarShadowOf f)
      (target.scalarShadowOf g) →
    f = g

/-- Locked framed Grothendieck period conjecture attached to a concrete classical framed target. -/
def GrothendieckFramedPeriodConjecture
    (target : FramedPeriodConjectureTarget.{u, v, w}) : Prop :=
  ∀ {X Y : target.baseTarget.MotiveCategory} (f g : X ⟶ Y),
    target.framedPeriodShadow.equalityRelation
      (target.framedShadowOf f)
      (target.framedShadowOf g) →
    f = g

/-- The packaged scalar target statement is definitionally the locked scalar conjecture. -/
theorem scalar_target_statement_iff_locked_grothendieck_period_conjecture
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    ClassicalGrothendieckPeriodFaithfulnessStatement target ↔
      GrothendieckPeriodConjecture target := by
  rfl

/-- The packaged framed target statement is definitionally the locked framed conjecture. -/
theorem framed_target_statement_iff_locked_grothendieck_framed_period_conjecture
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    ClassicalFramedPeriodConjectureStatement target ↔
      GrothendieckFramedPeriodConjecture target := by
  rfl

/-- Locked scalar conjecture from the existing classical target package. -/
theorem grothendieck_period_conjecture
    (target : ClassicalGrothendieckPeriodFaithfulnessTarget.{u, v, w}) :
    GrothendieckPeriodConjecture target := by
  exact ClassicalGrothendieckPeriodFaithfulnessTarget.faithfulnessStatement_of_reflection target

/-- Locked framed conjecture from the existing classical framed target package. -/
theorem grothendieck_framed_period_conjecture
    (target : FramedPeriodConjectureTarget.{u, v, w}) :
    GrothendieckFramedPeriodConjecture target := by
  exact FramedPeriodConjectureTarget.faithfulnessStatement_of_reflection target

end ClassicalConjectures
end ClassicalPeriods
end TraceCalc