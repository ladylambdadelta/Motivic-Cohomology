import TraceCalc.ClassicalPeriods.Basic
import TraceCalc.LayerD.ConcretePeriodFaithfulness

universe u v

namespace TraceCalc
namespace LayerD

/-- Proof-carrying package for Task 22 once the internal realization functor target
is discharged. This keeps the theorem statement separate from any eventual witness. -/
structure InternalRealizationFunctorData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : InternalRealizationFunctorTarget ctx) where
  functorExists_holds : target.functorExists
  comparisonCompatibility_holds : target.comparisonCompatibility
  faithful_holds : target.faithful

namespace InternalRealizationFunctorData

def toTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalRealizationFunctorTarget ctx}
    (_ : InternalRealizationFunctorData ctx target) : InternalRealizationFunctorTarget ctx :=
  target

theorem target_eq
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalRealizationFunctorTarget ctx}
    (data : InternalRealizationFunctorData ctx target) :
    data.toTarget = target := rfl

/-- Task 22 is the first concrete upstream feed for the structured-realization bridge:
the two realization-functor obligations come from the internal functor target, and the
bridge's faithfulness slot reuses the same faithful-on-morphisms payload. -/
def toStructuredRealizationPackage
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalRealizationFunctorTarget ctx}
    (data : InternalRealizationFunctorData ctx target) : StructuredRealizationPackage where
  realizationFunctorsPiZero := target.functorExists
  realizationFunctorsPiZero_holds := data.functorExists_holds
  realizationFunctorsInfinity := target.comparisonCompatibility
  realizationFunctorsInfinity_holds := data.comparisonCompatibility_holds
  structuredRealizationConsequence := target.faithful
  structuredRealizationConsequence_holds := data.faithful_holds

theorem structuredRealizationPackage_fields
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalRealizationFunctorTarget ctx}
    (data : InternalRealizationFunctorData ctx target) :
    data.toStructuredRealizationPackage.realizationFunctorsPiZero = target.functorExists ∧
      data.toStructuredRealizationPackage.realizationFunctorsInfinity =
        target.comparisonCompatibility ∧
      data.toStructuredRealizationPackage.structuredRealizationConsequence =
        target.faithful := by
  exact ⟨rfl, rfl, rfl⟩

end InternalRealizationFunctorData

/-- First concrete provider surface for the object-level Betti/de Rham realization agreement
obligations. This records only the target formulas, not any comparison-isomorphism or period
matrix consequences. -/
structure BettiDeRhamAgreementTarget
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}) where
  realizationFunctorExists : Prop
  comparisonCompatibility : Prop
  bettiAgreement : Prop
  deRhamAgreement : Prop

namespace BettiDeRhamAgreementTarget

/-- Betti/de Rham agreement data feeds the Task 22 target only through the realization-existence
and comparison-compatibility slots; any faithfulness payload must still come from elsewhere. -/
def toInternalRealizationFunctorTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    (target : BettiDeRhamAgreementTarget ctx)
    (faithful : Prop) : InternalRealizationFunctorTarget ctx where
  functorExists := target.realizationFunctorExists
  comparisonCompatibility := target.comparisonCompatibility
  faithful := faithful

end BettiDeRhamAgreementTarget

/-- Proof-carrying provider package for the first concrete Betti/de Rham agreement surface. -/
structure BettiDeRhamAgreementData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : BettiDeRhamAgreementTarget ctx) where
  realizationFunctorExists_holds : target.realizationFunctorExists
  comparisonCompatibility_holds : target.comparisonCompatibility
  bettiAgreement_holds : target.bettiAgreement
  deRhamAgreement_holds : target.deRhamAgreement

namespace BettiDeRhamAgreementData

def toTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : BettiDeRhamAgreementTarget ctx}
    (_ : BettiDeRhamAgreementData ctx target) : BettiDeRhamAgreementTarget ctx :=
  target

theorem target_eq
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : BettiDeRhamAgreementTarget ctx}
    (data : BettiDeRhamAgreementData ctx target) :
    data.toTarget = target := rfl

/-- Build the Task 22 proof-carrying wrapper from the first Betti/de Rham agreement surface.
The agreement data supplies the realization-existence and comparison-compatibility slots; the
faithfulness slot is still an explicit external input rather than something derived here. -/
def toInternalRealizationFunctorData
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : BettiDeRhamAgreementTarget ctx}
    (data : BettiDeRhamAgreementData ctx target)
    (faithful : Prop)
    (faithful_holds : faithful) :
    InternalRealizationFunctorData ctx (target.toInternalRealizationFunctorTarget faithful) where
  functorExists_holds := data.realizationFunctorExists_holds
  comparisonCompatibility_holds := data.comparisonCompatibility_holds
  faithful_holds := faithful_holds

end BettiDeRhamAgreementData

namespace InternalRealizationFunctorData

/-- Constructor from the first Betti/de Rham provider surface into the Task 22 data wrapper.
This does not derive faithfulness from Betti/de Rham agreement; it only packages an already
supplied faithfulness proof alongside the provider-side realization inputs. -/
def ofBettiDeRhamAgreement
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : BettiDeRhamAgreementTarget ctx}
    (agreementData : BettiDeRhamAgreementData ctx target)
    (faithful : Prop)
    (faithful_holds : faithful) :
    InternalRealizationFunctorData ctx (target.toInternalRealizationFunctorTarget faithful) :=
  agreementData.toInternalRealizationFunctorData faithful faithful_holds

end InternalRealizationFunctorData

/-- Proof-carrying package for Task 23 once the internal period-faithfulness construction
target is discharged. -/
structure InternalPFConstructionData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : InternalPFConstructionTarget ctx) where
  periodFaithful_holds : target.periodFaithful
  unconditional_holds : target.unconditional

namespace InternalPFConstructionData

def toTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalPFConstructionTarget ctx}
    (_ : InternalPFConstructionData ctx target) : InternalPFConstructionTarget ctx :=
  target

theorem target_eq
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalPFConstructionTarget ctx}
    (data : InternalPFConstructionData ctx target) :
    data.toTarget = target := rfl

end InternalPFConstructionData

/-- Proof-carrying package for Task 24 once the internal evaluation-faithfulness target
is discharged. -/
structure InternalEvaluationFaithfulnessData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : InternalEvaluationFaithfulnessTarget ctx) where
  evaluationFaithful_holds : target.evaluationFaithful
  natural_holds : target.natural

namespace InternalEvaluationFaithfulnessData

def toTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalEvaluationFaithfulnessTarget ctx}
    (_ : InternalEvaluationFaithfulnessData ctx target) :
    InternalEvaluationFaithfulnessTarget ctx :=
  target

theorem target_eq
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : InternalEvaluationFaithfulnessTarget ctx}
    (data : InternalEvaluationFaithfulnessData ctx target) :
    data.toTarget = target := rfl

end InternalEvaluationFaithfulnessData

/-- Proof-carrying package for the remaining open witness on Task 25.
The theorem statement itself is already stored as data in
`ClassicalCoarsePeriodConsequenceTarget.periodConsequence`; the only extra witness
to carry separately is the prerequisite-discharge claim. -/
structure ClassicalCoarsePeriodConsequenceWitness
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : ClassicalCoarsePeriodConsequenceTarget ctx) where
  prerequisitesDischargedTarget_holds : target.prerequisitesDischargedTarget

namespace ClassicalCoarsePeriodConsequenceWitness

def toTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : ClassicalCoarsePeriodConsequenceTarget ctx}
    (_ : ClassicalCoarsePeriodConsequenceWitness ctx target) :
    ClassicalCoarsePeriodConsequenceTarget ctx :=
  target

theorem target_eq
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {target : ClassicalCoarsePeriodConsequenceTarget ctx}
    (data : ClassicalCoarsePeriodConsequenceWitness ctx target) :
    data.toTarget = target := rfl

end ClassicalCoarsePeriodConsequenceWitness

/-- Honest stage-level package for the currently open period-faithfulness declarations.
It records the four theorem targets without asserting that any of them are solved. -/
structure PeriodFaithfulnessStagePackage
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}) where
  internalRealizationFunctor : InternalRealizationFunctorTarget ctx
  internalPFConstruction : InternalPFConstructionTarget ctx
  internalEvaluationFaithfulness : InternalEvaluationFaithfulnessTarget ctx
  classicalCoarsePeriodConsequence : ClassicalCoarsePeriodConsequenceTarget ctx

/-- Proof-carrying refinement of `PeriodFaithfulnessStagePackage`. This is the honest
target/data split for the remaining period-faithfulness milestones. -/
structure PeriodFaithfulnessStageData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (pkg : PeriodFaithfulnessStagePackage ctx) where
  internalRealizationFunctorData :
    InternalRealizationFunctorData ctx pkg.internalRealizationFunctor
  internalPFConstructionData :
    InternalPFConstructionData ctx pkg.internalPFConstruction
  internalEvaluationFaithfulnessData :
    InternalEvaluationFaithfulnessData ctx pkg.internalEvaluationFaithfulness
  classicalCoarsePeriodConsequenceData :
    ClassicalCoarsePeriodConsequenceWitness ctx pkg.classicalCoarsePeriodConsequence

namespace PeriodFaithfulnessStageData

def toPackage
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {pkg : PeriodFaithfulnessStagePackage ctx}
    (_ : PeriodFaithfulnessStageData ctx pkg) : PeriodFaithfulnessStagePackage ctx :=
  pkg

theorem package_eq
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    {pkg : PeriodFaithfulnessStagePackage ctx}
    (data : PeriodFaithfulnessStageData ctx pkg) :
    data.toPackage = pkg := rfl

end PeriodFaithfulnessStageData

end LayerD
end TraceCalc