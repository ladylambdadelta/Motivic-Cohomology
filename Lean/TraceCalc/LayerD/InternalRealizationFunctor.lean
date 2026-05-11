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

end InternalRealizationFunctorData

/-- Proof-carrying package for Task 23 once the internal period-faithfulness construction
target is discharged. -/
structure InternalPFConstructionData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : InternalPFConstructionTarget ctx) where
  periodFaithful_holds : target.periodFaithful
  unconditional_holds : target.unconditional

namespace InternalPFConstructionData

end InternalPFConstructionData

/-- Proof-carrying package for Task 24 once the internal evaluation-faithfulness target
is discharged. -/
structure InternalEvaluationFaithfulnessData
    (ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v})
    (target : InternalEvaluationFaithfulnessTarget ctx) where
  evaluationFaithful_holds : target.evaluationFaithful
  natural_holds : target.natural

namespace InternalEvaluationFaithfulnessData

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

end PeriodFaithfulnessStageData

end LayerD
end TraceCalc