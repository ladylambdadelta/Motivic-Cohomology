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
  functorExists_holds : target.functorExistsStatement
  comparisonCompatibility_holds : target.comparisonCompatibilityStatement
  faithful_holds : target.structuredRealizationConsequenceStatement

namespace InternalRealizationFunctorData

/-- Canonical proof-carrying package extracted from the exact Task 22 target. -/
def ofTarget
    {ctx : ClassicalPeriods.ClassicalComparisonContext.{u, v}}
    (target : InternalRealizationFunctorTarget ctx) :
    InternalRealizationFunctorData ctx target where
  functorExists_holds := target.functorExistsStatement_holds
  comparisonCompatibility_holds := target.comparisonCompatibilityStatement_holds
  faithful_holds := target.structuredRealizationConsequenceStatement_holds

end InternalRealizationFunctorData

end LayerD
end TraceCalc