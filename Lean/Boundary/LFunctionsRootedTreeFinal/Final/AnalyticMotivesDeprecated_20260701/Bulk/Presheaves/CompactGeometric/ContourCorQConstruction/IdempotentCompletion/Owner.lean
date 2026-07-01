import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.ContourCorQConstruction.ThickClosure.Owner

/-!
# Constructed idempotent completion

This owner records idempotent-completion data over constructed thick closures.
The stable morphism splitting data belongs downstream from this object layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Idempotent-completion data for constructed compact analytic motives. -/
structure ConstructedCompactAnalyticIdempotentCompletion where
  thickObject : ConstructedCompactAnalyticThickClosure
  retractObject : ConstructedTateStabilizedAnalyticPresheaf

namespace ConstructedCompactAnalyticIdempotentCompletion

/-- The constructed thick object from which the retract is selected. -/
def thickClosure
    (E : ConstructedCompactAnalyticIdempotentCompletion) :
    ConstructedCompactAnalyticThickClosure :=
  E.thickObject

/-- The constructed retract object. -/
def retract
    (E : ConstructedCompactAnalyticIdempotentCompletion) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  E.retractObject

/-- The closed object of the thick closure. -/
def closedObject
    (E : ConstructedCompactAnalyticIdempotentCompletion) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  E.thickObject.closedObject

/-- A selected generator of the underlying thick object. -/
def generatorAt
    (E : ConstructedCompactAnalyticIdempotentCompletion)
    (i : E.thickObject.GeneratorIndex) :
    ConstructedCompactAnalyticGenerator :=
  E.thickObject.generatorAt i

/-- The source bulk of a selected generator. -/
def generatorSource
    (E : ConstructedCompactAnalyticIdempotentCompletion)
    (i : E.thickObject.GeneratorIndex) :
    ContourAdmissibleBulk :=
  E.thickObject.generatorSource i

/-- The retract level at one Tate weight. -/
def retractLevelAt
    (E : ConstructedCompactAnalyticIdempotentCompletion)
    (n : Int) :
    ConstructedIntervalLocalAnalyticPresheaf :=
  E.retractObject.levelAt n

end ConstructedCompactAnalyticIdempotentCompletion

end AnalyticMotives
end LFunctions
end Boundary
