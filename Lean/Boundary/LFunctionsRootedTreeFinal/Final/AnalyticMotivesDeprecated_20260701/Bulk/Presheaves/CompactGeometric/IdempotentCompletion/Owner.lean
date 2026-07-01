import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.ThickClosure.Owner

/-!
# Idempotent completion of compact analytic motives

This file owns the idempotent-complete compact geometric analytic-motive
subcategory.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Idempotent-completion data for compact geometric analytic motives.  It records
an object in the thick closure together with a chosen retract object.  The
splitting morphisms belong to the stable morphism layer after that layer is
constructed.
-/
structure CompactAnalyticIdempotentCompletion where
  thickObject : CompactAnalyticThickClosure
  retractObject : TateStabilizedAnalyticPresheaf

namespace CompactAnalyticIdempotentCompletion

/-- The thick object from which an idempotent-complete object is split. -/
def thickClosure (E : CompactAnalyticIdempotentCompletion) :
    CompactAnalyticThickClosure :=
  E.thickObject

/-- The retract object selected by idempotent-completion data. -/
def retract (E : CompactAnalyticIdempotentCompletion) :
    TateStabilizedAnalyticPresheaf :=
  E.retractObject

/-- The closed object of the thick closure used by idempotent-completion data. -/
def closedObject (E : CompactAnalyticIdempotentCompletion) :
    TateStabilizedAnalyticPresheaf :=
  E.thickObject.closedObject

/-- A selected compact generator of the thick object used by idempotent completion. -/
def generatorAt (E : CompactAnalyticIdempotentCompletion)
    (i : E.thickObject.GeneratorIndex) :
    CompactAnalyticGenerator :=
  E.thickObject.generatorAt i

/-- The source bulk of a selected generator in the thick object. -/
def generatorSource (E : CompactAnalyticIdempotentCompletion)
    (i : E.thickObject.GeneratorIndex) :
    ContourAdmissibleBulk :=
  E.thickObject.generatorSource i

/-- The analytic Tate object selected by the retract object. -/
def retractTate (E : CompactAnalyticIdempotentCompletion) :
    AnalyticTateObject :=
  E.retractObject.tateObject

end CompactAnalyticIdempotentCompletion

end AnalyticMotives
end LFunctions
end Boundary
