import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.ContourCorQConstruction.IdempotentCompletion.Owner

/-!
# Constructed compact geometric analytic motives

This owner packages the constructed thick closure and idempotent completion as
the compact geometric layer of the constructed analytic motive lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A compact geometric analytic motive in the constructed lane. -/
structure ConstructedCompactGeometricAnalyticMotive where
  thickClosure : ConstructedCompactAnalyticThickClosure
  idempotentCompletion : ConstructedCompactAnalyticIdempotentCompletion

namespace ConstructedCompactGeometricAnalyticMotive

/-- The constructed thick-closure component. -/
def thick (M : ConstructedCompactGeometricAnalyticMotive) :
    ConstructedCompactAnalyticThickClosure :=
  M.thickClosure

/-- The constructed idempotent-completion component. -/
def idempotent (M : ConstructedCompactGeometricAnalyticMotive) :
    ConstructedCompactAnalyticIdempotentCompletion :=
  M.idempotentCompletion

/-- The closed object of the constructed thick closure. -/
def closedObject (M : ConstructedCompactGeometricAnalyticMotive) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  M.thickClosure.closedObject

/-- The retract object selected by idempotent completion. -/
def retractObject (M : ConstructedCompactGeometricAnalyticMotive) :
    ConstructedTateStabilizedAnalyticPresheaf :=
  M.idempotentCompletion.retractObject

/-- A selected constructed compact generator. -/
def generatorAt (M : ConstructedCompactGeometricAnalyticMotive)
    (i : M.thickClosure.GeneratorIndex) :
    ConstructedCompactAnalyticGenerator :=
  M.thickClosure.generatorAt i

/-- The source bulk of a selected constructed compact generator. -/
def generatorSource (M : ConstructedCompactGeometricAnalyticMotive)
    (i : M.thickClosure.GeneratorIndex) :
    ContourAdmissibleBulk :=
  M.thickClosure.generatorSource i

end ConstructedCompactGeometricAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
