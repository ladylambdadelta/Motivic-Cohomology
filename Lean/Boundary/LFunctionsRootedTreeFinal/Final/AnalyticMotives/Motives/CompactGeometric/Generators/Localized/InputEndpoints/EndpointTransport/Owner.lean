import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.Owner

/-!
# Endpoint equality transport for localization-input compact generators

This file records the concrete endpoint equalities needed to compose compact
generator morphisms attached to separate localization inputs.  The equalities
come directly from the `ofTraceObject` definitions of source and target
generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Equal source objects give equal source compact generators. -/
theorem TraceLocalizationInput.sourceGenerator_eq_sourceGenerator_of_sourceObject_eq
    (left right : TraceLocalizationInput)
    (source_eq : left.sourceObject = right.sourceObject) :
    left.sourceGenerator =
      right.sourceGenerator :=
  congrArg
    TraceAnalyticGeometricGenerator.ofTraceObject
    source_eq

/-- Equal target objects give equal target compact generators. -/
theorem TraceLocalizationInput.targetGenerator_eq_targetGenerator_of_targetObject_eq
    (left right : TraceLocalizationInput)
    (target_eq : left.targetObject = right.targetObject) :
    left.targetGenerator =
      right.targetGenerator :=
  congrArg
    TraceAnalyticGeometricGenerator.ofTraceObject
    target_eq

/-- A left target object equal to a right source object identifies the compact endpoints. -/
theorem TraceLocalizationInput.targetGenerator_eq_sourceGenerator_of_targetObject_eq_sourceObject
    (left right : TraceLocalizationInput)
    (endpoint_eq : left.targetObject = right.sourceObject) :
    left.targetGenerator =
      right.sourceGenerator :=
  congrArg
    TraceAnalyticGeometricGenerator.ofTraceObject
    endpoint_eq

/-- A left source object equal to a right target object identifies the compact endpoints. -/
theorem TraceLocalizationInput.sourceGenerator_eq_targetGenerator_of_sourceObject_eq_targetObject
    (left right : TraceLocalizationInput)
    (endpoint_eq : left.sourceObject = right.targetObject) :
    left.sourceGenerator =
      right.targetGenerator :=
  congrArg
    TraceAnalyticGeometricGenerator.ofTraceObject
    endpoint_eq

/-- A right source object equal to a left target object identifies the compact endpoints. -/
theorem TraceLocalizationInput.targetGenerator_eq_sourceGenerator_of_sourceObject_eq_targetObject_symm
    (left right : TraceLocalizationInput)
    (endpoint_eq : right.sourceObject = left.targetObject) :
    left.targetGenerator =
      right.sourceGenerator :=
  TraceLocalizationInput.targetGenerator_eq_sourceGenerator_of_targetObject_eq_sourceObject
    left
    right
    (Eq.symm endpoint_eq)

/-- A right target object equal to a left source object identifies the compact endpoints. -/
theorem TraceLocalizationInput.sourceGenerator_eq_targetGenerator_of_targetObject_eq_sourceObject_symm
    (left right : TraceLocalizationInput)
    (endpoint_eq : right.targetObject = left.sourceObject) :
    left.sourceGenerator =
      right.targetGenerator :=
  TraceLocalizationInput.sourceGenerator_eq_targetGenerator_of_sourceObject_eq_targetObject
    left
    right
    (Eq.symm endpoint_eq)

end AnalyticMotives
end LFunctions
end Boundary
