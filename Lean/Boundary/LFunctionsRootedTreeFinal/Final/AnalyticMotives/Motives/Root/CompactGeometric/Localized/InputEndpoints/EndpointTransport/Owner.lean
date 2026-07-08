import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.EndpointTransport.Owner

/-!
# Motive-root endpoint equality transport for input compact generators

This file exposes concrete endpoint-equality transport for localization-input
compact generators through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: equal source objects give equal source compact generators. -/
theorem TraceAnalyticMotive.sourceGenerator_eq_sourceGenerator_of_sourceObject_eq
    (left right : TraceLocalizationInput)
    (source_eq : left.sourceObject = right.sourceObject) :
    left.sourceGenerator =
      right.sourceGenerator :=
  TraceLocalizationInput.sourceGenerator_eq_sourceGenerator_of_sourceObject_eq
    left
    right
    source_eq

/-- Motive-root wrapper: equal target objects give equal target compact generators. -/
theorem TraceAnalyticMotive.targetGenerator_eq_targetGenerator_of_targetObject_eq
    (left right : TraceLocalizationInput)
    (target_eq : left.targetObject = right.targetObject) :
    left.targetGenerator =
      right.targetGenerator :=
  TraceLocalizationInput.targetGenerator_eq_targetGenerator_of_targetObject_eq
    left
    right
    target_eq

/-- Motive-root wrapper: a left target equal to a right source identifies compact endpoints. -/
theorem TraceAnalyticMotive.targetGenerator_eq_sourceGenerator_of_targetObject_eq_sourceObject
    (left right : TraceLocalizationInput)
    (endpoint_eq : left.targetObject = right.sourceObject) :
    left.targetGenerator =
      right.sourceGenerator :=
  TraceLocalizationInput.targetGenerator_eq_sourceGenerator_of_targetObject_eq_sourceObject
    left
    right
    endpoint_eq

/-- Motive-root wrapper: a left source equal to a right target identifies compact endpoints. -/
theorem TraceAnalyticMotive.sourceGenerator_eq_targetGenerator_of_sourceObject_eq_targetObject
    (left right : TraceLocalizationInput)
    (endpoint_eq : left.sourceObject = right.targetObject) :
    left.sourceGenerator =
      right.targetGenerator :=
  TraceLocalizationInput.sourceGenerator_eq_targetGenerator_of_sourceObject_eq_targetObject
    left
    right
    endpoint_eq

/-- Motive-root wrapper: a right source equal to a left target identifies compact endpoints. -/
theorem TraceAnalyticMotive.targetGenerator_eq_sourceGenerator_of_sourceObject_eq_targetObject_symm
    (left right : TraceLocalizationInput)
    (endpoint_eq : right.sourceObject = left.targetObject) :
    left.targetGenerator =
      right.sourceGenerator :=
  TraceLocalizationInput.targetGenerator_eq_sourceGenerator_of_sourceObject_eq_targetObject_symm
    left
    right
    endpoint_eq

/-- Motive-root wrapper: a right target equal to a left source identifies compact endpoints. -/
theorem TraceAnalyticMotive.sourceGenerator_eq_targetGenerator_of_targetObject_eq_sourceObject_symm
    (left right : TraceLocalizationInput)
    (endpoint_eq : right.targetObject = left.sourceObject) :
    left.sourceGenerator =
      right.targetGenerator :=
  TraceLocalizationInput.sourceGenerator_eq_targetGenerator_of_targetObject_eq_sourceObject_symm
    left
    right
    endpoint_eq

end AnalyticMotives
end LFunctions
end Boundary
