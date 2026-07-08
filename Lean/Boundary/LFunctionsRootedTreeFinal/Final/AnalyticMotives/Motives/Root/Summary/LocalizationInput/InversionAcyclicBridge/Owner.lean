import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.InversionAcyclicBridge.Owner

/-!
# Motive-root summary for inversion-acyclic bridges

This file exposes the concrete bridge between unstable inversion and additive
mapping-cone acyclic generators through the motive-root summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: the inversion-acyclic bridge attached to a localization input. -/
def TraceAnalyticMotive.rootSummary_inversionAcyclicBridge
    (input : TraceLocalizationInput) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  input.inversionAcyclicBridge

/-- Motive-root summary: the bridge attached to an input remembers that input. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_input
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge input).input =
      input :=
  TraceLocalizationInput.inversionAcyclicBridge_input input

/-- Motive-root summary: the bridge unstable isomorphism. -/
def TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso
    (input : TraceLocalizationInput) :
    CategoryTheory.Iso
      input.unstableSource
      input.unstableTarget :=
  (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge input).unstableIso

/-- Motive-root summary: the bridge unstable isomorphism is the input unstable isomorphism. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso_eq
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso input =
      input.unstableIso :=
  TraceLocalizationInput.inversionAcyclicBridge_unstableIso input

/-- Motive-root summary: the bridge acyclic generator. -/
def TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator :=
  (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge input).acyclicGenerator

/-- Motive-root summary: the bridge acyclic generator is the input acyclic generator. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicGenerator_eq
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicGenerator input =
      input.additiveAcyclicGenerator :=
  TraceLocalizationInput.inversionAcyclicBridge_acyclicGenerator input

/-- Motive-root summary: the bridge acyclic object. -/
def TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge input).acyclicObject

/-- Motive-root summary: the bridge acyclic object is the input acyclic object. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject_eq
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject input =
      input.additiveAcyclicObject :=
  TraceLocalizationInput.inversionAcyclicBridge_acyclicObject input

/-- Motive-root summary: the bridge acyclic object is the input cone third vertex. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject input =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  TraceLocalizationInput.inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex input

/-- Motive-root summary: the bridge unstable isomorphism hom is the unstable forward arrow. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso_hom
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso input).hom =
      input.unstableForward :=
  TraceLocalizationInput.inversionAcyclicBridge_unstableIso_hom input

/-- Motive-root summary: the bridge unstable isomorphism inverse is the unstable inverse arrow. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso_inv
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso input).inv =
      input.unstableInverse :=
  TraceLocalizationInput.inversionAcyclicBridge_unstableIso_inv input

/-- Motive-root summary: the bridge acyclic cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_triangle_distinguished
    (input : TraceLocalizationInput) :
    (TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicGenerator input).triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.inversionAcyclicBridge_triangle_distinguished input

end AnalyticMotives
end LFunctions
end Boundary
