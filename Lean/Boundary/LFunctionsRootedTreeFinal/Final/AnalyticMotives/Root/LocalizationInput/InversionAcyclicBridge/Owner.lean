import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.InversionAcyclicBridge.Owner

/-!
# Public inversion-acyclic bridge facade

This file exposes the concrete bridge between unstable inversion and additive
mapping-cone acyclic generators at the public root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root facade: the inversion-acyclic bridge attached to a localization input. -/
def AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge
    (input : TraceLocalizationInput) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge input

/-- Public root facade: the bridge unstable isomorphism. -/
def AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso
    (input : TraceLocalizationInput) :
    CategoryTheory.Iso
      input.unstableSource
      input.unstableTarget :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso input

/-- Public root facade: the bridge unstable isomorphism is the input unstable isomorphism. -/
theorem AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso_eq
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso input =
      input.unstableIso :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso_eq input

/-- Public root facade: the bridge acyclic generator. -/
def AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicGenerator input

/-- Public root facade: the bridge acyclic generator is the input acyclic generator. -/
theorem AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicGenerator_eq
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicGenerator input =
      input.additiveAcyclicGenerator :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicGenerator_eq input

/-- Public root facade: the bridge acyclic object. -/
def AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicObject
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicObject input

/-- Public root facade: the bridge acyclic object is the input cone third vertex. -/
theorem AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicObject input =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex input

/-- Public root facade: the bridge unstable isomorphism hom is the unstable forward arrow. -/
theorem AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso_hom
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso input).hom =
      input.unstableForward :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso_hom input

/-- Public root facade: the bridge unstable isomorphism inverse is the unstable inverse arrow. -/
theorem AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso_inv
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_unstableIso input).inv =
      input.unstableInverse :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso_inv input

/-- Public root facade: the bridge acyclic cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_triangle_distinguished
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootFacade_inversionAcyclicBridge_acyclicGenerator input).triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_triangle_distinguished input

end AnalyticMotives
end LFunctions
end Boundary
