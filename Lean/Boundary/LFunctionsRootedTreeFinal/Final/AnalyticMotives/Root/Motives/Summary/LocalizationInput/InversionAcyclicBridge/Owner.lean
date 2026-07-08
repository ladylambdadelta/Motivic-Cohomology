import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.InversionAcyclicBridge.Owner

/-!
# Top-root motive summary for inversion-acyclic bridges

This file forwards the concrete bridge between unstable inversion and additive
mapping-cone acyclic generators to the top-root motive summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root motive summary: the inversion-acyclic bridge attached to a localization input. -/
def AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge
    (input : TraceLocalizationInput) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge input

/-- Top-root motive summary: the bridge unstable isomorphism. -/
def AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso
    (input : TraceLocalizationInput) :
    CategoryTheory.Iso
      input.unstableSource
      input.unstableTarget :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso input

/-- Top-root motive summary: the bridge unstable isomorphism is the input unstable isomorphism. -/
theorem AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso_eq
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso input =
      input.unstableIso :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso_eq input

/-- Top-root motive summary: the bridge acyclic generator. -/
def AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicGenerator input

/-- Top-root motive summary: the bridge acyclic generator is the input acyclic generator. -/
theorem AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicGenerator_eq
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicGenerator input =
      input.additiveAcyclicGenerator :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicGenerator_eq input

/-- Top-root motive summary: the bridge acyclic object. -/
def AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicObject
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject input

/-- Top-root motive summary: the bridge acyclic object is the input cone third vertex. -/
theorem AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicObject input =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex input

/-- Top-root motive summary: the bridge unstable isomorphism hom is the unstable forward arrow. -/
theorem AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso_hom
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso input).hom =
      input.unstableForward :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso_hom input

/-- Top-root motive summary: the bridge unstable isomorphism inverse is the unstable inverse arrow. -/
theorem AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso_inv
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_unstableIso input).inv =
      input.unstableInverse :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_unstableIso_inv input

/-- Top-root motive summary: the bridge acyclic cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_triangle_distinguished
    (input : TraceLocalizationInput) :
    (AnalyticMotivesRoot.rootSummary_inversionAcyclicBridge_acyclicGenerator input).triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_inversionAcyclicBridge_triangle_distinguished input

end AnalyticMotives
end LFunctions
end Boundary
