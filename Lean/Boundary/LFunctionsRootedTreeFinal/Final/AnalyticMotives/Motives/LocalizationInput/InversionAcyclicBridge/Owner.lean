import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.AcyclicGenerators.Owner

/-!
# Bridge between unstable inversion and additive acyclic generators

This file records the concrete bridge carried by one analytic localization
input: the unstable envelope inverts the input, and the additive homotopy
category carries its mapping-cone acyclic generator.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The additive acyclic generator attached to a localization input. -/
def TraceLocalizationInput.additiveAcyclicGenerator
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveAcyclicGenerator where
  input := input

/-- The additive acyclic generator remembers the localization input. -/
theorem TraceLocalizationInput.additiveAcyclicGenerator_input
    (input : TraceLocalizationInput) :
    input.additiveAcyclicGenerator.input =
      input :=
  rfl

/-- The additive acyclic object attached to a localization input. -/
def TraceLocalizationInput.additiveAcyclicObject
    (input : TraceLocalizationInput) :
    TraceAnalyticAdditiveHomotopyCategory :=
  input.additiveAcyclicGenerator.object

/-- The additive acyclic object is the third vertex of the input mapping-cone triangle. -/
theorem TraceLocalizationInput.additiveAcyclicObject_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    input.additiveAcyclicObject =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The bridge package from unstable inversion to additive acyclic cone data. -/
structure TraceLocalizationInput.InversionAcyclicBridge where
  input : TraceLocalizationInput

/-- The unstable isomorphism carried by an inversion-acyclic bridge. -/
def TraceLocalizationInput.InversionAcyclicBridge.unstableIso
    (bridge : TraceLocalizationInput.InversionAcyclicBridge) :
    CategoryTheory.Iso
      bridge.input.unstableSource
      bridge.input.unstableTarget :=
  bridge.input.unstableIso

/-- The additive acyclic generator carried by an inversion-acyclic bridge. -/
def TraceLocalizationInput.InversionAcyclicBridge.acyclicGenerator
    (bridge : TraceLocalizationInput.InversionAcyclicBridge) :
    TraceAnalyticAdditiveAcyclicGenerator :=
  bridge.input.additiveAcyclicGenerator

/-- The additive acyclic object carried by an inversion-acyclic bridge. -/
def TraceLocalizationInput.InversionAcyclicBridge.acyclicObject
    (bridge : TraceLocalizationInput.InversionAcyclicBridge) :
    TraceAnalyticAdditiveHomotopyCategory :=
  bridge.acyclicGenerator.object

/-- Build the inversion-acyclic bridge attached to a localization input. -/
def TraceLocalizationInput.inversionAcyclicBridge
    (input : TraceLocalizationInput) :
    TraceLocalizationInput.InversionAcyclicBridge where
  input := input

/-- The bridge attached to an input remembers that input. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_input
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.input =
      input :=
  rfl

/-- The bridge unstable isomorphism is the input unstable isomorphism. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_unstableIso
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.unstableIso =
      input.unstableIso :=
  rfl

/-- The bridge acyclic generator is the input additive acyclic generator. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_acyclicGenerator
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.acyclicGenerator =
      input.additiveAcyclicGenerator :=
  rfl

/-- The bridge acyclic object is the input additive acyclic object. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_acyclicObject
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.acyclicObject =
      input.additiveAcyclicObject :=
  rfl

/-- The bridge acyclic object is the third vertex of the input mapping-cone triangle. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_acyclicObject_eq_triangleThirdVertex
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.acyclicObject =
      input.boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The bridge unstable isomorphism has the localized forward arrow as hom. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_unstableIso_hom
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.unstableIso.hom =
      input.unstableForward :=
  rfl

/-- The bridge unstable isomorphism has the localized inverse arrow as inverse. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_unstableIso_inv
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.unstableIso.inv =
      input.unstableInverse :=
  rfl

/-- The bridge acyclic cone triangle is distinguished. -/
theorem TraceLocalizationInput.inversionAcyclicBridge_triangle_distinguished
    (input : TraceLocalizationInput) :
    input.inversionAcyclicBridge.acyclicGenerator.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveAcyclicGenerator.triangle_distinguished
    input.inversionAcyclicBridge.acyclicGenerator

end AnalyticMotives
end LFunctions
end Boundary
