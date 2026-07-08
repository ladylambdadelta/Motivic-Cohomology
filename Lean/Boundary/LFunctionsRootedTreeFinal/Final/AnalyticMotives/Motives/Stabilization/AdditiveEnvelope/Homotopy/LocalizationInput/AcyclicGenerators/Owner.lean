import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.LocalizationInput.Owner

/-!
# Stable acyclic generators from analytic localization inputs

This file packages the stable cone object attached to each concrete analytic
localization input.  These are the generators for the Verdier-null class used
by the later analytic motive quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A stable acyclic generator is the mapping-cone object of a concrete analytic
localization input in the additive analytic homotopy category. -/
structure TraceAnalyticStableAcyclicGenerator where
  input : TraceLocalizationInput

/-- The stable distinguished triangle attached to an acyclic generator. -/
def TraceAnalyticStableAcyclicGenerator.triangle
    (generator : TraceAnalyticStableAcyclicGenerator) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  generator.input.stableMappingConeTriangle

/-- The stable acyclic object attached to an acyclic generator. -/
def TraceAnalyticStableAcyclicGenerator.object
    (generator : TraceAnalyticStableAcyclicGenerator) :
    TraceAnalyticAdditiveHomotopyCategory :=
  generator.triangle.obj₃

/-- The source object of the stable acyclic triangle. -/
def TraceAnalyticStableAcyclicGenerator.source
    (generator : TraceAnalyticStableAcyclicGenerator) :
    TraceAnalyticAdditiveHomotopyCategory :=
  generator.triangle.obj₁

/-- The target object of the stable acyclic triangle. -/
def TraceAnalyticStableAcyclicGenerator.target
    (generator : TraceAnalyticStableAcyclicGenerator) :
    TraceAnalyticAdditiveHomotopyCategory :=
  generator.triangle.obj₂

/-- The first map in the stable acyclic triangle. -/
def TraceAnalyticStableAcyclicGenerator.firstMap
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.source ⟶ generator.target :=
  generator.triangle.mor₁

/-- The cone map into the stable acyclic object. -/
def TraceAnalyticStableAcyclicGenerator.coneMap
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.target ⟶ generator.object :=
  generator.triangle.mor₂

/-- The connecting map out of the stable acyclic object. -/
def TraceAnalyticStableAcyclicGenerator.connectingMap
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.object ⟶ generator.source⟦(1 : ℤ)⟧ :=
  generator.triangle.mor₃

/-- The stable acyclic triangle is the stable mapping-cone triangle of its input. -/
theorem TraceAnalyticStableAcyclicGenerator.triangle_eq
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.triangle =
      generator.input.stableMappingConeTriangle :=
  rfl

/-- The stable acyclic triangle is distinguished. -/
theorem TraceAnalyticStableAcyclicGenerator.triangle_distinguished
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  generator.input.stableMappingConeTriangle_distinguished

/-- The stable acyclic object is the third vertex of the stable cone triangle. -/
theorem TraceAnalyticStableAcyclicGenerator.object_eq_triangle_obj₃
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.object =
      generator.triangle.obj₃ :=
  rfl

/-- The source is the first vertex of the stable cone triangle. -/
theorem TraceAnalyticStableAcyclicGenerator.source_eq_triangle_obj₁
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.source =
      generator.triangle.obj₁ :=
  rfl

/-- The target is the second vertex of the stable cone triangle. -/
theorem TraceAnalyticStableAcyclicGenerator.target_eq_triangle_obj₂
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.target =
      generator.triangle.obj₂ :=
  rfl

/-- The first map is the first morphism of the stable cone triangle. -/
theorem TraceAnalyticStableAcyclicGenerator.firstMap_eq_triangle_mor₁
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.firstMap =
      generator.triangle.mor₁ :=
  rfl

/-- The first map of a stable acyclic generator is the stable map of its input. -/
theorem TraceAnalyticStableAcyclicGenerator.firstMap_eq_input_stableMap
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.firstMap =
      generator.input.stableMap :=
  rfl

/-- The cone map is the second morphism of the stable cone triangle. -/
theorem TraceAnalyticStableAcyclicGenerator.coneMap_eq_triangle_mor₂
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.coneMap =
      generator.triangle.mor₂ :=
  rfl

/-- The connecting map is the third morphism of the stable cone triangle. -/
theorem TraceAnalyticStableAcyclicGenerator.connectingMap_eq_triangle_mor₃
    (generator : TraceAnalyticStableAcyclicGenerator) :
    generator.connectingMap =
      generator.triangle.mor₃ :=
  rfl

/-- The stable acyclic generator attached to descent-channel localization. -/
def TraceAnalyticStableAcyclicGenerator.descentChannel
    (source target : QTraceExpression) :
    TraceAnalyticStableAcyclicGenerator where
  input := TraceLocalizationInput.descentChannel source target

/-- The stable acyclic generator attached to descent-refinement localization. -/
def TraceAnalyticStableAcyclicGenerator.descentRefinement
    (source target : QTraceExpression) :
    TraceAnalyticStableAcyclicGenerator where
  input := TraceLocalizationInput.descentRefinement source target

/-- The stable acyclic generator attached to descent-schedule localization. -/
def TraceAnalyticStableAcyclicGenerator.descentSchedule
    (source target : QTraceExpression) :
    TraceAnalyticStableAcyclicGenerator where
  input := TraceLocalizationInput.descentSchedule source target

/-- The stable acyclic generator attached to interval-Stokes localization. -/
def TraceAnalyticStableAcyclicGenerator.intervalStokes
    (source target : QTraceExpression) :
    TraceAnalyticStableAcyclicGenerator where
  input := TraceLocalizationInput.intervalStokes source target

/-- The stable acyclic generator attached to interval-Fubini localization. -/
def TraceAnalyticStableAcyclicGenerator.intervalFubini
    (source target : QTraceExpression) :
    TraceAnalyticStableAcyclicGenerator where
  input := TraceLocalizationInput.intervalFubini source target

/-- The stable acyclic generator attached to Tate-weight-drop localization. -/
def TraceAnalyticStableAcyclicGenerator.tateWeightDrop
    (source target : QTraceExpression) :
    TraceAnalyticStableAcyclicGenerator where
  input := TraceLocalizationInput.tateWeightDrop source target

/-- Descent-channel stable acyclic generators remember their localization input. -/
theorem TraceAnalyticStableAcyclicGenerator.descentChannel_input
    (source target : QTraceExpression) :
    (TraceAnalyticStableAcyclicGenerator.descentChannel source target).input =
      TraceLocalizationInput.descentChannel source target :=
  rfl

/-- Descent-refinement stable acyclic generators remember their localization input. -/
theorem TraceAnalyticStableAcyclicGenerator.descentRefinement_input
    (source target : QTraceExpression) :
    (TraceAnalyticStableAcyclicGenerator.descentRefinement source target).input =
      TraceLocalizationInput.descentRefinement source target :=
  rfl

/-- Descent-schedule stable acyclic generators remember their localization input. -/
theorem TraceAnalyticStableAcyclicGenerator.descentSchedule_input
    (source target : QTraceExpression) :
    (TraceAnalyticStableAcyclicGenerator.descentSchedule source target).input =
      TraceLocalizationInput.descentSchedule source target :=
  rfl

/-- Interval-Stokes stable acyclic generators remember their localization input. -/
theorem TraceAnalyticStableAcyclicGenerator.intervalStokes_input
    (source target : QTraceExpression) :
    (TraceAnalyticStableAcyclicGenerator.intervalStokes source target).input =
      TraceLocalizationInput.intervalStokes source target :=
  rfl

/-- Interval-Fubini stable acyclic generators remember their localization input. -/
theorem TraceAnalyticStableAcyclicGenerator.intervalFubini_input
    (source target : QTraceExpression) :
    (TraceAnalyticStableAcyclicGenerator.intervalFubini source target).input =
      TraceLocalizationInput.intervalFubini source target :=
  rfl

/-- Tate-weight-drop stable acyclic generators remember their localization input. -/
theorem TraceAnalyticStableAcyclicGenerator.tateWeightDrop_input
    (source target : QTraceExpression) :
    (TraceAnalyticStableAcyclicGenerator.tateWeightDrop source target).input =
      TraceLocalizationInput.tateWeightDrop source target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
