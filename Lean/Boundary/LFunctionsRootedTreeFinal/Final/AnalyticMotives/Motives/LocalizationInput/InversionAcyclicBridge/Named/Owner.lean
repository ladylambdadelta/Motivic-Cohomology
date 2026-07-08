import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.InversionAcyclicBridge.Owner

/-!
# Named inversion-acyclic bridges

This file specializes the inversion-acyclic bridge to the six concrete
analytic localization generators.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The inversion-acyclic bridge for descent-channel localization. -/
def TraceLocalizationInput.descentChannel_inversionAcyclicBridge
    (source target : QTraceExpression) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  (TraceLocalizationInput.descentChannel source target).inversionAcyclicBridge

/-- The descent-channel bridge unstable isomorphism is the descent-channel unstable isomorphism. -/
theorem TraceLocalizationInput.descentChannel_inversionAcyclicBridge_unstableIso
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel_inversionAcyclicBridge source target).unstableIso =
      (TraceLocalizationInput.descentChannel source target).unstableIso :=
  rfl

/-- The descent-channel bridge acyclic object is the descent-channel cone third vertex. -/
theorem TraceLocalizationInput.descentChannel_inversionAcyclicBridge_acyclicObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel_inversionAcyclicBridge source target).acyclicObject =
      (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The inversion-acyclic bridge for descent-refinement localization. -/
def TraceLocalizationInput.descentRefinement_inversionAcyclicBridge
    (source target : QTraceExpression) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  (TraceLocalizationInput.descentRefinement source target).inversionAcyclicBridge

/-- The descent-refinement bridge unstable isomorphism is the descent-refinement unstable isomorphism. -/
theorem TraceLocalizationInput.descentRefinement_inversionAcyclicBridge_unstableIso
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement_inversionAcyclicBridge source target).unstableIso =
      (TraceLocalizationInput.descentRefinement source target).unstableIso :=
  rfl

/-- The descent-refinement bridge acyclic object is the descent-refinement cone third vertex. -/
theorem TraceLocalizationInput.descentRefinement_inversionAcyclicBridge_acyclicObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement_inversionAcyclicBridge source target).acyclicObject =
      (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The inversion-acyclic bridge for descent-schedule localization. -/
def TraceLocalizationInput.descentSchedule_inversionAcyclicBridge
    (source target : QTraceExpression) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  (TraceLocalizationInput.descentSchedule source target).inversionAcyclicBridge

/-- The descent-schedule bridge unstable isomorphism is the descent-schedule unstable isomorphism. -/
theorem TraceLocalizationInput.descentSchedule_inversionAcyclicBridge_unstableIso
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule_inversionAcyclicBridge source target).unstableIso =
      (TraceLocalizationInput.descentSchedule source target).unstableIso :=
  rfl

/-- The descent-schedule bridge acyclic object is the descent-schedule cone third vertex. -/
theorem TraceLocalizationInput.descentSchedule_inversionAcyclicBridge_acyclicObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule_inversionAcyclicBridge source target).acyclicObject =
      (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The inversion-acyclic bridge for interval-Stokes localization. -/
def TraceLocalizationInput.intervalStokes_inversionAcyclicBridge
    (source target : QTraceExpression) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  (TraceLocalizationInput.intervalStokes source target).inversionAcyclicBridge

/-- The interval-Stokes bridge unstable isomorphism is the interval-Stokes unstable isomorphism. -/
theorem TraceLocalizationInput.intervalStokes_inversionAcyclicBridge_unstableIso
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes_inversionAcyclicBridge source target).unstableIso =
      (TraceLocalizationInput.intervalStokes source target).unstableIso :=
  rfl

/-- The interval-Stokes bridge acyclic object is the interval-Stokes cone third vertex. -/
theorem TraceLocalizationInput.intervalStokes_inversionAcyclicBridge_acyclicObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes_inversionAcyclicBridge source target).acyclicObject =
      (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The inversion-acyclic bridge for interval-Fubini localization. -/
def TraceLocalizationInput.intervalFubini_inversionAcyclicBridge
    (source target : QTraceExpression) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  (TraceLocalizationInput.intervalFubini source target).inversionAcyclicBridge

/-- The interval-Fubini bridge unstable isomorphism is the interval-Fubini unstable isomorphism. -/
theorem TraceLocalizationInput.intervalFubini_inversionAcyclicBridge_unstableIso
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini_inversionAcyclicBridge source target).unstableIso =
      (TraceLocalizationInput.intervalFubini source target).unstableIso :=
  rfl

/-- The interval-Fubini bridge acyclic object is the interval-Fubini cone third vertex. -/
theorem TraceLocalizationInput.intervalFubini_inversionAcyclicBridge_acyclicObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini_inversionAcyclicBridge source target).acyclicObject =
      (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

/-- The inversion-acyclic bridge for Tate-weight-drop localization. -/
def TraceLocalizationInput.tateWeightDrop_inversionAcyclicBridge
    (source target : QTraceExpression) :
    TraceLocalizationInput.InversionAcyclicBridge :=
  (TraceLocalizationInput.tateWeightDrop source target).inversionAcyclicBridge

/-- The Tate-weight-drop bridge unstable isomorphism is the Tate-weight-drop unstable isomorphism. -/
theorem TraceLocalizationInput.tateWeightDrop_inversionAcyclicBridge_unstableIso
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop_inversionAcyclicBridge source target).unstableIso =
      (TraceLocalizationInput.tateWeightDrop source target).unstableIso :=
  rfl

/-- The Tate-weight-drop bridge acyclic object is the Tate-weight-drop cone third vertex. -/
theorem TraceLocalizationInput.tateWeightDrop_inversionAcyclicBridge_acyclicObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop_inversionAcyclicBridge source target).acyclicObject =
      (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangleThirdVertex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
