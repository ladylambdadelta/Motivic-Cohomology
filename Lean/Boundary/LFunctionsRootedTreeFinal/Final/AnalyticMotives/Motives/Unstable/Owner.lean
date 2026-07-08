import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Owner

/-!
# Unstable analytic motive envelope

This file names the current concrete unstable envelope of analytic motives.

The envelope is the formal localized-word category built from `TraceCorQ`
objects, with the selected analytic calculus inputs inverted.  It is not a
stable category or triangulated category; those layers must be built
downstream from this localized category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the current unstable analytic-motive envelope. -/
abbrev TraceUnstableAnalyticMotive :=
  TraceLocalizedWordObject

/-- Morphisms in the current unstable analytic-motive envelope. -/
abbrev TraceUnstableAnalyticMotiveHom
    (source target : TraceUnstableAnalyticMotive) :=
  TraceLocalizedWordHom source target

/-- Build an unstable analytic motive from a trace-correspondence object. -/
def TraceUnstableAnalyticMotive.ofTraceObject
    (object : TraceCorQObject) :
    TraceUnstableAnalyticMotive :=
  TraceLocalizedWordObject.ofTraceObject object

/-- The unstable analytic-motive category is the localized-word category. -/
def traceUnstableAnalyticMotiveCategory :
    CategoryTheory.Category TraceUnstableAnalyticMotive :=
  traceLocalizationWordCategory

/-- The unstable motive over a trace object remembers that trace object. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_underlying
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).underlying =
      object :=
  TraceLocalizedWordObject.ofTraceObject_underlying
    object

/-- The identity unstable analytic-motive morphism is the identity localized word class. -/
theorem TraceUnstableAnalyticMotive.id_eq
    (object : TraceUnstableAnalyticMotive) :
    (𝟙 object : TraceUnstableAnalyticMotiveHom object object) =
      TraceLocalizationWordClass.identity object.underlying :=
  rfl

/-- Composition of unstable analytic-motive morphisms is localized-word composition. -/
theorem TraceUnstableAnalyticMotive.comp_eq
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    left ≫ right =
      TraceLocalizationWordClass.comp left right :=
  rfl

/-- The identity unstable morphism over a trace object is represented by the empty word. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_id_eq
    (object : TraceCorQObject) :
    (𝟙 (TraceUnstableAnalyticMotive.ofTraceObject object) :
      TraceUnstableAnalyticMotiveHom
        (TraceUnstableAnalyticMotive.ofTraceObject object)
        (TraceUnstableAnalyticMotive.ofTraceObject object)) =
      TraceLocalizationWordClass.identity object :=
  rfl

/-- A localization input supplies a source unstable analytic motive. -/
def TraceLocalizationInput.unstableSource
    (input : TraceLocalizationInput) :
    TraceUnstableAnalyticMotive :=
  input.localizedSourceObject

/-- A localization input supplies a target unstable analytic motive. -/
def TraceLocalizationInput.unstableTarget
    (input : TraceLocalizationInput) :
    TraceUnstableAnalyticMotive :=
  input.localizedTargetObject

/-- A localization input supplies a forward unstable analytic-motive morphism. -/
def TraceLocalizationInput.unstableForward
    (input : TraceLocalizationInput) :
    TraceUnstableAnalyticMotiveHom
      input.unstableSource
      input.unstableTarget :=
  input.localizedForwardArrow

/-- A localization input supplies an inverse unstable analytic-motive morphism. -/
def TraceLocalizationInput.unstableInverse
    (input : TraceLocalizationInput) :
    TraceUnstableAnalyticMotiveHom
      input.unstableTarget
      input.unstableSource :=
  input.localizedInverseArrow

/-- A localization input is inverted in the unstable analytic-motive envelope. -/
def TraceLocalizationInput.unstableIso
    (input : TraceLocalizationInput) :
    CategoryTheory.Iso
      input.unstableSource
      input.unstableTarget :=
  input.localizedIso

/-- The unstable source is the localized source object. -/
theorem TraceLocalizationInput.unstableSource_eq
    (input : TraceLocalizationInput) :
    input.unstableSource =
      input.localizedSourceObject :=
  rfl

/-- The unstable target is the localized target object. -/
theorem TraceLocalizationInput.unstableTarget_eq
    (input : TraceLocalizationInput) :
    input.unstableTarget =
      input.localizedTargetObject :=
  rfl

/-- The unstable forward morphism is the localized forward arrow. -/
theorem TraceLocalizationInput.unstableForward_eq
    (input : TraceLocalizationInput) :
    input.unstableForward =
      input.localizedForwardArrow :=
  rfl

/-- The unstable inverse morphism is the localized inverse arrow. -/
theorem TraceLocalizationInput.unstableInverse_eq
    (input : TraceLocalizationInput) :
    input.unstableInverse =
      input.localizedInverseArrow :=
  rfl

/-- The unstable isomorphism is the localized input isomorphism. -/
theorem TraceLocalizationInput.unstableIso_eq
    (input : TraceLocalizationInput) :
    input.unstableIso =
      input.localizedIso :=
  rfl

/-- The hom of the unstable isomorphism is the unstable forward morphism. -/
theorem TraceLocalizationInput.unstableIso_hom
    (input : TraceLocalizationInput) :
    input.unstableIso.hom =
      input.unstableForward :=
  rfl

/-- The inverse of the unstable isomorphism is the unstable inverse morphism. -/
theorem TraceLocalizationInput.unstableIso_inv
    (input : TraceLocalizationInput) :
    input.unstableIso.inv =
      input.unstableInverse :=
  rfl

/-- Descent-channel inputs are inverted in the unstable envelope. -/
def TraceUnstableAnalyticMotive.descentChannelIso
    (source target : QTraceExpression) :
    CategoryTheory.Iso
      (TraceLocalizationInput.descentChannel source target).unstableSource
      (TraceLocalizationInput.descentChannel source target).unstableTarget :=
  (TraceLocalizationInput.descentChannel source target).unstableIso

/-- Descent-refinement inputs are inverted in the unstable envelope. -/
def TraceUnstableAnalyticMotive.descentRefinementIso
    (source target : QTraceExpression) :
    CategoryTheory.Iso
      (TraceLocalizationInput.descentRefinement source target).unstableSource
      (TraceLocalizationInput.descentRefinement source target).unstableTarget :=
  (TraceLocalizationInput.descentRefinement source target).unstableIso

/-- Descent-schedule inputs are inverted in the unstable envelope. -/
def TraceUnstableAnalyticMotive.descentScheduleIso
    (source target : QTraceExpression) :
    CategoryTheory.Iso
      (TraceLocalizationInput.descentSchedule source target).unstableSource
      (TraceLocalizationInput.descentSchedule source target).unstableTarget :=
  (TraceLocalizationInput.descentSchedule source target).unstableIso

/-- Interval-Stokes inputs are inverted in the unstable envelope. -/
def TraceUnstableAnalyticMotive.intervalStokesIso
    (source target : QTraceExpression) :
    CategoryTheory.Iso
      (TraceLocalizationInput.intervalStokes source target).unstableSource
      (TraceLocalizationInput.intervalStokes source target).unstableTarget :=
  (TraceLocalizationInput.intervalStokes source target).unstableIso

/-- Interval-Fubini inputs are inverted in the unstable envelope. -/
def TraceUnstableAnalyticMotive.intervalFubiniIso
    (source target : QTraceExpression) :
    CategoryTheory.Iso
      (TraceLocalizationInput.intervalFubini source target).unstableSource
      (TraceLocalizationInput.intervalFubini source target).unstableTarget :=
  (TraceLocalizationInput.intervalFubini source target).unstableIso

/-- Tate-weight-drop inputs are inverted in the unstable envelope. -/
def TraceUnstableAnalyticMotive.tateWeightDropIso
    (source target : QTraceExpression) :
    CategoryTheory.Iso
      (TraceLocalizationInput.tateWeightDrop source target).unstableSource
      (TraceLocalizationInput.tateWeightDrop source target).unstableTarget :=
  (TraceLocalizationInput.tateWeightDrop source target).unstableIso

/-- The descent-channel unstable isomorphism is the input-level localized isomorphism. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentChannelIso source target =
      TraceLocalizationInput.descentChannelLocalizedIso source target :=
  rfl

/-- The descent-refinement unstable isomorphism is the input-level localized isomorphism. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentRefinementIso source target =
      TraceLocalizationInput.descentRefinementLocalizedIso source target :=
  rfl

/-- The descent-schedule unstable isomorphism is the input-level localized isomorphism. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentScheduleIso source target =
      TraceLocalizationInput.descentScheduleLocalizedIso source target :=
  rfl

/-- The interval-Stokes unstable isomorphism is the input-level localized isomorphism. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.intervalStokesIso source target =
      TraceLocalizationInput.intervalStokesLocalizedIso source target :=
  rfl

/-- The interval-Fubini unstable isomorphism is the input-level localized isomorphism. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.intervalFubiniIso source target =
      TraceLocalizationInput.intervalFubiniLocalizedIso source target :=
  rfl

/-- The Tate-weight-drop unstable isomorphism is the input-level localized isomorphism. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.tateWeightDropIso source target =
      TraceLocalizationInput.tateWeightDropLocalizedIso source target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
