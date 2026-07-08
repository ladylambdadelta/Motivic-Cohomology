import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Lengths.Owner

/-!
# Composition imported-rectangle payload in the unstable envelope

This file exposes imported-rectangle endpoint payload for composition of
unstable analytic-motive homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition keeps the left hom source endpoint rectangles. -/
theorem TraceUnstableAnalyticMotiveHom.comp_sourceImportedRectangles
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangles =
      TraceLocalizedWordHom.sourceImportedRectangles left :=
  TraceLocalizedWordHom.comp_sourceImportedRectangles
    left
    right

/-- Composition keeps the right hom target endpoint rectangles. -/
theorem TraceUnstableAnalyticMotiveHom.comp_targetImportedRectangles
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangles =
      TraceLocalizedWordHom.targetImportedRectangles right :=
  TraceLocalizedWordHom.comp_targetImportedRectangles
    left
    right

/-- Composition keeps the left hom source endpoint imported count. -/
theorem TraceUnstableAnalyticMotiveHom.comp_sourceImportedRectangleCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).sourceImportedRectangleCount =
      TraceLocalizedWordHom.sourceImportedRectangleCount left :=
  TraceLocalizedWordHom.comp_sourceImportedRectangleCount
    left
    right

/-- Composition keeps the right hom target endpoint imported count. -/
theorem TraceUnstableAnalyticMotiveHom.comp_targetImportedRectangleCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).targetImportedRectangleCount =
      TraceLocalizedWordHom.targetImportedRectangleCount right :=
  TraceLocalizedWordHom.comp_targetImportedRectangleCount
    left
    right

/-- The endpoint rectangles of a composed hom are left source followed by right target. -/
theorem TraceUnstableAnalyticMotiveHom.comp_endpointImportedRectangles
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangles =
      TraceLocalizedWordHom.sourceImportedRectangles left ++
        TraceLocalizedWordHom.targetImportedRectangles right :=
  TraceLocalizedWordHom.comp_endpointImportedRectangles
    left
    right

/-- The endpoint count of a composed hom is left source count plus right target count. -/
theorem TraceUnstableAnalyticMotiveHom.comp_endpointImportedRectangleCount
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      TraceLocalizedWordHom.sourceImportedRectangleCount left +
        TraceLocalizedWordHom.targetImportedRectangleCount right :=
  TraceLocalizedWordHom.comp_endpointImportedRectangleCount
    left
    right

/-- A composed hom endpoint imported count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotiveHom.comp_endpointImportedRectangleCount_eq_length
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    (TraceLocalizationWordClass.comp left right).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp left right).endpointImportedRectangles.length :=
  TraceLocalizedWordHom.comp_endpointImportedRectangleCount_eq_length
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
