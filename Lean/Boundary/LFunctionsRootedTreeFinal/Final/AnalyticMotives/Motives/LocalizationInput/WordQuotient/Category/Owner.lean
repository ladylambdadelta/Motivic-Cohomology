import Mathlib.CategoryTheory.Category.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Owner

/-!
# Category of formal localized words

This file packages formal localized word classes as a category on a wrapper of
trace objects.  The wrapper keeps this formal localization category separate
from the ambient `TraceCorQ` category instance on bare trace objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the formal localized word category. -/
structure TraceLocalizedWordObject where
  underlying : TraceCorQObject

/-- The localized-word object over a trace-correspondence object. -/
def TraceLocalizedWordObject.ofTraceObject
    (object : TraceCorQObject) :
    TraceLocalizedWordObject where
  underlying := object

/-- The localized-word object constructor has the supplied underlying object. -/
theorem TraceLocalizedWordObject.ofTraceObject_underlying
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).underlying =
      object :=
  rfl

/-- Homs in the formal localized word category. -/
abbrev TraceLocalizedWordHom
    (source target : TraceLocalizedWordObject) :=
  TraceLocalizationWordClass source.underlying target.underlying

/-- The category of formal localized trace words. -/
instance traceLocalizationWordCategory :
    CategoryTheory.Category TraceLocalizedWordObject where
  Hom := TraceLocalizedWordHom
  id := fun object =>
    TraceLocalizationWordClass.identity object.underlying
  comp := fun left right =>
    TraceLocalizationWordClass.comp left right
  id_comp := fun hom =>
    TraceLocalizationWordClass.comp_identity_left hom
  comp_id := fun hom =>
    TraceLocalizationWordClass.comp_identity_right hom
  assoc := fun left middle right =>
    TraceLocalizationWordClass.comp_assoc left middle right

end AnalyticMotives
end LFunctions
end Boundary
