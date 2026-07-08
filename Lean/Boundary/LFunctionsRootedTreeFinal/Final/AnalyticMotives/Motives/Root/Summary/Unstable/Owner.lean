import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Owner

/-!
# Motive-root unstable category summaries

This file exposes root summary theorems for unstable analytic motive identity
and composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: unstable identity is localized-word identity. -/
theorem TraceAnalyticMotive.rootSummary_unstableIdentity_eq_wordClass
    (object : TraceUnstableAnalyticMotive) :
    (𝟙 object : TraceUnstableAnalyticMotiveHom object object) =
      TraceLocalizationWordClass.identity object.underlying :=
  TraceAnalyticMotive.unstableIdentity_eq_wordClass
    object

/-- Motive-root summary: unstable composition is localized-word composition. -/
theorem TraceAnalyticMotive.rootSummary_unstableComposition_eq_wordClass_comp
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    left ≫ right =
      TraceLocalizationWordClass.comp left right :=
  TraceAnalyticMotive.unstableComposition_eq_wordClass_comp
    left
    right

/-- Motive-root summary: unstable left identity law. -/
theorem TraceAnalyticMotive.rootSummary_unstableIdentity_comp
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    (𝟙 source : TraceUnstableAnalyticMotiveHom source source) ≫ hom =
      hom :=
  TraceAnalyticMotive.unstableIdentity_comp
    hom

/-- Motive-root summary: unstable right identity law. -/
theorem TraceAnalyticMotive.rootSummary_unstableComp_identity
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom ≫ (𝟙 target : TraceUnstableAnalyticMotiveHom target target) =
      hom :=
  TraceAnalyticMotive.unstableComp_identity
    hom

/-- Motive-root summary: unstable composition is associative. -/
theorem TraceAnalyticMotive.rootSummary_unstableComposition_assoc
    {first second third fourth : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (middle : TraceUnstableAnalyticMotiveHom second third)
    (right : TraceUnstableAnalyticMotiveHom third fourth) :
    (left ≫ middle) ≫ right =
      left ≫ (middle ≫ right) :=
  TraceAnalyticMotive.unstableComposition_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary
