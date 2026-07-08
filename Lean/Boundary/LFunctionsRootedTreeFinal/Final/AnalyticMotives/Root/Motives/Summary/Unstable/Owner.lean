import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.Owner

/-!
# Top-root unstable category summaries

This file exposes unstable analytic motive identity and composition laws under
the public analytic-motives root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public motive summary: unstable identity is localized-word identity. -/
theorem AnalyticMotivesRoot.rootSummary_unstableIdentity_eq_wordClass
    (object : TraceUnstableAnalyticMotive) :
    (𝟙 object : TraceUnstableAnalyticMotiveHom object object) =
      TraceLocalizationWordClass.identity object.underlying :=
  TraceAnalyticMotive.rootSummary_unstableIdentity_eq_wordClass
    object

/-- Public motive summary: unstable composition is localized-word composition. -/
theorem AnalyticMotivesRoot.rootSummary_unstableComposition_eq_wordClass_comp
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    left ≫ right =
      TraceLocalizationWordClass.comp left right :=
  TraceAnalyticMotive.rootSummary_unstableComposition_eq_wordClass_comp
    left
    right

/-- Public motive summary: unstable left identity law. -/
theorem AnalyticMotivesRoot.rootSummary_unstableIdentity_comp
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    (𝟙 source : TraceUnstableAnalyticMotiveHom source source) ≫ hom =
      hom :=
  TraceAnalyticMotive.rootSummary_unstableIdentity_comp
    hom

/-- Public motive summary: unstable right identity law. -/
theorem AnalyticMotivesRoot.rootSummary_unstableComp_identity
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom ≫ (𝟙 target : TraceUnstableAnalyticMotiveHom target target) =
      hom :=
  TraceAnalyticMotive.rootSummary_unstableComp_identity
    hom

/-- Public motive summary: unstable composition is associative. -/
theorem AnalyticMotivesRoot.rootSummary_unstableComposition_assoc
    {first second third fourth : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (middle : TraceUnstableAnalyticMotiveHom second third)
    (right : TraceUnstableAnalyticMotiveHom third fourth) :
    (left ≫ middle) ≫ right =
      left ≫ (middle ≫ right) :=
  TraceAnalyticMotive.rootSummary_unstableComposition_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary
