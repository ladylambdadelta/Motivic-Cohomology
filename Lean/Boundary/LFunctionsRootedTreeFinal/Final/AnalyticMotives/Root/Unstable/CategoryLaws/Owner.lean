import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.CategoryLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.CategoryLaws.CompactInterpretationTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.CategoryLaws.ForwardWordTriples.Owner

/-!
# Public category laws for unstable analytic motives

This file exposes the categorical operations and laws of the unstable
analytic-motive envelope through the public root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: unstable identity is localized-word identity. -/
theorem AnalyticMotivesRoot.unstableIdentity_eq_wordClass
    (object : TraceUnstableAnalyticMotive) :
    (𝟙 object : TraceUnstableAnalyticMotiveHom object object) =
      TraceLocalizationWordClass.identity object.underlying :=
  TraceAnalyticMotive.unstableIdentity_eq_wordClass
    object

/-- Public wrapper: unstable composition is localized-word composition. -/
theorem AnalyticMotivesRoot.unstableComposition_eq_wordClass_comp
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    left ≫ right =
      TraceLocalizationWordClass.comp left right :=
  TraceAnalyticMotive.unstableComposition_eq_wordClass_comp
    left
    right

/-- Public wrapper: left identity for unstable analytic-motive morphisms. -/
theorem AnalyticMotivesRoot.unstableIdentity_comp
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    (𝟙 source : TraceUnstableAnalyticMotiveHom source source) ≫ hom =
      hom :=
  TraceAnalyticMotive.unstableIdentity_comp
    hom

/-- Public wrapper: right identity for unstable analytic-motive morphisms. -/
theorem AnalyticMotivesRoot.unstableComp_identity
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom ≫ (𝟙 target : TraceUnstableAnalyticMotiveHom target target) =
      hom :=
  TraceAnalyticMotive.unstableComp_identity
    hom

/-- Public wrapper: associativity for unstable analytic-motive morphisms. -/
theorem AnalyticMotivesRoot.unstableComposition_assoc
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
