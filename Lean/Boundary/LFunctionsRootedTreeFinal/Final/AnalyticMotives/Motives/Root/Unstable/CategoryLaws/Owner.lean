import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.CategoryLaws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.CategoryLaws.CompactInterpretationTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.CategoryLaws.ForwardWordTriples.Owner

/-!
# Motive-root category laws for unstable analytic motives

This file exposes unstable analytic-motive identities, composition, unit laws,
and associativity through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: unstable identity is localized-word identity. -/
theorem TraceAnalyticMotive.unstableIdentity_eq_wordClass
    (object : TraceUnstableAnalyticMotive) :
    (𝟙 object : TraceUnstableAnalyticMotiveHom object object) =
      TraceLocalizationWordClass.identity object.underlying :=
  TraceUnstableAnalyticMotive.identity_eq_wordClass
    object

/-- Motive-root wrapper: unstable composition is localized-word composition. -/
theorem TraceAnalyticMotive.unstableComposition_eq_wordClass_comp
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    left ≫ right =
      TraceLocalizationWordClass.comp left right :=
  TraceUnstableAnalyticMotive.composition_eq_wordClass_comp
    left
    right

/-- Motive-root wrapper: left identity for unstable analytic-motive morphisms. -/
theorem TraceAnalyticMotive.unstableIdentity_comp
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    (𝟙 source : TraceUnstableAnalyticMotiveHom source source) ≫ hom =
      hom :=
  TraceUnstableAnalyticMotive.identity_comp
    hom

/-- Motive-root wrapper: right identity for unstable analytic-motive morphisms. -/
theorem TraceAnalyticMotive.unstableComp_identity
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom ≫ (𝟙 target : TraceUnstableAnalyticMotiveHom target target) =
      hom :=
  TraceUnstableAnalyticMotive.comp_identity
    hom

/-- Motive-root wrapper: associativity for unstable analytic-motive morphisms. -/
theorem TraceAnalyticMotive.unstableComposition_assoc
    {first second third fourth : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (middle : TraceUnstableAnalyticMotiveHom second third)
    (right : TraceUnstableAnalyticMotiveHom third fourth) :
    (left ≫ middle) ≫ right =
      left ≫ (middle ≫ right) :=
  TraceUnstableAnalyticMotive.composition_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary
