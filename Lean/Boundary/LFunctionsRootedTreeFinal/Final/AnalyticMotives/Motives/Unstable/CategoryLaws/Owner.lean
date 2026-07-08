import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner

/-!
# Category laws for the unstable analytic-motive envelope

This file exposes the categorical operations of the unstable analytic-motive
envelope as concrete localized-word operations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity unstable morphism is the localized-word identity. -/
theorem TraceUnstableAnalyticMotive.identity_eq_wordClass
    (object : TraceUnstableAnalyticMotive) :
    (𝟙 object : TraceUnstableAnalyticMotiveHom object object) =
      TraceLocalizationWordClass.identity object.underlying :=
  TraceUnstableAnalyticMotive.id_eq
    object

/-- Unstable morphism composition is localized-word-class composition. -/
theorem TraceUnstableAnalyticMotive.composition_eq_wordClass_comp
    {first second third : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (right : TraceUnstableAnalyticMotiveHom second third) :
    left ≫ right =
      TraceLocalizationWordClass.comp left right :=
  TraceUnstableAnalyticMotive.comp_eq
    left
    right

/-- Left identity for unstable analytic-motive morphisms. -/
theorem TraceUnstableAnalyticMotive.identity_comp
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    (𝟙 source : TraceUnstableAnalyticMotiveHom source source) ≫ hom =
      hom :=
  TraceLocalizationWordClass.comp_identity_left
    hom

/-- Right identity for unstable analytic-motive morphisms. -/
theorem TraceUnstableAnalyticMotive.comp_identity
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom ≫ (𝟙 target : TraceUnstableAnalyticMotiveHom target target) =
      hom :=
  TraceLocalizationWordClass.comp_identity_right
    hom

/-- Associativity for unstable analytic-motive morphisms. -/
theorem TraceUnstableAnalyticMotive.composition_assoc
    {first second third fourth : TraceUnstableAnalyticMotive}
    (left : TraceUnstableAnalyticMotiveHom first second)
    (middle : TraceUnstableAnalyticMotiveHom second third)
    (right : TraceUnstableAnalyticMotiveHom third fourth) :
    (left ≫ middle) ≫ right =
      left ≫ (middle ≫ right) :=
  TraceLocalizationWordClass.comp_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary
