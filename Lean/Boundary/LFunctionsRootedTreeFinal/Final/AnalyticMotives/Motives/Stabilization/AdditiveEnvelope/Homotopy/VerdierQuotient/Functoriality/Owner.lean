import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Maps.Owner

/-!
# Functoriality of represented stable morphisms

The stable represented-morphism constructor is the Verdier quotient functor on
additive-homotopy morphisms.  This file exposes its identity and composition
laws without requiring downstream files to unfold the localization functor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The represented stable morphism of an identity additive-homotopy morphism
is the identity stable morphism. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_id
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticStableMotiveCategory.mapOf
        (𝟙 object : object ⟶ object) =
      𝟙 (TraceAnalyticStableMotiveCategory.objectOf object) :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq
      (𝟙 object : object ⟶ object))
    (TraceAnalyticStableMotiveCategory.quotientFunctor.map_id object)

/-- The represented stable morphism of a composite additive-homotopy morphism
is the composite of the represented stable morphisms. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_comp
    {first second third : TraceAnalyticAdditiveHomotopyCategory}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticStableMotiveCategory.mapOf (left ≫ right) =
      TraceAnalyticStableMotiveCategory.mapOf left ≫
        TraceAnalyticStableMotiveCategory.mapOf right :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq (left ≫ right))
    (Eq.trans
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_comp
        left
        right)
      (congrArg₂
        (fun head tail => head ≫ tail)
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq left))
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq right))))

/-- If a composite additive-homotopy morphism is zero, then the composite of
the represented stable morphisms is zero. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_comp_eq_zero_of_comp_eq_zero
    {first second third : TraceAnalyticAdditiveHomotopyCategory}
    (left : first ⟶ second)
    (right : second ⟶ third)
    (vanishing : left ≫ right = 0) :
    TraceAnalyticStableMotiveCategory.mapOf left ≫
        TraceAnalyticStableMotiveCategory.mapOf right =
      0 :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticStableMotiveCategory.mapOf_comp left right))
    (Eq.trans
      (congrArg
        TraceAnalyticStableMotiveCategory.mapOf
        vanishing)
      (TraceAnalyticStableMotiveCategory.mapOf_zero first third))

end AnalyticMotives
end LFunctions
end Boundary
