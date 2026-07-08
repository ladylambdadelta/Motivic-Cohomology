import Mathlib.CategoryTheory.Triangulated.Functor
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# Triangulated functor structure of the analytic Verdier quotient

The analytic stable motive category is obtained by Verdier localization of the
additive analytic homotopy category.  This file exposes the induced
triangulated-functor structure on the quotient functor and the corresponding
distinguished-triangle transport theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic Verdier quotient functor is triangulated. -/
def TraceAnalyticStableMotiveCategory.quotientFunctorIsTriangulated :
    TraceAnalyticStableMotiveCategory.quotientFunctor.IsTriangulated :=
  letI stablePretriangulated :
      Pretriangulated TraceAnalyticStableMotiveCategory :=
    TraceAnalyticStableMotiveCategory.pretriangulatedStructure
  CategoryTheory.Triangulated.Localization.isTriangulated_functor
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms

/-- The analytic Verdier quotient sends additive distinguished triangles to
stable distinguished triangles. -/
theorem TraceAnalyticStableMotiveCategory.quotientFunctor_map_distinguished
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    TraceAnalyticStableMotiveCategory.quotientFunctor.mapTriangle.obj
        triangle ∈
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  CategoryTheory.Functor.map_distinguished
    TraceAnalyticStableMotiveCategory.quotientFunctor
    triangle
    distinguished

/-- The stable image of an additive distinguished triangle has zero first
two-fold composite. -/
theorem TraceAnalyticStableMotiveCategory.comp_zero₁₂_of_quotient_distinguished
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    (TraceAnalyticStableMotiveCategory.quotientFunctor.mapTriangle.obj
        triangle).mor₁ ≫
      (TraceAnalyticStableMotiveCategory.quotientFunctor.mapTriangle.obj
        triangle).mor₂ =
        0 :=
  CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂
    (TraceAnalyticStableMotiveCategory.quotientFunctor.mapTriangle.obj
      triangle)
    (TraceAnalyticStableMotiveCategory.quotientFunctor_map_distinguished
      triangle
      distinguished)

end AnalyticMotives
end LFunctions
end Boundary
