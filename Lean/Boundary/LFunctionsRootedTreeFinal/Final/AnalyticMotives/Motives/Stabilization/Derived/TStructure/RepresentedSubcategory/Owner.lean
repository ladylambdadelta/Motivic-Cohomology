import Mathlib.CategoryTheory.FullSubcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Owner

/-!
# Represented objects for the derived analytic truncation calculus

This file packages the full subcategory of derived analytic motives carrying
the concrete cut-`1` Yoneda truncation representative used by the current
analytic truncation theorem.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The full subcategory of derived analytic motives equipped with concrete
cut-`1` Yoneda truncation representative data. -/
abbrev RepresentedTruncationObject :=
  CategoryTheory.FullSubcategory
    (TraceAnalyticMotivicTStructure
      .HasYonedaTruncationRepresentative 1)

/-- The inclusion of represented truncation objects into the ambient derived
analytic motive category. -/
abbrev RepresentedTruncationObject.inclusion :
    TraceAnalyticMotivicTStructure.RepresentedTruncationObject ⥤
      TraceAnalyticDerivedMotiveCategory :=
  CategoryTheory.fullSubcategoryInclusion
    (TraceAnalyticMotivicTStructure
      .HasYonedaTruncationRepresentative 1)

/-- The ambient derived analytic motive carried by a represented truncation
object. -/
def RepresentedTruncationObject.object
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticDerivedMotiveCategory :=
  object.obj

/-- The cut-`1` Yoneda truncation representative existence carried by a
represented truncation object. -/
def RepresentedTruncationObject.membership
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticMotivicTStructure
      .HasYonedaTruncationRepresentative 1 object.object :=
  object.property

/-- The inclusion sends a represented truncation object to its ambient
derived analytic motive. -/
theorem RepresentedTruncationObject.inclusion_obj
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticMotivicTStructure
        .RepresentedTruncationObject.inclusion.obj object =
      object.object :=
  rfl

/-- Every represented truncation object has the adjacent Mathlib-shape
truncation triangle supplied by its concrete Yoneda representative data. -/
theorem RepresentedTruncationObject.exists_triangle_zero_one
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
      (firstMap : lower ⟶ object.object)
      (secondMap : object.object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .derivedTStructure_exists_triangle_zero_one_of_yonedaRepresentative
      object.object
      object.membership

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
