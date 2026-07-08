import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.Subcategories.Owner

/-!
# Certificate for represented truncation objects

This file packages the concrete truncation data attached to an object of the
represented truncation subcategory: the chosen lower and upper vertices lie in
the normalized aisle and coaisle, the chosen triangle is distinguished, its
three consecutive composites are zero, and the chosen short complex is exact
under both preadditive Yoneda tests.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- The represented-object truncation triangle is a normalized
`≤ 0`-to-object-to-`≥ 1` distinguished triangle with the expected
zero-compositions. -/
theorem normalized_triangle_certificate
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.representative.lowerObject =
        (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
          object.lowerAisleObjectZero ∧
      object.representative.upperObject =
        (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
          object.upperCoaisleObjectOne ∧
        object.triangle ∈ distTriang TraceAnalyticDerivedMotiveCategory ∧
          object.firstMap ≫ object.secondMap = 0 ∧
            object.secondMap ≫ object.connectingMap = 0 ∧
  object.connectingMap ≫ object.firstMap⟦(1 : ℤ)⟧' = 0 :=
  And.intro
    (Eq.symm object.lowerAisleObjectZero_inclusion)
    (And.intro
      (Eq.symm object.upperCoaisleObjectOne_inclusion)
      (And.intro
        object.triangle_distinguished
        (And.intro
          object.firstMap_comp_secondMap
          (And.intro
            object.secondMap_comp_connectingMap
            object.connectingMap_comp_shift_firstMap))))

/-- The represented-object chosen short complex is the normalized
aisle-to-object-to-coaisle sequence and is exact after both preadditive Yoneda
tests. -/
theorem normalized_shortComplex_certificate
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    object.shortComplex.X₁ =
        (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
          object.lowerAisleObjectZero ∧
      object.shortComplex.X₂ = object.object ∧
        object.shortComplex.X₃ =
          (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
            object.upperCoaisleObjectOne ∧
          object.shortComplex.f = object.firstMap ∧
            object.shortComplex.g = object.secondMap ∧
              object.shortComplex.zero = object.firstMap_comp_secondMap ∧
                (object.shortComplex.map
                    (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                  (object.shortComplex.op.map
                    (preadditiveYoneda.obj rightProbe)).Exact :=
  let exactPair := object.yonedaExact_pair leftProbe rightProbe
  And.intro
    object.lowerAisleObjectZero_inclusion
    (And.intro
      object.shortComplex_X₂
      (And.intro
        object.upperCoaisleObjectOne_inclusion
        (And.intro
          object.shortComplex_f
          (And.intro
            object.shortComplex_g
            (And.intro
              object.shortComplex_zero
              exactPair)))))

/-- The full represented-object truncation certificate, combining the
distinguished triangle, normalized aisle/coaisle endpoints, zero-compositions,
and paired Yoneda exactness of the associated short complex. -/
theorem normalized_truncation_certificate
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (object.representative.lowerObject =
        (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
          object.lowerAisleObjectZero ∧
      object.representative.upperObject =
        (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
          object.upperCoaisleObjectOne ∧
        object.triangle ∈ distTriang TraceAnalyticDerivedMotiveCategory ∧
          object.firstMap ≫ object.secondMap = 0 ∧
            object.secondMap ≫ object.connectingMap = 0 ∧
              object.connectingMap ≫ object.firstMap⟦(1 : ℤ)⟧' = 0) ∧
      object.shortComplex.X₁ =
        (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
          object.lowerAisleObjectZero ∧
        object.shortComplex.X₂ = object.object ∧
          object.shortComplex.X₃ =
            (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
              object.upperCoaisleObjectOne ∧
            object.shortComplex.f = object.firstMap ∧
              object.shortComplex.g = object.secondMap ∧
                object.shortComplex.zero = object.firstMap_comp_secondMap ∧
                  (object.shortComplex.map
                      (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                    (object.shortComplex.op.map
                      (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    object.normalized_triangle_certificate
    (object.normalized_shortComplex_certificate leftProbe rightProbe)

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
