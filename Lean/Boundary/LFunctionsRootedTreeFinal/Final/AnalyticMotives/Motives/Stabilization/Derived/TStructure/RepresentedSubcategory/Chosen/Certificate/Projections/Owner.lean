import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.Certificate.Owner

/-!
# Projections from represented-object truncation certificates

This file exposes the grouped triangle and short-complex parts of the full
represented-object truncation certificate.
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

/-- The triangle part of the full represented-object truncation certificate. -/
theorem normalized_truncation_certificate_triangle_part
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
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
  (object.normalized_truncation_certificate leftProbe rightProbe).left

/-- The short-complex part of the full represented-object truncation
certificate. -/
theorem normalized_truncation_certificate_shortComplex_part
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
  (object.normalized_truncation_certificate leftProbe rightProbe).right

/-- The full represented-object truncation certificate recovers the
represented-object normalized exact-sequence certificate. -/
theorem normalized_truncation_certificate_exactSequence_part
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
          object.shortComplex.f = object.representative.firstMap ∧
            object.shortComplex.g = object.representative.secondMap ∧
              (object.shortComplex.map
                  (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                (object.shortComplex.op.map
                  (preadditiveYoneda.obj rightProbe)).Exact :=
  object.normalized_exactSequence_certificate leftProbe rightProbe

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
