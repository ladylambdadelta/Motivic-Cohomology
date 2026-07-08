import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Owner

/-!
# Projections from chosen Yoneda truncation triangles

This file records the definitional projections from the chosen truncation
triangle attached to a concrete Yoneda representative.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- The first vertex of the chosen triangle is the chosen lower object. -/
theorem triangle_obj₁
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle.obj₁ = representative.lowerObject :=
  rfl

/-- The second vertex of the chosen triangle is the represented object. -/
theorem triangle_obj₂
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle.obj₂ = object :=
  rfl

/-- The third vertex of the chosen triangle is the chosen upper object. -/
theorem triangle_obj₃
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle.obj₃ = representative.upperObject :=
  rfl

/-- The first map of the chosen triangle is the chosen first truncation map. -/
theorem triangle_mor₁
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle.mor₁ = representative.firstMap :=
  rfl

/-- The second map of the chosen triangle is the chosen second truncation map. -/
theorem triangle_mor₂
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle.mor₂ = representative.secondMap :=
  rfl

/-- The connecting map of the chosen triangle is the chosen connecting map. -/
theorem triangle_mor₃
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.triangle.mor₃ = representative.connectingMap :=
  rfl

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
