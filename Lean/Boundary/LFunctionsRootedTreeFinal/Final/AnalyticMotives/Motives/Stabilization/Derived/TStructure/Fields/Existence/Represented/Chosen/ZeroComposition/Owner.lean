import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Projections.Owner

/-!
# Zero-composition laws for chosen Yoneda truncation triangles

This file specializes the distinguished-triangle zero-composition laws to the
chosen truncation triangle attached to a concrete Yoneda representative.
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

/-- In the chosen truncation triangle, the first map followed by the second
map is zero. -/
theorem firstMap_comp_secondMap
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.firstMap ≫ representative.secondMap = 0 :=
  Pretriangulated.comp_distTriang_mor_zero₁₂
    representative.triangle
    representative.triangle_distinguished

/-- In the chosen truncation triangle, the second map followed by the
connecting map is zero. -/
theorem secondMap_comp_connectingMap
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.secondMap ≫ representative.connectingMap = 0 :=
  Pretriangulated.comp_distTriang_mor_zero₂₃
    representative.triangle
    representative.triangle_distinguished

/-- In the chosen truncation triangle, the connecting map followed by the
shifted first map is zero. -/
theorem connectingMap_comp_shift_firstMap
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.connectingMap ≫ representative.firstMap⟦(1 : ℤ)⟧' = 0 :=
  Pretriangulated.comp_distTriang_mor_zero₃₁
    representative.triangle
    representative.triangle_distinguished

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
