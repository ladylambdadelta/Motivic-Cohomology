import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.ZeroComposition.Owner

/-!
# Short complex from a chosen Yoneda truncation triangle

This file turns the first two maps of the chosen truncation triangle attached
to a concrete Yoneda representative into a `ShortComplex`.
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

/-- The short complex formed by the first two maps of the chosen truncation
triangle. -/
def shortComplex
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    ShortComplex TraceAnalyticDerivedMotiveCategory :=
  ShortComplex.mk
    representative.firstMap
    representative.secondMap
    representative.firstMap_comp_secondMap

/-- The first object of the chosen truncation short complex is the chosen
lower object. -/
theorem shortComplex_X₁
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex.X₁ = representative.lowerObject :=
  rfl

/-- The middle object of the chosen truncation short complex is the
represented object. -/
theorem shortComplex_X₂
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex.X₂ = object :=
  rfl

/-- The third object of the chosen truncation short complex is the chosen
upper object. -/
theorem shortComplex_X₃
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex.X₃ = representative.upperObject :=
  rfl

/-- The first map of the chosen truncation short complex is the chosen first
map. -/
theorem shortComplex_f
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex.f = representative.firstMap :=
  rfl

/-- The second map of the chosen truncation short complex is the chosen second
map. -/
theorem shortComplex_g
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex.g = representative.secondMap :=
  rfl

/-- The zero field of the chosen truncation short complex is the first
zero-composition law of the chosen triangle. -/
theorem shortComplex_zero
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    representative.shortComplex.zero =
      representative.firstMap_comp_secondMap :=
  rfl

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
