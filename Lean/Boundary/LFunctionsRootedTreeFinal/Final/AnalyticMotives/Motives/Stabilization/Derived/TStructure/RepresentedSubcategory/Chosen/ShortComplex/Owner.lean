import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.Triangle.Owner

/-!
# Chosen truncation short complex for represented truncation objects

This file exposes the explicit chosen truncation short complex attached to an
object of the represented truncation subcategory, together with its
projections and paired Yoneda exactness.
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

/-- The first object of the represented-object chosen short complex is the
chosen lower object. -/
theorem shortComplex_X₁
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.X₁ = object.representative.lowerObject :=
  object.representative.shortComplex_X₁

/-- The middle object of the represented-object chosen short complex is the
ambient represented object. -/
theorem shortComplex_X₂
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.X₂ = object.object :=
  object.representative.shortComplex_X₂

/-- The third object of the represented-object chosen short complex is the
chosen upper object. -/
theorem shortComplex_X₃
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.X₃ = object.representative.upperObject :=
  object.representative.shortComplex_X₃

/-- The first map of the represented-object chosen short complex is the chosen
lower truncation map. -/
theorem shortComplex_f
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.f = object.firstMap :=
  object.representative.shortComplex_f

/-- The second map of the represented-object chosen short complex is the
chosen upper truncation map. -/
theorem shortComplex_g
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.g = object.secondMap :=
  object.representative.shortComplex_g

/-- The zero field of the represented-object chosen short complex is the
first zero-composition law of the chosen triangle. -/
theorem shortComplex_zero
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.shortComplex.zero = object.firstMap_comp_secondMap :=
  object.representative.shortComplex_zero

/-- The represented-object chosen short complex is exact after both covariant
and contravariant preadditive Yoneda probes. -/
theorem yonedaExact_pair
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (object.shortComplex.map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      (object.shortComplex.op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  object.representative.normalized_yonedaExact_pair
    leftProbe
    rightProbe

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
