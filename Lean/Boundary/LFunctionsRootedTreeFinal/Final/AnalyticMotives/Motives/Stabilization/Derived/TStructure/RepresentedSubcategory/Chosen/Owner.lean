import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Normalized.Exactness.Certificate.Owner

/-!
# Chosen representatives in the represented truncation subcategory

This file chooses the concrete cut-`1` Yoneda representative carried by a
represented truncation object and exposes its normalized truncation data.
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

/-- A chosen concrete cut-`1` Yoneda representative for a represented
truncation object. -/
def representative
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticMotivicTStructure
      .YonedaTruncationRepresentative 1 object.object :=
  Classical.choice object.membership

/-- The normalized lower aisle object attached to a represented truncation
object. -/
def lowerAisleObjectZero
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle 0 :=
  object.representative.lowerAisleObjectZero

/-- The normalized upper coaisle object attached to a represented truncation
object. -/
def upperCoaisleObjectOne
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle 1 :=
  object.representative.upperCoaisleObjectOne

/-- The normalized explicit truncation short complex attached to a represented
truncation object. -/
def shortComplex
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    ShortComplex TraceAnalyticDerivedMotiveCategory :=
  object.representative.shortComplex

/-- The normalized exact-sequence certificate for the chosen representative of
a represented truncation object. -/
theorem normalized_exactSequence_certificate
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
  object.representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
