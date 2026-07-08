import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Existence.Represented.Chosen.Normalized.Exactness.Certificate.Owner

/-!
# Projections from the normalized truncation exact-sequence certificate

This file exposes the endpoint, map, and paired-exactness fields of the
normalized chosen truncation exact-sequence certificate.
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

/-- The first endpoint of the normalized exact sequence is the lower aisle
inclusion. -/
theorem normalized_exactSequence_X₁
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    representative.shortComplex.X₁ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion 0).obj
        representative.lowerAisleObjectZero :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).left

/-- The middle endpoint of the normalized exact sequence is the represented
object. -/
theorem normalized_exactSequence_X₂
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    representative.shortComplex.X₂ = object :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).right.left

/-- The third endpoint of the normalized exact sequence is the upper coaisle
inclusion. -/
theorem normalized_exactSequence_X₃
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    representative.shortComplex.X₃ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion 1).obj
        representative.upperCoaisleObjectOne :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).right.right.left

/-- The first map of the normalized exact sequence is the chosen first
truncation map. -/
theorem normalized_exactSequence_firstMap
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    representative.shortComplex.f = representative.firstMap :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).right.right.right.left

/-- The second map of the normalized exact sequence is the chosen second
truncation map. -/
theorem normalized_exactSequence_secondMap
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    representative.shortComplex.g = representative.secondMap :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).right.right.right.right.left

/-- The normalized exact sequence is exact after covariant preadditive Yoneda
evaluation. -/
theorem normalized_exactSequence_coyonedaExact
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (representative.shortComplex.map
      (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).right.right.right.right.right.left

/-- The normalized exact sequence is exact after contravariant preadditive
Yoneda evaluation. -/
theorem normalized_exactSequence_yonedaExact
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    (representative.shortComplex.op.map
      (preadditiveYoneda.obj rightProbe)).Exact :=
  (representative.normalized_exactSequence_certificate
    leftProbe
    rightProbe).right.right.right.right.right.right

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary
