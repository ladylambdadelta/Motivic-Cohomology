import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Family.Projections.Owner

/-!
# Short-complex projections from the family boundary handoff

This file peels the family boundary handoff short-complex certificate into
endpoint, map, zero, and Yoneda exactness fields.
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

/-- The family boundary handoff identifies the first short-complex endpoint
with the normalized lower aisle inclusion. -/
theorem family_boundaryHandoff_shortComplex_X₁
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    object.shortComplex.X₁ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
        0).obj object.lowerAisleObjectZero := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    (family_boundaryHandoff_shortComplex_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe
      object).left

/-- The family boundary handoff identifies the middle short-complex endpoint
with the represented object. -/
theorem family_boundaryHandoff_shortComplex_X₂
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    object.shortComplex.X₂ = object.object := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    (family_boundaryHandoff_shortComplex_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe
      object).right.left

/-- The family boundary handoff identifies the third short-complex endpoint
with the normalized upper coaisle inclusion. -/
theorem family_boundaryHandoff_shortComplex_X₃
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    object.shortComplex.X₃ =
      (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
        1).obj object.upperCoaisleObjectOne := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    (family_boundaryHandoff_shortComplex_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe
      object).right.right.left

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
