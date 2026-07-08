import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Family.Projections.ShortComplex.Owner

/-!
# Short-complex map projections from the family boundary handoff

This file peels the family boundary handoff short-complex certificate into
the two maps and the zero field.
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

/-- The family boundary handoff identifies the first short-complex map with
the chosen first truncation map. -/
theorem family_boundaryHandoff_shortComplex_f
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
    object.shortComplex.f = object.firstMap := by
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
      object).right.right.right.right.left

/-- The family boundary handoff identifies the second short-complex map with
the chosen second truncation map. -/
theorem family_boundaryHandoff_shortComplex_g
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
    object.shortComplex.g = object.secondMap := by
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
      object).right.right.right.right.right.left

/-- The family boundary handoff identifies the short-complex zero field with
the chosen first zero-composition law. -/
theorem family_boundaryHandoff_shortComplex_zero
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
    object.shortComplex.zero = object.firstMap_comp_secondMap := by
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
      object).right.right.right.right.right.right.left

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
