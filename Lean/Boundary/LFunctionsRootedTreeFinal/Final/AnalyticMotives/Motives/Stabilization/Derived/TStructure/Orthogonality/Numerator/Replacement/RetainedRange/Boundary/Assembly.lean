import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Upper
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Lower

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The concrete upper truncation boundary short-complex map is the
right-boundary model projection, up to the opcycles and next-degree truncation
isomorphisms. -/
theorem target_truncGEProjection_boundary_arrow_iso_rightBoundaryProjection
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    Arrow.mk
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        0
        1
        2).map
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)) ≅
    Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .rightBoundaryProjection
          (leftObject :=
            ((shortComplexFunctor'
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              0
              1
              2).obj
                (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
                  1
                  targetComplex)).X₁)
          ((shortComplexFunctor'
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            0
            1
            2).obj targetComplex)
          (((shortComplexFunctor'
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            0
            1
            2).obj targetComplex).homologyData.right)
          (((shortComplexFunctor'
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            0
            1
            2).map
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)).τ₁)) := by
  Arrow.isoMk'
    (TraceAnalyticDerivedMotiveCategory
      .targetBoundaryShortComplexMap targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .targetRightBoundaryModelMap targetComplex)
    (Iso.refl
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetBoundaryShortComplexMap targetComplex)).left)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_arrow_square_rightBoundaryProjection
        targetComplex)

/-- The concrete lower truncation boundary short-complex map is the
left-boundary model inclusion, up to the previous-degree and cycles truncation
isomorphisms. -/
theorem source_truncLEInclusion_boundary_arrow_iso_leftBoundaryInclusion
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    Arrow.mk
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        (-1 : ℤ)
        0
        1).map
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)) ≅
    Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .leftBoundaryInclusion
          ((shortComplexFunctor'
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            (-1 : ℤ)
            0
            1).obj sourceComplex)
          (((shortComplexFunctor'
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            (-1 : ℤ)
            0
            1).obj sourceComplex).homologyData.left)
          (((shortComplexFunctor'
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            (-1 : ℤ)
            0
            1).map
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)).τ₃)) := by
  Arrow.isoMk'
    (TraceAnalyticDerivedMotiveCategory
      .sourceBoundaryShortComplexMap sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .sourceLeftBoundaryModelMap sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
        sourceComplex)
    (Iso.refl
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceBoundaryShortComplexMap sourceComplex)).right)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_arrow_square_leftBoundaryInclusion
        sourceComplex)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
