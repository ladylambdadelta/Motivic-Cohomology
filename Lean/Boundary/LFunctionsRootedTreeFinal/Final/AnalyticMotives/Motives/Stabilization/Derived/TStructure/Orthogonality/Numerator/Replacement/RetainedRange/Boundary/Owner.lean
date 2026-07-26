import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Nonboundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Assembly

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The lower boundary inclusion induces an isomorphism on the homology object
of the displayed boundary short complexes. -/
theorem source_truncLEInclusion_boundary_homologyMap_isIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    IsIso
      (ShortComplex.homologyMap
        ((shortComplexFunctor'
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          (-1 : ℤ)
          0
          1).map
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex))) := by
  let actualMap :
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        (-1 : ℤ)
        0
        1).obj
          (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
            0
            sourceComplex)) ⟶
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        (-1 : ℤ)
        0
        1).obj sourceComplex) :=
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      (-1 : ℤ)
      0
      1).map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex))
  let modelMap :
      TraceAnalyticDerivedMotiveCategory
        .leftBoundaryModel
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
            1).obj
              (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
                0
                sourceComplex)).X₃) ⟶
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        (-1 : ℤ)
        0
        1).obj sourceComplex) :=
    TraceAnalyticDerivedMotiveCategory
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
              .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)).τ₃)
  letI :
      ShortComplex.QuasiIso modelMap :=
    TraceAnalyticDerivedMotiveCategory
      .leftBoundaryInclusion_quasiIso
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
          1).obj
            (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
              0
              sourceComplex)).X₃)
        (((shortComplexFunctor'
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          (-1 : ℤ)
          0
          1).map
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)).τ₃)
  let arrowIso :
      Arrow.mk actualMap ≅ Arrow.mk modelMap :=
    TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_arrow_iso_leftBoundaryInclusion
        sourceComplex
  let actualQuasiIso :
      ShortComplex.QuasiIso actualMap :=
    ShortComplex.quasiIso_of_arrow_mk_iso
      modelMap
      actualMap
      arrowIso.symm
  (ShortComplex.quasiIso_iff actualMap).mp actualQuasiIso

/-- The boundary short-complex map for the lower truncation inclusion is a
quasi-isomorphism.  This is the exact remaining lower-boundary homology
calculation: the middle map is the lower-boundary cycles inclusion obtained
by dualizing the opposite upper opcycles projection. -/
theorem source_truncLEInclusion_boundary_shortComplex_quasiIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ShortComplex.QuasiIso
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        (-1 : ℤ)
        0
        1).map
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)) :=
  (ShortComplex.quasiIso_iff
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      (-1 : ℤ)
      0
      1).map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex))).mpr
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_homologyMap_isIso
        sourceComplex)

/-- At the lower boundary degree, the lower-truncation inclusion induces an
isomorphism on homology. -/
theorem exactAt_source_truncLEInclusion_quasiIsoAt_boundary_zero
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    QuasiIsoAt
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)
      0 :=
  let sourceInclusion :
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
          0
          sourceComplex ⟶
        sourceComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex
  let previousRelation :
      (ComplexShape.up ℤ).Rel (-1 : ℤ) 0 :=
    rfl
  let nextRelation :
      (ComplexShape.up ℤ).Rel 0 1 :=
    rfl
  (_root_.quasiIsoAt_iff'
    sourceInclusion
    (-1 : ℤ)
    0
    1
    ((ComplexShape.up ℤ).prev_eq' previousRelation)
    ((ComplexShape.up ℤ).next_eq' nextRelation)).mpr
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_shortComplex_quasiIso
        sourceComplex)

/-- The upper boundary projection induces an isomorphism on the homology object
of the displayed boundary short complexes. -/
theorem target_truncGEProjection_boundary_homologyMap_isIso
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    IsIso
      (ShortComplex.homologyMap
        ((shortComplexFunctor'
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          0
          1
          2).map
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncGEProjectionMap 1 targetComplex))) := by
  let actualMap :
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        0
        1
        2).obj targetComplex) ⟶
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        0
        1
        2).obj
          (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
            1
            targetComplex)) :=
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      0
      1
      2).map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncGEProjectionMap 1 targetComplex))
  let modelMap :
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        0
        1
        2).obj targetComplex) ⟶
      TraceAnalyticDerivedMotiveCategory
        .rightBoundaryModel
          (((shortComplexFunctor'
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
            2).obj targetComplex).homologyData.right) :=
    TraceAnalyticDerivedMotiveCategory
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
              .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)).τ₁)
  letI :
      ShortComplex.QuasiIso modelMap :=
    TraceAnalyticDerivedMotiveCategory
      .rightBoundaryProjection_quasiIso
        (((shortComplexFunctor'
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
          2).map
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)).τ₁)
  let arrowIso :
      Arrow.mk actualMap ≅ Arrow.mk modelMap :=
    TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_arrow_iso_rightBoundaryProjection
        targetComplex
  let actualQuasiIso :
      ShortComplex.QuasiIso actualMap :=
    ShortComplex.quasiIso_of_arrow_mk_iso
      modelMap
      actualMap
      arrowIso.symm
  (ShortComplex.quasiIso_iff actualMap).mp actualQuasiIso

/-- The boundary short-complex map for the upper truncation projection is a
quasi-isomorphism.  This is the exact remaining upper-boundary homology
calculation: the middle map is the opcycles quotient, and the target
short-complex homology is the same kernel after the transported opcycles
differential. -/
theorem target_truncGEProjection_boundary_shortComplex_quasiIso
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    ShortComplex.QuasiIso
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        0
        1
        2).map
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)) :=
  (ShortComplex.quasiIso_iff
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      0
      1
      2).map
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncGEProjectionMap 1 targetComplex))).mpr
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_homologyMap_isIso
        targetComplex)

/-- At the upper boundary degree, the upper-truncation projection induces an
isomorphism on homology. -/
theorem exactAt_target_truncGEProjection_quasiIsoAt_boundary_one
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    QuasiIsoAt
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)
      1 :=
  let targetProjection :
      targetComplex ⟶
        TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
          1
          targetComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGEProjectionMap 1 targetComplex
  let previousRelation :
      (ComplexShape.up ℤ).Rel 0 1 :=
    rfl
  let nextRelation :
      (ComplexShape.up ℤ).Rel 1 2 :=
    rfl
  (_root_.quasiIsoAt_iff'
    targetProjection
    0
    1
    2
    ((ComplexShape.up ℤ).prev_eq' previousRelation)
    ((ComplexShape.up ℤ).next_eq' nextRelation)).mpr
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_shortComplex_quasiIso
        targetComplex)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
