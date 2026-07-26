import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Models
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Components.Owner

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The displayed upper-boundary short-complex map. -/
def targetBoundaryShortComplexMap
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
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

/-- The model map for the displayed upper-boundary map. -/
def targetRightBoundaryModelMap
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
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
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex).τ₁

/-- The displayed lower-boundary short-complex map. -/
def sourceBoundaryShortComplexMap
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
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

/-- The model map for the displayed lower-boundary map. -/
def sourceLeftBoundaryModelMap
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
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
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex).τ₃

/-- The upper boundary target keeps the left zero-side object. -/
def target_truncGEProjection_boundary_target_leftIso
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.X₁ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex)).right.X₁ :=
  Iso.refl
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.X₁

/-- Upper boundary middle-object transport through concrete and chosen opcycles. -/
def target_truncGEProjection_boundary_target_middleIso
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.X₂ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex)).right.X₂ :=
  let tail : ℕ := 0
  let hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        (1 : ℤ) :=
    Eq.trans rfl (Int.add_zero 1)
  let hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail :=
    (ComplexShape.boundaryGE_embeddingUpIntGE_iff 1 tail).2 rfl
  let displayedShortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      0
      1
      2).obj targetComplex)
  (_root_.HomologicalComplex.truncGEXIsoOpcycles
    targetComplex
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
    hdegree
    hboundary) ≪≫
    targetComplex.opcyclesIsoSc'
      0
      1
      2
      rfl
      rfl ≪≫
    displayedShortComplex.homologyData.right.opcyclesIso

/-- The upper boundary right object is the next nonboundary truncation object. -/
def target_truncGEProjection_boundary_target_rightIso
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.X₃ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex)).right.X₃ :=
  let tail : ℕ := 1
  let htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).r (2 : ℤ) =
        some tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_r_eq_some_of_cut_le_degree
        1
        2
        (show (1 : ℤ) ≤ 2 from Int.reduceLE)
  let hdegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        (2 : ℤ) :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      htail
  let hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail :=
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).not_boundaryGE_next
      (ComplexShape.up_mk 0 1 rfl)
  _root_.HomologicalComplex.truncGEXIso
    targetComplex
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
    hdegree
    hboundary

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
