import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.Owner

/-!
# Restricted-core upper projection map

This file assembles the restricted-core component formulas into an actual chain
map `K.restriction e ⟶ K.truncGE' e`.  The commutativity field is supplied by
the boundary and nonboundary normal-form theorems.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Componentwise commutativity for the restricted-core upper projection. -/
theorem truncGEProjectionCoreComponent_comm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreComponent embedding complex source ≫
        (complex.truncGE' embedding).d source target =
      (complex.restriction embedding).d source target ≫
        truncGEProjectionCoreComponent embedding complex target :=
  let targetNotBoundary : ¬ embedding.BoundaryGE target :=
    embedding.not_boundaryGE_next hrel
  if hsource : embedding.BoundaryGE source then
    let leftComponent :
        truncGEProjectionCoreComponent embedding complex source ≫
            (complex.truncGE' embedding).d source target =
          truncGEProjectionCoreBoundaryCommLeft
            embedding
            complex
            source
            target
            hsource :=
      congrArg
        (fun component =>
          component ≫ (complex.truncGE' embedding).d source target)
        (truncGEProjectionCoreComponent_of_boundary
          embedding
          complex
          source
          hsource)
    let rightComponent :
        truncGEProjectionCoreBoundaryCommRight
            embedding
            complex
            source
            target
            hrel =
          (complex.restriction embedding).d source target ≫
            truncGEProjectionCoreComponent embedding complex target :=
      Eq.symm
        (congrArg
          (fun component =>
            (complex.restriction embedding).d source target ≫ component)
          (truncGEProjectionCoreComponent_of_not_boundary
            embedding
            complex
            target
            targetNotBoundary))
    Eq.trans
      leftComponent
      (Eq.trans
        (truncGEProjectionCoreBoundaryComm
          embedding
          complex
          source
          target
          hrel
          hsource)
        rightComponent)
  else
    let leftComponent :
        truncGEProjectionCoreComponent embedding complex source ≫
            (complex.truncGE' embedding).d source target =
          truncGEProjectionCoreNonboundaryCommLeft
            embedding
            complex
            source
            target
            hsource :=
      congrArg
        (fun component =>
          component ≫ (complex.truncGE' embedding).d source target)
        (truncGEProjectionCoreComponent_of_not_boundary
          embedding
          complex
          source
          hsource)
    let rightComponent :
        truncGEProjectionCoreNonboundaryCommRight
            embedding
            complex
            source
            target
            hrel =
          (complex.restriction embedding).d source target ≫
            truncGEProjectionCoreComponent embedding complex target :=
      Eq.symm
        (congrArg
          (fun component =>
            (complex.restriction embedding).d source target ≫ component)
          (truncGEProjectionCoreComponent_of_not_boundary
            embedding
            complex
            target
            targetNotBoundary))
    Eq.trans
      leftComponent
      (Eq.trans
        (truncGEProjectionCoreNonboundaryComm
          embedding
          complex
          source
          target
          hrel
          hsource)
        rightComponent)

/-- The restricted-core upper projection chain map
`K.restriction e ⟶ K.truncGE' e`. -/
def truncGEProjectionCoreMap
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree] :
    complex.restriction embedding ⟶ complex.truncGE' embedding where
  f tail := truncGEProjectionCoreComponent embedding complex tail
  comm' source target hrel :=
    truncGEProjectionCoreComponent_comm
      embedding
      complex
      source
      target
      hrel

/-- Projection formula for the restricted-core upper projection map. -/
theorem truncGEProjectionCoreMap_f
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι) :
    (truncGEProjectionCoreMap embedding complex).f tail =
      truncGEProjectionCoreComponent embedding complex tail :=
  rfl

/-- Analytic integer specialization of the restricted-core upper projection
chain map. -/
def additiveTruncGEProjectionCoreMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    complex.restriction
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) ⟶
      complex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut) :=
  TraceAnalyticMotivicTStructure.truncGEProjectionCoreMap
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
