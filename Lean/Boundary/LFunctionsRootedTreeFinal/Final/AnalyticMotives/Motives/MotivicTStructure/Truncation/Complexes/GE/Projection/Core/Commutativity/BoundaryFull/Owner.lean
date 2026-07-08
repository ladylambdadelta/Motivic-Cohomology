import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.BoundaryLeftNormalForm.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RightFullNormalForm.Owner

/-!
# Boundary restricted-core commutativity

This file proves the boundary case of the restricted-core upper projection
commutativity square by reducing both sides to the common normal form.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The boundary right side reduces to the common normal form. -/
theorem truncGEProjectionCoreBoundaryCommRight_eq_normalForm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreBoundaryCommRight
        embedding
        complex
        source
        target
        hrel =
      truncGEProjectionCoreCommNormalForm
        embedding
        complex
        source
        target
        hrel :=
  Eq.trans
    (truncGEProjectionCoreBoundaryCommRight_eq_restrictionFormula
      embedding
      complex
      source
      target
      hrel)
    (Eq.trans
      (Eq.symm
        (truncGEProjectionCoreCommRightExpandedNormalForm_eq
          embedding
          complex
          source
          target
          hrel))
      (truncGEProjectionCoreCommRightExpanded_eq_normalForm
        embedding
        complex
        source
        target
        hrel))

/-- Boundary case of restricted-core upper projection commutativity. -/
theorem truncGEProjectionCoreBoundaryComm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target)
    (hboundary : embedding.BoundaryGE source) :
    truncGEProjectionCoreBoundaryCommLeft
        embedding
        complex
        source
        target
        hboundary =
      truncGEProjectionCoreBoundaryCommRight
        embedding
        complex
        source
        target
        hrel :=
  Eq.trans
    (truncGEProjectionCoreBoundaryCommLeft_eq_normalForm
      embedding
      complex
      source
      target
      hrel
      hboundary)
    (Eq.symm
      (truncGEProjectionCoreBoundaryCommRight_eq_normalForm
        embedding
        complex
        source
        target
        hrel))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
