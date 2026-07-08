import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NonboundaryLeftNormalForm.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RightFullNormalForm.Owner

/-!
# Nonboundary restricted-core commutativity

This file proves the nonboundary case of the restricted-core upper projection
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

/-- The nonboundary right side reduces to the common normal form. -/
theorem truncGEProjectionCoreNonboundaryCommRight_eq_normalForm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreNonboundaryCommRight
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
    (truncGEProjectionCoreNonboundaryCommRight_eq_restrictionFormula
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

/-- Nonboundary case of restricted-core upper projection commutativity. -/
theorem truncGEProjectionCoreNonboundaryComm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target)
    (hsource : ¬ embedding.BoundaryGE source) :
    truncGEProjectionCoreNonboundaryCommLeft
        embedding
        complex
        source
        target
        hsource =
      truncGEProjectionCoreNonboundaryCommRight
        embedding
        complex
        source
        target
        hrel :=
  Eq.trans
    (truncGEProjectionCoreNonboundaryCommLeft_eq_normalForm
      embedding
      complex
      source
      target
      hrel
      hsource)
    (Eq.symm
      (truncGEProjectionCoreNonboundaryCommRight_eq_normalForm
        embedding
        complex
        source
        target
        hrel))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
