import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RightUnitCancellation.Owner

/-!
# Right-side full normal form

This file combines the right-side restriction-identity reductions with the
unit-cancellation theorem, proving that the expanded right side is the common
normal form.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The expanded right-side expression reduces to the common normal form. -/
theorem truncGEProjectionCoreCommRightExpanded_eq_normalForm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreCommRightExpandedNormalForm
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
    (truncGEProjectionCoreCommRightExpanded_sourceRestrictionHomId
      embedding
      complex
      source
      target
      hrel)
    (Eq.trans
      (truncGEProjectionCoreCommRightExpanded_targetRestrictionInvId
        embedding
        complex
        source
        target
        hrel)
      (Eq.trans
        (Eq.symm
          (truncGEProjectionCoreCommRightUnitDecorated_eq
            embedding
            complex
            source
            target
            hrel))
        (truncGEProjectionCoreCommRightUnitDecorated_eq_normalForm
          embedding
          complex
          source
          target
          hrel)))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
