import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.BoundaryReduction.Owner

/-!
# Boundary cancellation for restricted-core projection commutativity

The boundary equality reduces to the standard opcycles formula
`pOpcycles ≫ fromOpcycles = d` at the embedded source and target degrees.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The embedded-degree opcycles cancellation used in the boundary case of
restricted-core projection commutativity. -/
theorem truncGEProjectionCoreBoundary_p_fromOpcycles
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι) :
    complex.pOpcycles (embedding.f source) ≫
        complex.fromOpcycles
          (embedding.f source)
          (embedding.f target) =
      complex.d (embedding.f source) (embedding.f target) :=
  _root_.HomologicalComplex.p_fromOpcycles
    complex
    (embedding.f source)
    (embedding.f target)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
