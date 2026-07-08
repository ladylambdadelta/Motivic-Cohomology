import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Components.Owner

/-!
# Boundary vanishing for upper truncation projection

The upper truncation projection uses the opcycles quotient at the lower
boundary of the embedded tail.  The incoming differential into that boundary
vanishes after `pOpcycles`; this is the concrete lift condition needed to
extend the restricted projection across the zero side of the truncation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The incoming differential into a GE boundary is killed by the opcycles
quotient used in the truncation projection. -/
theorem truncGEProjectionBoundary_d_pOpcycles
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι)
    (incoming : ι')
    (hboundary : embedding.BoundaryGE tail)
    (hincoming : ambientShape.Rel incoming (embedding.f tail)) :
    complex.d incoming (embedding.f tail) ≫
        complex.pOpcycles (embedding.f tail) =
      0 :=
  _root_.HomologicalComplex.d_pOpcycles
    complex
    incoming
    (embedding.f tail)

/-- Analytic integer specialization of boundary opcycles vanishing. -/
theorem additiveTruncGEProjectionBoundary_d_pOpcycles
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (incoming : ℤ)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hincoming :
      (ComplexShape.up ℤ).Rel
        incoming
        ((TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail)) :
    complex.d
          incoming
          ((TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail) ≫
        complex.pOpcycles
          ((TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail) =
      0 :=
  TraceAnalyticMotivicTStructure.truncGEProjectionBoundary_d_pOpcycles
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    tail
    incoming
    hboundary
    hincoming

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
