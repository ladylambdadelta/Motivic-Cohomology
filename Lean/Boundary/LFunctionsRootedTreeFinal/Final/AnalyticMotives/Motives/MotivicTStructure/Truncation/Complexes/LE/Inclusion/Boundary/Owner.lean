import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Inclusion.Components.Owner

/-!
# Boundary vanishing for lower truncation inclusion

The lower truncation inclusion is dual to the upper projection on the opposite
complex.  Its boundary vanishing is therefore the unopposite form of the
upper-boundary opcycles vanishing statement.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Opposite

namespace TraceAnalyticMotivicTStructure

/-- The lower-boundary vanishing statement obtained by applying the upper
projection boundary theorem to the opposite complex and unopping. -/
theorem additiveTruncLEInclusionBoundary_unop_d_pOpcycles
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (outgoing : ℤ)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail)
    (houtgoing :
      (ComplexShape.up ℤ).symm.Rel
        outgoing
        ((TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.f tail)) :
    (((HomologicalComplex.op complex).d
          outgoing
          ((TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.f tail) ≫
        (HomologicalComplex.op complex).pOpcycles
          ((TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.f tail)).unop) =
      0 :=
  congrArg
    Quiver.Hom.unop
    (TraceAnalyticMotivicTStructure.truncGEProjectionBoundary_d_pOpcycles
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
      (HomologicalComplex.op complex)
      tail
      outgoing
      hboundary
      houtgoing)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
