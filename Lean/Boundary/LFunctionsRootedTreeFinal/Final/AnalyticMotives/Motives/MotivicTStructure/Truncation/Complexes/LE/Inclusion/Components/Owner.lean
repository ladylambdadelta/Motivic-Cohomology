import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Owner

/-!
# Degreewise lower truncation inclusion components

The lower truncation is defined by applying upper truncation to the opposite
complex and unopping back.  Its inclusion into the original complex is therefore
the unop of the upper projection component on the opposite complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Opposite

/-- The degreewise component of the concrete inclusion
`truncLE(cut, K) ⟶ K`, defined by duality from the upper projection component
of the opposite complex. -/
def TraceAnalyticMotivicTStructure.additiveTruncLEInclusionComponent
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).X degree ⟶
      complex.X degree :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  (TraceAnalyticMotivicTStructure.truncGEProjectionComponent
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
    (HomologicalComplex.op complex)
    degree).unop

/-- The lower inclusion component is the unop of the opposite upper projection
component. -/
theorem TraceAnalyticMotivicTStructure.additiveTruncLEInclusionComponent_eq_unop
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.additiveTruncLEInclusionComponent
        cut
        complex
        degree =
      (letI :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
        TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
      (TraceAnalyticMotivicTStructure.truncGEProjectionComponent
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
        (HomologicalComplex.op complex)
        degree).unop) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
