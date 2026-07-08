import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Owner

/-!
# Stable short complex of the truncation decomposition

This file maps the concrete cochain-level truncation decomposition
`truncLE(cut - 1,K) ⟶ K ⟶ truncGE(cut,K)` through the additive homotopy
quotient and then the stable Verdier quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The stable image of the normalized cochain truncation-decomposition short
complex. -/
def stableCochainDecompositionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticStableMotiveCategory :=
  (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
    cut
    complex).map
      (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
        TraceAnalyticStableMotiveCategory.quotientFunctor)

/-- The first object of the stable truncation-decomposition short complex is
the stable image of the paired lower truncation. -/
theorem stableCochainDecompositionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex)) :=
  rfl

/-- The second object of the stable truncation-decomposition short complex is
the stable image of the original complex. -/
theorem stableCochainDecompositionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The third object of the stable truncation-decomposition short complex is
the stable upper truncation. -/
theorem stableCochainDecompositionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  rfl

/-- The first map of the stable truncation-decomposition short complex is the
stable image of the paired lower inclusion. -/
theorem stableCochainDecompositionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).f =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          (TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
            cut
            complex)) :=
  rfl

/-- The second map of the stable truncation-decomposition short complex is the
stable upper truncation projection. -/
theorem stableCochainDecompositionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap
        cut
        complex :=
  rfl

/-- The stable lower truncation map followed by the stable upper projection is
zero. -/
theorem stableCochainDecompositionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
