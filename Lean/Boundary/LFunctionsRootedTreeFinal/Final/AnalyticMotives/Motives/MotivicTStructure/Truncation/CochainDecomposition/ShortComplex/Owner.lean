import Mathlib.Algebra.Homology.ShortComplex.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.CompositeZero.Owner

/-!
# Short complex of the normalized cochain truncation decomposition

This file packages the proved cochain-level zero composite as a `ShortComplex`
in the category of additive analytic cochain complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The cochain short complex
`truncLE(cut - 1,K) ⟶ K ⟶ truncGE(cut,K)` attached to the normalized
truncation decomposition. -/
def additiveCochainDecompositionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticAdditiveCochainComplex :=
  ShortComplex.mk
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap_zero
      cut
      complex)

/-- The first object of the cochain truncation-decomposition short complex is
the paired lower truncation. -/
theorem additiveCochainDecompositionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
        cut
        complex :=
  rfl

/-- The middle object of the cochain truncation-decomposition short complex is
the original complex. -/
theorem additiveCochainDecompositionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
      cut
      complex).X₂ =
      complex :=
  rfl

/-- The third object of the cochain truncation-decomposition short complex is
the upper truncation. -/
theorem additiveCochainDecompositionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.additiveTruncGE
        cut
        complex :=
  rfl

/-- The first map of the cochain truncation-decomposition short complex is the
paired lower inclusion. -/
theorem additiveCochainDecompositionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
      cut
      complex).f =
      TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
        cut
        complex :=
  rfl

/-- The second map of the cochain truncation-decomposition short complex is the
upper projection. -/
theorem additiveCochainDecompositionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
        cut
        complex :=
  rfl

/-- The short-complex zero field is the cochain-level composite-zero theorem. -/
theorem additiveCochainDecompositionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
          cut
          complex).g =
      0 :=
  TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap_zero
    cut
    complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
