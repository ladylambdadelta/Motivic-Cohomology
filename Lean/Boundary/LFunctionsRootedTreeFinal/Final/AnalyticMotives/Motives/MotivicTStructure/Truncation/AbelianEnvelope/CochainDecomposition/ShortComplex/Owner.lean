import Mathlib.Algebra.Homology.ShortComplex.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.CompositeZero.Owner

/-!
# Short complex of the abelian-envelope truncation decomposition

This file packages the abelian-envelope zero composite as a `ShortComplex`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The abelian-envelope short complex
`truncLE(cut - 1,K) ⟶ K ⟶ truncGE(cut,K)` attached to the normalized
truncation decomposition. -/
def abelianEnvelopeIntrinsicCochainDecompositionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    ShortComplex TraceAnalyticAbelianCochainComplex :=
  ShortComplex.mk
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionLowerMap cut complex)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionUpperMap cut complex)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionCompositeMap_zero cut complex)

/-- The first object of the abelian-envelope truncation-decomposition short
complex is the paired lower truncation. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex).X₁ =
      TraceAnalyticMotivicTStructure.abelianEnvelopeDecompositionTruncLE
        cut
        complex :=
  rfl

/-- The middle object of the abelian-envelope truncation-decomposition short
complex is the original complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex).X₂ =
      complex :=
  rfl

/-- The third object of the abelian-envelope truncation-decomposition short
complex is the upper truncation. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex).X₃ =
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex :=
  rfl

/-- The first map of the abelian-envelope truncation-decomposition short
complex is the paired lower inclusion. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex).f =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionLowerMap cut complex :=
  rfl

/-- The second map of the abelian-envelope truncation-decomposition short
complex is the upper projection. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex).g =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionUpperMap cut complex :=
  rfl

/-- The short-complex zero field is the abelian-envelope cochain-level
composite-zero theorem. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex).f ≫
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex).g =
      0 :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionCompositeMap_zero cut complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
