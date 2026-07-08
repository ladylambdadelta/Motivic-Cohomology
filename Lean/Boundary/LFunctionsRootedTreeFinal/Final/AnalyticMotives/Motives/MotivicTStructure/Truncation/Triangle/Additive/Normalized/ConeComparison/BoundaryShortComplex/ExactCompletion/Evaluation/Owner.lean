import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.AbelianEnvelope.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Exact.Evaluation.Owner

/-!
# Probe evaluation of the exact-completion boundary short complex

The corrected exact-completion boundary object is an actual cokernel in the
analytic presheaf abelian envelope.  Evaluating at any analytic additive probe
therefore gives an exact Q-module short complex, and hence a concrete
range-kernel identity.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Probe evaluation of the exact-completion boundary short complex. -/
def exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    ShortComplex (ModuleCat Rat) :=
  (TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryShortComplex
      cut
      complex).map
        (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)

/-- The first Q-module in the evaluated exact-completion boundary sequence is
the represented hom module into degree `cut - 1`. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).X₁ =
      ModuleCat.of Rat
        (probe ⟶ complex.X (cut - 1)) :=
  rfl

/-- The middle Q-module in the evaluated exact-completion boundary sequence is
the represented hom module into degree `cut`. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).X₂ =
      ModuleCat.of Rat
        (probe ⟶ complex.X cut) :=
  rfl

/-- The boundary Q-module in the evaluated exact-completion sequence is the
probe value of the actual presheaf cokernel. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).X₃ =
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryCokernel
          cut
          complex).obj
        (Opposite.op probe) :=
  rfl

/-- The first map of the evaluated exact-completion boundary sequence is
precomposition with the incoming analytic differential. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).f =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d (cut - 1) cut)).app
        (Opposite.op probe) :=
  rfl

/-- The second map of the evaluated exact-completion boundary sequence is the
probe value of the actual cokernel projection. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).g =
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryProjection
          cut
          complex).app
        (Opposite.op probe) :=
  rfl

/-- Probe evaluation preserves exactness of the exact-completion boundary
sequence. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).Exact :=
  TraceAnalyticAdditiveAbelianEnvelope.evaluation_exact
    probe
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex_exact
        cut
        complex)

/-- Exactness of the evaluated exact-completion boundary sequence is
equivalent to equality of range and kernel. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_exact_iff_range_eq_ker
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe).Exact ↔
      LinearMap.range
          (TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
              cut
              complex
              probe).f =
        LinearMap.ker
          (TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
              cut
              complex
              probe).g :=
  ShortComplex.moduleCat_exact_iff_range_eq_ker
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        probe)

/-- The evaluated exact-completion boundary sequence has range equal to
kernel. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_range_eq_ker
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    LinearMap.range
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
            cut
            complex
            probe).f =
      LinearMap.ker
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
            cut
            complex
            probe).g :=
  ShortComplex.Exact.moduleCat_range_eq_ker
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex_exact
        cut
        complex
        probe)

/-- The evaluated comparison from the exact-completion boundary short complex
to the represented analytic boundary short complex. -/
def exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplex
          cut
          complex
          probe ⟶
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
          cut
          complex
          tail
          htail
          hboundary
          probe :=
  ShortComplex.homMk
    (𝟙 (ModuleCat.of Rat (probe ⟶ complex.X (cut - 1))))
    (𝟙 (ModuleCat.of Rat (probe ⟶ complex.X cut)))
    ((TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryToRepresented
        cut
        complex
        tail
        htail
        hboundary).app
        (Opposite.op probe))
    (Eq.trans
      (Category.id_comp
        (((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
          (complex.d (cut - 1) cut)).app
          (Opposite.op probe)))
      (Eq.symm
        (Category.comp_id
          (((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
            (complex.d (cut - 1) cut)).app
            (Opposite.op probe)))))
    (let boundary :
        complex.X cut ⟶
          (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut :=
      (((CochainComplex.mappingCone.inr
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedCochainDecompositionLowerMap
              cut
              complex)).f cut) ≫
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap
            cut
            complex).f cut)
    let representedBoundary :
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
            (complex.X cut) ⟶
          (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
            ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
              cut) :=
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map boundary
    let facAtProbe :
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryProjection
            cut
            complex).app (Opposite.op probe) ≫
          (TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              cut
              complex
              tail
              htail
              hboundary).app (Opposite.op probe) =
        representedBoundary.app (Opposite.op probe) :=
      congrArg
        (fun morphism => morphism.app (Opposite.op probe))
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented_fac
            cut
            complex
            tail
            htail
            hboundary)
    Eq.trans
      (Category.id_comp (representedBoundary.app (Opposite.op probe)))
      (Eq.symm facAtProbe))

/-- The evaluated comparison is identity on the first Q-module. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented
        cut
        complex
        tail
        htail
        hboundary
        probe).τ₁ =
      𝟙 (ModuleCat.of Rat (probe ⟶ complex.X (cut - 1))) :=
  rfl

/-- The evaluated comparison is identity on the middle Q-module. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented
        cut
        complex
        tail
        htail
        hboundary
        probe).τ₂ =
      𝟙 (ModuleCat.of Rat (probe ⟶ complex.X cut)) :=
  rfl

/-- The evaluated comparison is the probe value of the cokernel comparison on
the boundary Q-module. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProbeShortComplexToRepresented
        cut
        complex
        tail
        htail
        hboundary
        probe).τ₃ =
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary).app
        (Opposite.op probe) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
