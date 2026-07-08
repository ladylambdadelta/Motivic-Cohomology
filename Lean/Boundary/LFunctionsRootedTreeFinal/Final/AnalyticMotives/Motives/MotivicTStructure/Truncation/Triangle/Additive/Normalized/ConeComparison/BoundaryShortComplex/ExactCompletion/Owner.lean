import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Owner

/-!
# Exact-completion boundary cokernel for the normalized cone comparison

The represented presheaf of the analytic opcycles quotient need not be the
pointwise cokernel of the represented incoming differential.  The exact
completion boundary object is therefore defined as the actual cokernel in the
analytic presheaf abelian envelope.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- The exact-completion boundary object: the actual presheaf cokernel of the
represented incoming analytic differential at the truncation cut. -/
def exactCompletionNormalizedConeComparisonBoundaryCokernel
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveAbelianEnvelope :=
  cokernel
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut))

/-- The quotient map from the represented cut-degree object to the
exact-completion boundary cokernel. -/
def exactCompletionNormalizedConeComparisonBoundaryProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj (complex.X cut) ⟶
      TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryCokernel
          cut
          complex :=
  cokernel.π
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut))

/-- The exact-completion boundary short complex attached to the incoming
analytic differential at the truncation cut. -/
def exactCompletionNormalizedConeComparisonBoundaryShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
  ShortComplex.mk
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut))
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProjection
        cut
        complex)
    (cokernel.condition
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d (cut - 1) cut)))

/-- The first object of the exact-completion boundary short complex is the
represented object in degree `cut - 1`. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex
        cut
        complex).X₁ =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X (cut - 1)) :=
  rfl

/-- The middle object of the exact-completion boundary short complex is the
represented object in degree `cut`. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex
        cut
        complex).X₂ =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X cut) :=
  rfl

/-- The third object of the exact-completion boundary short complex is the
actual cokernel presheaf of the represented incoming differential. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex
        cut
        complex).X₃ =
      TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryCokernel
          cut
          complex :=
  rfl

/-- The second map of the exact-completion boundary short complex is the
cokernel projection in the analytic presheaf abelian envelope. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex
        cut
        complex).g =
      TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryProjection
          cut
          complex :=
  rfl

/-- The exact-completion boundary projection is a cokernel of the represented
incoming analytic differential. -/
theorem exactCompletionNormalizedConeComparisonBoundaryProjection_isCokernel
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    IsColimit
      (CokernelCofork.ofπ
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryProjection
            cut
            complex)
        (cokernel.condition
          ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
            (complex.d (cut - 1) cut)))) :=
  cokernelIsCokernel
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut))

/-- The exact-completion boundary short complex is exact, with no probe
exactness or splitting hypothesis: its second map is the actual cokernel in
the analytic presheaf abelian envelope. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplex_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex
        cut
        complex).Exact :=
  let shortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
  letI :
      shortComplex.HasHomology :=
    CategoryWithHomology.hasHomology shortComplex
  ShortComplex.exact_of_g_is_cokernel
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProjection_isCokernel
        cut
        complex)

/-- The analytic normalized cone boundary component factors through the
exact-completion boundary cokernel.  This is the canonical comparison from the
cokernel-presented boundary object to the represented analytic upper-boundary
object. -/
def exactCompletionNormalizedConeComparisonBoundaryToRepresented
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryCokernel
          cut
          complex ⟶
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
          cut) :=
  cokernel.desc
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut))
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      ((((CochainComplex.mappingCone.inr
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedCochainDecompositionLowerMap
              cut
              complex)).f cut) ≫
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap
            cut
            complex).f cut)))
    (let incoming :
        complex.X (cut - 1) ⟶ complex.X cut :=
      complex.d (cut - 1) cut
    let boundary :
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
    let represented :
        TraceAnalyticAdditiveCategoryObject ⥤
          TraceAnalyticAdditiveAbelianEnvelope :=
      TraceAnalyticAdditiveAbelianEnvelope.yoneda
    let zeroInAdditive :
        incoming ≫ boundary = 0 :=
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary).zero
    let mapComposite :
        represented.map incoming ≫ represented.map boundary =
          represented.map (incoming ≫ boundary) :=
      Eq.symm (represented.map_comp incoming boundary)
    let mapZeroEquation :
        represented.map (incoming ≫ boundary) =
          represented.map 0 :=
      congrArg
        (fun morphism => represented.map morphism)
        zeroInAdditive
    let preservesZero :
        represented.map (0 : complex.X (cut - 1) ⟶
          (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) =
          0 :=
      represented.map_zero
    Eq.trans mapComposite
      (Eq.trans mapZeroEquation preservesZero))

/-- The exact-completion comparison is characterized by the cokernel
projection followed by the represented normalized cone boundary component. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_fac
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryProjection
          cut
          complex ≫
      TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((((CochainComplex.mappingCone.inr
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedCochainDecompositionLowerMap
                cut
                complex)).f cut) ≫
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap
              cut
              complex).f cut)) :=
  cokernel.π_desc
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      (complex.d (cut - 1) cut))
    ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
      ((((CochainComplex.mappingCone.inr
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedCochainDecompositionLowerMap
              cut
              complex)).f cut) ≫
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap
            cut
            complex).f cut)))
    (let incoming :
        complex.X (cut - 1) ⟶ complex.X cut :=
      complex.d (cut - 1) cut
    let boundary :
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
    let represented :
        TraceAnalyticAdditiveCategoryObject ⥤
          TraceAnalyticAdditiveAbelianEnvelope :=
      TraceAnalyticAdditiveAbelianEnvelope.yoneda
    let zeroInAdditive :
        incoming ≫ boundary = 0 :=
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary).zero
    let mapComposite :
        represented.map incoming ≫ represented.map boundary =
          represented.map (incoming ≫ boundary) :=
      Eq.symm (represented.map_comp incoming boundary)
    let mapZeroEquation :
        represented.map (incoming ≫ boundary) =
          represented.map 0 :=
      congrArg
        (fun morphism => represented.map morphism)
        zeroInAdditive
    let preservesZero :
        represented.map (0 : complex.X (cut - 1) ⟶
          (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) =
          0 :=
      represented.map_zero
    Eq.trans mapComposite
      (Eq.trans mapZeroEquation preservesZero))

/-- The canonical comparison from the exact-completion boundary short complex
to the represented analytic boundary short complex.  It is identity on the two
incoming represented terms and the cokernel comparison on the boundary term. -/
def exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryShortComplex
          cut
          complex ⟶
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary :=
  ShortComplex.homMk
    (𝟙 ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
      (complex.X (cut - 1))))
    (𝟙 ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
      (complex.X cut)))
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryToRepresented
        cut
        complex
        tail
        htail
        hboundary)
    (Eq.trans
      (Category.id_comp
        ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
          (complex.d (cut - 1) cut)))
      (Eq.symm
        (Category.comp_id
          ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
            (complex.d (cut - 1) cut)))))
    (Eq.trans
      (Category.id_comp
        ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
          ((((CochainComplex.mappingCone.inr
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedCochainDecompositionLowerMap
                  cut
                  complex)).f cut) ≫
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap
                cut
                complex).f cut))))
      (Eq.symm
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented_fac
            cut
            complex
            tail
            htail
            hboundary)))

/-- The comparison morphism is identity on the represented source degree. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented
        cut
        complex
        tail
        htail
        hboundary).τ₁ =
      𝟙 ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X (cut - 1))) :=
  rfl

/-- The comparison morphism is identity on the represented boundary source
degree. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented
        cut
        complex
        tail
        htail
        hboundary).τ₂ =
      𝟙 ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        (complex.X cut)) :=
  rfl

/-- The comparison morphism is the cokernel comparison on the boundary term. -/
theorem exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryShortComplexToRepresented
        cut
        complex
        tail
        htail
        hboundary).τ₃ =
      TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
