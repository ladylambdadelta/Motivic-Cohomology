import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.QuotientFunctor.ShortComplex.YonedaExact.Paired.Owner

/-!
# Certificate for homotopy quotient short complexes

This file bundles the maps, zero field, zero-composition laws, and paired
preadditive Yoneda exactness of the short complex attached to a homotopy
quotient image.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The short complex attached to a homotopy quotient image has the expected
maps, zero field, all three quotient-image zero-composition laws, and paired
preadditive Yoneda exactness. -/
theorem homotopyQuotientFunctor_shortComplex_certificate
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex
        triangle
        distinguished).f =
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁ ∧
      (TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_shortComplex
          triangle
          distinguished).g =
        ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
          .mapTriangle.obj triangle).mor₂ ∧
        (TraceAnalyticStableInfinityCategory
          .homotopyQuotientFunctor_shortComplex
            triangle
            distinguished).zero =
          TraceAnalyticStableInfinityCategory
            .homotopyQuotientFunctor_distinguished_mor₁_comp_mor₂
              triangle
              distinguished ∧
          ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
              .mapTriangle.obj triangle).mor₁ ≫
            ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
              .mapTriangle.obj triangle).mor₂ =
              0 ∧
            ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
                .mapTriangle.obj triangle).mor₂ ≫
              ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
                .mapTriangle.obj triangle).mor₃ =
                0 ∧
              ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
                  .mapTriangle.obj triangle).mor₃ ≫
                (((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
                  .mapTriangle.obj triangle).mor₁)⟦(1 : ℤ)⟧' =
                  0 ∧
                ((TraceAnalyticStableInfinityCategory
                  .homotopyQuotientFunctor_shortComplex
                    triangle
                    distinguished).map
                    (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                  ((TraceAnalyticStableInfinityCategory
                    .homotopyQuotientFunctor_shortComplex
                      triangle
                      distinguished).op.map
                      (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor_shortComplex_f triangle distinguished)
    (And.intro
      (TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctor_shortComplex_g triangle distinguished)
      (And.intro
        (TraceAnalyticStableInfinityCategory
          .homotopyQuotientFunctor_shortComplex_zero triangle distinguished)
        (And.intro
          (TraceAnalyticStableInfinityCategory
            .homotopyQuotientFunctor_distinguished_mor₁_comp_mor₂
              triangle
              distinguished)
          (And.intro
            (TraceAnalyticStableInfinityCategory
              .homotopyQuotientFunctor_distinguished_mor₂_comp_mor₃
                triangle
                distinguished)
            (And.intro
              (TraceAnalyticStableInfinityCategory
                .homotopyQuotientFunctor_distinguished_mor₃_comp_shift_mor₁
                  triangle
                  distinguished)
              (TraceAnalyticStableInfinityCategory
                .homotopyQuotientFunctor_pairedYonedaShortComplex_exact
                  triangle
                  distinguished
                  leftProbe
                  rightProbe)))))

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
