import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Owner

/-!
# Additive map formulas in the analytic Verdier quotient

The stable represented-morphism constructor is the Verdier quotient functor on
morphisms.  Since that functor is additive, it carries zero morphisms and sums
of additive-homotopy morphisms to the corresponding stable morphisms, and it
commutes with the additive-group scalar operations supplied by preadditivity.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The represented stable morphism of a zero additive-homotopy morphism is
zero. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_zero
    (source target : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticStableMotiveCategory.mapOf
        (0 : source ⟶ target) =
      (0 :
        TraceAnalyticStableMotiveCategory.objectOf source ⟶
          TraceAnalyticStableMotiveCategory.objectOf target) :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq
      (0 : source ⟶ target))
    (TraceAnalyticStableMotiveCategory.quotientFunctor.map_zero
      source
      target)

/-- The represented stable morphism of a sum of additive-homotopy morphisms is
the sum of the represented stable morphisms. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_add
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (left right : source ⟶ target) :
    TraceAnalyticStableMotiveCategory.mapOf (left + right) =
      TraceAnalyticStableMotiveCategory.mapOf left +
        TraceAnalyticStableMotiveCategory.mapOf right :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq (left + right))
    (Eq.trans
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_add)
      (congrArg₂
        (fun first second => first + second)
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq left))
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq right))))

/-- The represented stable morphism of the negative of an additive-homotopy
morphism is the negative of the represented stable morphism. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_neg
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticStableMotiveCategory.mapOf (-hom) =
      -TraceAnalyticStableMotiveCategory.mapOf hom :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq (-hom))
    (Eq.trans
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_neg)
      (congrArg
        Neg.neg
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq hom))))

/-- The represented stable morphism of a difference of additive-homotopy
morphisms is the difference of the represented stable morphisms. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_sub
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (left right : source ⟶ target) :
    TraceAnalyticStableMotiveCategory.mapOf (left - right) =
      TraceAnalyticStableMotiveCategory.mapOf left -
        TraceAnalyticStableMotiveCategory.mapOf right :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq (left - right))
    (Eq.trans
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_sub)
      (congrArg₂
        (fun first second => first - second)
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq left))
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq right))))

/-- The represented stable morphism of a natural-number multiple is the same
natural-number multiple of the represented stable morphism. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_nsmul
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (multiplicity : ℕ)
    (hom : source ⟶ target) :
    TraceAnalyticStableMotiveCategory.mapOf (multiplicity • hom) =
      multiplicity • TraceAnalyticStableMotiveCategory.mapOf hom :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq
      (multiplicity • hom))
    (Eq.trans
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_nsmul)
      (congrArg
        (fun mapped => multiplicity • mapped)
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq hom))))

/-- The represented stable morphism of an integer multiple is the same integer
multiple of the represented stable morphism. -/
theorem TraceAnalyticStableMotiveCategory.mapOf_zsmul
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (weight : ℤ)
    (hom : source ⟶ target) :
    TraceAnalyticStableMotiveCategory.mapOf (weight • hom) =
      weight • TraceAnalyticStableMotiveCategory.mapOf hom :=
  Eq.trans
    (TraceAnalyticStableMotiveCategory.mapOf_eq
      (weight • hom))
    (Eq.trans
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map_zsmul)
      (congrArg
        (fun mapped => weight • mapped)
        (Eq.symm
          (TraceAnalyticStableMotiveCategory.mapOf_eq hom))))

end AnalyticMotives
end LFunctions
end Boundary
