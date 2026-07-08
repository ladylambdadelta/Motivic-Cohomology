import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner

/-!
# Chain maps between bounded additive analytic complexes

Bounded complexes form a concrete full subcollection of additive analytic
complexes.  Morphisms are the ordinary chain maps between the underlying
complexes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Chain maps between bounded additive analytic complexes. -/
abbrev TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom
    {bound : Nat}
    (source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :=
  source.complex ⟶ target.complex

/-- Identity chain map on a bounded additive analytic complex. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom complex complex :=
  𝟙 complex.complex

/-- Composition of chain maps between bounded additive analytic complexes. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
    {bound : Nat}
    {first second third :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first third :=
  left ≫ right

/-- The bounded-complex identity is the underlying complex identity. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id_eq
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id complex =
      𝟙 complex.complex :=
  rfl

/-- The bounded-complex composition is the underlying chain-map composition. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp_eq
    {bound : Nat}
    {first second third :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp left right =
      left ≫ right :=
  rfl

/-- Left identity for chain maps between bounded additive analytic complexes. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id_comp
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id source)
        hom =
      hom :=
  CategoryTheory.Category.id_comp hom

/-- Right identity for chain maps between bounded additive analytic complexes. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp_id
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        hom
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.id target) =
      hom :=
  CategoryTheory.Category.comp_id hom

/-- Associativity for chain-map composition between bounded additive analytic complexes. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp_assoc
    {bound : Nat}
    {first second third fourth :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (left :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom first second)
    (middle :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom second third)
    (right :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom third fourth) :
    TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp left middle)
        right =
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp
        left
        (TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.comp middle right) :=
  CategoryTheory.Category.assoc left middle right

end AnalyticMotives
end LFunctions
end Boundary
