import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.Preimage.Owner

/-!
# Fullness and faithfulness of the effective-realization Yoneda source

This file records the concrete hom-level inverse supplied by source-side
Yoneda preimages as fullness and faithfulness statements for the analytic
representable-source functor.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Every morphism between effective-realization source representables is the
image of its recovered compact-generator morphism. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_full_surjective
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    ∃ preimage : source ⟶ target,
      TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map preimage =
        morphism :=
  Exists.intro
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism)
    (TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage morphism)

/-- The explicit full preimage of a representable-source morphism is the
source Yoneda preimage. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_full_preimage_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism) =
      (TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv source target).symm
        morphism :=
  Eq.symm
    (TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv_symm_apply
      morphism)

/-- The effective-realization source functor reflects equality of
compact-generator morphisms. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_faithful_reflects
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map left =
        TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map right) :
    left = right :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_map left))
    (Eq.trans
      (congrArg
        (fun morphism =>
          TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism)
        map_eq)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_map right))

/-- Source Yoneda preimage is a left inverse to the representable-source
functor on morphisms. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimage_leftInverse
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism) =
      morphism :=
  TraceAnalyticEffectiveRealization.yonedaSourcePreimage_map
    morphism

/-- Source Yoneda preimage is a right inverse to the representable-source
functor on morphisms. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimage_rightInverse
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism) =
      morphism :=
  TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage
    morphism

/-- The effective-realization Yoneda source functor is full. -/
instance TraceAnalyticEffectiveRealization.yonedaSourceFunctor_full :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.Full where
  map_surjective {X Y} morphism :=
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor_full_surjective
      (source := X)
      (target := Y)
      morphism

/-- The effective-realization Yoneda source functor is faithful. -/
instance TraceAnalyticEffectiveRealization.yonedaSourceFunctor_faithful :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.Faithful where
  map_injective {X Y} {left right} map_eq :=
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor_faithful_reflects
      (source := X)
      (target := Y)
      map_eq

/-- Explicit fully faithful package for the effective-realization Yoneda
source functor, with inverse given by the concrete Yoneda preimage. -/
def TraceAnalyticEffectiveRealization.yonedaSourceFunctor_fullyFaithful :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.FullyFaithful where
  preimage {X Y} morphism :=
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism
  map_preimage {X Y} morphism :=
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage_rightInverse
      (source := X)
      (target := Y)
      morphism
  preimage_map {X Y} morphism :=
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage_leftInverse
      morphism

/-- The fully faithful package preimage agrees with the concrete Yoneda source
preimage. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_fullyFaithful_preimage_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor_fullyFaithful.preimage
        morphism =
      TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
