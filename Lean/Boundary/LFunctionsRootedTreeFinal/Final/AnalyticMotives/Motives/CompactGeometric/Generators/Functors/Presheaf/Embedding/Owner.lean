import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Embedding.Owner

/-!
# Ambient presheaf embedding consequences for compact generators

This file records equality-reflection and hom-lifting for the compact
representable-presheaf functor into all trace presheaves.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The ambient representable preimage of a morphism between compact-generator presheaves. -/
noncomputable def TraceAnalyticGeometricGenerator.presheafPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    source ⟶ target :=
  TraceCorQPresheaf.representablePreimage morphism

/-- The ambient presheaf preimage of an induced compact-generator map is the original morphism. -/
theorem TraceAnalyticGeometricGenerator.presheafPreimage_representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafPreimage
        morphism.representableMap =
      morphism :=
  TraceCorQPresheaf.representablePreimage_representableMap
    morphism.traceHom

/-- Every ambient morphism between compact-generator presheaves is induced by its preimage. -/
theorem TraceAnalyticGeometricGenerator.representableMap_presheafPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    (TraceAnalyticGeometricGenerator.presheafPreimage morphism).representableMap =
      morphism :=
  TraceCorQPresheaf.representableMap_representablePreimage morphism

/-- Equality of ambient representable maps reflects equality of compact-generator morphisms. -/
theorem TraceAnalyticGeometricGenerator.eq_of_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      left.representableMap =
        right.representableMap) :
    left = right :=
  Eq.trans
    (Eq.symm
      (TraceAnalyticGeometricGenerator.presheafPreimage_representableMap
        left))
    (Eq.trans
      (congrArg
        (fun morphism =>
          TraceAnalyticGeometricGenerator.presheafPreimage morphism)
        map_eq)
      (TraceAnalyticGeometricGenerator.presheafPreimage_representableMap
        right))

/-- Every ambient presheaf morphism between compact representables has a compact-generator lift. -/
theorem TraceAnalyticGeometricGenerator.exists_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    ∃ traceMorphism : source ⟶ target,
      traceMorphism.representableMap =
        morphism :=
  Exists.intro
    (TraceAnalyticGeometricGenerator.presheafPreimage morphism)
    (TraceAnalyticGeometricGenerator.representableMap_presheafPreimage
      morphism)

/-- The chosen compact-generator lift of an ambient presheaf morphism. -/
noncomputable def TraceAnalyticGeometricGenerator.liftRepresentableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    source ⟶ target :=
  TraceAnalyticGeometricGenerator.presheafPreimage morphism

/-- The chosen ambient lift maps back to the original presheaf morphism. -/
theorem TraceAnalyticGeometricGenerator.liftRepresentableMap_spec
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    (TraceAnalyticGeometricGenerator.liftRepresentableMap morphism).representableMap =
      morphism :=
  TraceAnalyticGeometricGenerator.representableMap_presheafPreimage
    morphism

end AnalyticMotives
end LFunctions
end Boundary
