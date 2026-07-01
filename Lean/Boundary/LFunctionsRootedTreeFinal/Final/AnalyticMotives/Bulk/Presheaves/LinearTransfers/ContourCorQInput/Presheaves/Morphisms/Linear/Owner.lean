import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Morphisms.Raw.Owner

/-!
# Morphisms of linear `ContourCor_Q` presheaves

This owner records morphisms of linear presheaves: natural transformations
whose components preserve the value-level rational-linear operations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A morphism of rational-linear `ContourCor_Q` presheaves. -/
structure ContourCorQLinearPresheafMorphism
    (F G : ContourCorQLinearPresheaf) where
  raw :
    ContourCorQPresheafMorphism F.underlying G.underlying
  map_zero :
    (X : ContourCorQPresheafObject) →
      raw.componentAt X (F.zeroAt X) = G.zeroAt X
  map_add :
    (X : ContourCorQPresheafObject) →
      (a b : F.valueAt X) →
        raw.componentAt X (F.addAt X a b) =
          G.addAt X (raw.componentAt X a) (raw.componentAt X b)
  map_scale :
    (X : ContourCorQPresheafObject) →
      (q : Rat) →
        (a : F.valueAt X) →
          raw.componentAt X (F.linearValues.scaleAt X q a) =
            G.linearValues.scaleAt X q (raw.componentAt X a)

namespace ContourCorQLinearPresheafMorphism

/-- The raw natural transformation underlying a linear presheaf morphism. -/
def rawMorphism {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G) :
    ContourCorQPresheafMorphism F.underlying G.underlying :=
  η.raw

/-- The component of a linear presheaf morphism at an object. -/
def componentAt {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (X : ContourCorQPresheafObject) :
    F.valueAt X → G.valueAt X :=
  η.raw.componentAt X

/-- Naturality of a linear presheaf morphism. -/
theorem naturality_eq {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y)
    (a : F.valueAt Y) :
    η.componentAt X (F.pullbackAlong f a) =
      G.pullbackAlong f (η.componentAt Y a) :=
  η.raw.naturality_eq f a

/-- A linear presheaf morphism preserves zero values. -/
theorem map_zero_eq {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (X : ContourCorQPresheafObject) :
    η.componentAt X (F.zeroAt X) = G.zeroAt X :=
  η.map_zero X

/-- A linear presheaf morphism preserves value addition. -/
theorem map_add_eq {F G : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (X : ContourCorQPresheafObject)
    (a b : F.valueAt X) :
    η.componentAt X (F.addAt X a b) =
      G.addAt X (η.componentAt X a) (η.componentAt X b) :=
  η.map_add X a b

/-- Identity morphism of a linear `ContourCor_Q` presheaf. -/
def id (F : ContourCorQLinearPresheaf) :
    ContourCorQLinearPresheafMorphism F F where
  raw := ContourCorQPresheafMorphism.id F.underlying
  map_zero := fun _ => rfl
  map_add := fun _ _ _ => rfl
  map_scale := fun _ _ _ => rfl

/-- Composition of linear `ContourCor_Q` presheaf morphisms. -/
def comp {F G H : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (θ : ContourCorQLinearPresheafMorphism G H) :
    ContourCorQLinearPresheafMorphism F H where
  raw := ContourCorQPresheafMorphism.comp η.raw θ.raw
  map_zero := fun X =>
    Eq.trans
      (congrArg (θ.componentAt X) (η.map_zero_eq X))
      (θ.map_zero_eq X)
  map_add := fun X a b =>
    Eq.trans
      (congrArg (θ.componentAt X) (η.map_add_eq X a b))
      (θ.map_add_eq X (η.componentAt X a) (η.componentAt X b))
  map_scale := fun X q a =>
    Eq.trans
      (congrArg (θ.componentAt X) (η.map_scale X q a))
      (θ.map_scale X q (η.componentAt X a))

/-- Identity morphism components are identity maps. -/
theorem id_component {F : ContourCorQLinearPresheaf}
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (id F).componentAt X a = a :=
  rfl

/-- Composite morphism components are componentwise composites. -/
theorem comp_component {F G H : ContourCorQLinearPresheaf}
    (η : ContourCorQLinearPresheafMorphism F G)
    (θ : ContourCorQLinearPresheafMorphism G H)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp η θ).componentAt X a =
      θ.componentAt X (η.componentAt X a) :=
  rfl

end ContourCorQLinearPresheafMorphism

end AnalyticMotives
end LFunctions
end Boundary
