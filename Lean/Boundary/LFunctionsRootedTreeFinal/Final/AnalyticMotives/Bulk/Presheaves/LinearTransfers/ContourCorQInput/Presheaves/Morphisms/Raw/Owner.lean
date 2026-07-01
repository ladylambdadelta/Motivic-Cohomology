import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Accessors.Owner

/-!
# Morphisms of `ContourCor_Q` presheaves

This owner records natural transformations between raw presheaves on the
balanced rational contour-transfer input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A morphism of raw `ContourCor_Q` presheaves. -/
structure ContourCorQPresheafMorphism
    (F G : ContourCorQPresheaf) where
  component :
    (X : ContourCorQPresheafObject) → F.valueAt X → G.valueAt X
  naturality :
    {X Y : ContourCorQPresheafObject} →
      (f : ContourCorQPresheafHom X Y) →
        (a : F.valueAt Y) →
          component X (F.pullbackAlong f a) =
            G.pullbackAlong f (component Y a)

namespace ContourCorQPresheafMorphism

/-- The component map at one object. -/
def componentAt {F G : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    (X : ContourCorQPresheafObject) :
    F.valueAt X → G.valueAt X :=
  η.component X

/-- Naturality of a presheaf morphism with respect to a transfer hom. -/
theorem naturality_eq {F G : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y)
    (a : F.valueAt Y) :
    η.componentAt X (F.pullbackAlong f a) =
      G.pullbackAlong f (η.componentAt Y a) :=
  η.naturality f a

/-- Identity morphism of a raw `ContourCor_Q` presheaf. -/
def id (F : ContourCorQPresheaf) :
    ContourCorQPresheafMorphism F F where
  component := fun _ a => a
  naturality := fun _ _ => rfl

/-- Composition of raw `ContourCor_Q` presheaf morphisms. -/
def comp {F G H : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    (θ : ContourCorQPresheafMorphism G H) :
    ContourCorQPresheafMorphism F H where
  component := fun X a => θ.componentAt X (η.componentAt X a)
  naturality := fun {X} {Y} f a =>
    Eq.trans
      (congrArg (θ.componentAt X) (η.naturality_eq f a))
      (θ.naturality_eq f (η.componentAt Y a))

/-- The identity morphism has identity components. -/
theorem id_component {F : ContourCorQPresheaf}
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (id F).componentAt X a = a :=
  rfl

/-- Composite components are componentwise composites. -/
theorem comp_component {F G H : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    (θ : ContourCorQPresheafMorphism G H)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp η θ).componentAt X a =
      θ.componentAt X (η.componentAt X a) :=
  rfl

end ContourCorQPresheafMorphism

end AnalyticMotives
end LFunctions
end Boundary
