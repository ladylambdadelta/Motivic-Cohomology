import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQConstruction.Objects.Owner

/-!
# Constructed `ContourCor_Q` linear presheaf homs

This owner names the homs in the constructive transfer lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Homs in the constructed linear presheaf transfer lane. -/
abbrev ConstructedContourPresheafHom
    (F G : ConstructedContourPresheafObject) :=
  ContourCorQLinearPresheafHom F G

namespace ConstructedContourPresheafHom

/-- The component map of a constructed presheaf hom at a bulk object. -/
def componentAt {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (X : ContourCorQPresheafObject) :
    F.valueAt X → G.valueAt X :=
  η.componentAt X

/-- Naturality of a constructed presheaf hom with respect to transfers. -/
theorem naturality {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    {X Y : ContourCorQPresheafObject}
    (f : ContourCorQPresheafHom X Y)
    (a : F.valueAt Y) :
    η.componentAt X (F.pullbackAlong f a) =
      G.pullbackAlong f (η.componentAt Y a) :=
  ContourCorQLinearPresheafMorphism.naturality_eq η f a

/-- Constructed presheaf homs preserve zero values. -/
theorem map_zero {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (X : ContourCorQPresheafObject) :
    η.componentAt X (F.zeroAt X) = G.zeroAt X :=
  ContourCorQLinearPresheafMorphism.map_zero_eq η X

/-- Constructed presheaf homs preserve addition. -/
theorem map_add {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (X : ContourCorQPresheafObject)
    (a b : F.valueAt X) :
    η.componentAt X (F.addAt X a b) =
      G.addAt X (η.componentAt X a) (η.componentAt X b) :=
  ContourCorQLinearPresheafMorphism.map_add_eq η X a b

/-- Constructed presheaf homs preserve scalar multiplication. -/
theorem map_scale {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (X : ContourCorQPresheafObject)
    (q : ℚ) (a : F.valueAt X) :
    η.componentAt X
        (ConstructedContourPresheafObject.scaleAt F X q a) =
      ConstructedContourPresheafObject.scaleAt G X q
        (η.componentAt X a) :=
  η.map_scale X q a

end ConstructedContourPresheafHom

end AnalyticMotives
end LFunctions
end Boundary
