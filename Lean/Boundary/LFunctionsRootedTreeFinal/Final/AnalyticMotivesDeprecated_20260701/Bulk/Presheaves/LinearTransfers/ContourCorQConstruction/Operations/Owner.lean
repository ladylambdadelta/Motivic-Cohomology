import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQConstruction.Homs.Owner

/-!
# Operations for constructed `ContourCor_Q` linear presheaves

This owner exposes identity and composition in the constructive transfer lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedContourPresheafHom

/-- Identity hom for constructed contour presheaves. -/
def id (F : ConstructedContourPresheafObject) :
    ConstructedContourPresheafHom F F :=
  ContourCorQLinearPresheafHom.id F

/-- Composition of constructed contour presheaf homs. -/
def comp {F G H : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (θ : ConstructedContourPresheafHom G H) :
    ConstructedContourPresheafHom F H :=
  ContourCorQLinearPresheafHom.comp η θ

/-- Identity hom components are identity maps. -/
theorem id_component
    (F : ConstructedContourPresheafObject)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (id F).componentAt X a = a :=
  ContourCorQLinearPresheafHom.id_component F X a

/-- Composite hom components are componentwise composites. -/
theorem comp_component {F G H : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (θ : ConstructedContourPresheafHom G H)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp η θ).componentAt X a =
      θ.componentAt X (η.componentAt X a) :=
  ContourCorQLinearPresheafHom.comp_component η θ X a

end ConstructedContourPresheafHom

end AnalyticMotives
end LFunctions
end Boundary
