import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.CategoryInput.Homs.Owner

/-!
# Operations for the linear presheaf category input

This owner exposes identity and composition for linear presheaf homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity hom in the linear presheaf category input. -/
def ContourCorQLinearPresheafHom.id
    (F : ContourCorQLinearPresheafObject) :
    ContourCorQLinearPresheafHom F F :=
  ContourCorQLinearPresheafMorphism.id F

/-- Composition in the linear presheaf category input. -/
def ContourCorQLinearPresheafHom.comp
    {F G H : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    (θ : ContourCorQLinearPresheafHom G H) :
    ContourCorQLinearPresheafHom F H :=
  ContourCorQLinearPresheafMorphism.comp η θ

/-- Identity hom components are identity maps. -/
theorem ContourCorQLinearPresheafHom.id_component
    (F : ContourCorQLinearPresheafObject)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (ContourCorQLinearPresheafHom.id F).componentAt X a = a :=
  rfl

/-- Composite hom components are componentwise composites. -/
theorem ContourCorQLinearPresheafHom.comp_component
    {F G H : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    (θ : ContourCorQLinearPresheafHom G H)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (ContourCorQLinearPresheafHom.comp η θ).componentAt X a =
      θ.componentAt X (η.componentAt X a) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
