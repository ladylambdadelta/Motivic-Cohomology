import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.CategoryInput.Operations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Morphisms.Linear.Laws.Owner

/-!
# Laws for the linear presheaf category input

This owner exposes pointwise identity and associativity laws for the public
linear presheaf hom operations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Left identity for public linear presheaf hom composition, componentwise. -/
theorem ContourCorQLinearPresheafHom.id_comp_component
    {F G : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (ContourCorQLinearPresheafHom.comp
      (ContourCorQLinearPresheafHom.id F) η).componentAt X a =
        η.componentAt X a :=
  rfl

/-- Right identity for public linear presheaf hom composition, componentwise. -/
theorem ContourCorQLinearPresheafHom.comp_id_component
    {F G : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (ContourCorQLinearPresheafHom.comp η
      (ContourCorQLinearPresheafHom.id G)).componentAt X a =
        η.componentAt X a :=
  rfl

/-- Associativity for public linear presheaf hom composition, componentwise. -/
theorem ContourCorQLinearPresheafHom.comp_assoc_component
    {F G H K : ContourCorQLinearPresheafObject}
    (η : ContourCorQLinearPresheafHom F G)
    (θ : ContourCorQLinearPresheafHom G H)
    (κ : ContourCorQLinearPresheafHom H K)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (ContourCorQLinearPresheafHom.comp
      (ContourCorQLinearPresheafHom.comp η θ) κ).componentAt X a =
        (ContourCorQLinearPresheafHom.comp η
          (ContourCorQLinearPresheafHom.comp θ κ)).componentAt X a :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
