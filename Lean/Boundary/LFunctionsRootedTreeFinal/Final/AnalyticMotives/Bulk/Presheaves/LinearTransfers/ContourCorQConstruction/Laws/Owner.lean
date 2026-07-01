import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQConstruction.Operations.Owner

/-!
# Laws for constructed `ContourCor_Q` linear presheaves

This owner exposes pointwise identity and associativity laws for the
constructive transfer lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ConstructedContourPresheafHom

/-- Left identity for constructed presheaf hom composition, componentwise. -/
theorem id_comp_component {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp (id F) η).componentAt X a = η.componentAt X a :=
  ContourCorQLinearPresheafHom.id_comp_component η X a

/-- Right identity for constructed presheaf hom composition, componentwise. -/
theorem comp_id_component {F G : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp η (id G)).componentAt X a = η.componentAt X a :=
  ContourCorQLinearPresheafHom.comp_id_component η X a

/-- Associativity for constructed presheaf hom composition, componentwise. -/
theorem comp_assoc_component
    {F G H K : ConstructedContourPresheafObject}
    (η : ConstructedContourPresheafHom F G)
    (θ : ConstructedContourPresheafHom G H)
    (κ : ConstructedContourPresheafHom H K)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp (comp η θ) κ).componentAt X a =
      (comp η (comp θ κ)).componentAt X a :=
  ContourCorQLinearPresheafHom.comp_assoc_component η θ κ X a

end ConstructedContourPresheafHom

end AnalyticMotives
end LFunctions
end Boundary
