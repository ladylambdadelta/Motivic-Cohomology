import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.ContourCorQInput.Presheaves.Morphisms.Raw.Owner

/-!
# Pointwise laws for raw presheaf morphisms

This owner proves identity and associativity laws for raw presheaf morphism
composition at the level of components.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace ContourCorQPresheafMorphism

/-- Left identity for raw presheaf morphisms, componentwise. -/
theorem id_comp_component {F G : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp (id F) η).componentAt X a = η.componentAt X a :=
  rfl

/-- Right identity for raw presheaf morphisms, componentwise. -/
theorem comp_id_component {F G : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp η (id G)).componentAt X a = η.componentAt X a :=
  rfl

/-- Associativity for raw presheaf morphisms, componentwise. -/
theorem comp_assoc_component {F G H K : ContourCorQPresheaf}
    (η : ContourCorQPresheafMorphism F G)
    (θ : ContourCorQPresheafMorphism G H)
    (κ : ContourCorQPresheafMorphism H K)
    (X : ContourCorQPresheafObject)
    (a : F.valueAt X) :
    (comp (comp η θ) κ).componentAt X a =
      (comp η (comp θ κ)).componentAt X a :=
  rfl

end ContourCorQPresheafMorphism

end AnalyticMotives
end LFunctions
end Boundary
