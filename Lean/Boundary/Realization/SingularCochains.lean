import Boundary.Realization.SingularChains

noncomputable section

open CategoryTheory

namespace Boundary
namespace Realization

@[simp]
theorem singularCochainsQ_map_comp'
    {X Y Z : TopCatᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCochainsQ.map (f ≫ g) =
      singularCochainsQ.map f ≫ singularCochainsQ.map g := by
  simpa using (Functor.map_comp singularCochainsQ f g)

@[simp]
theorem singularCochainsQ_map_op_comp
    {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCochainsQ.map (Opposite.op (f ≫ g)) =
      singularCochainsQ.map (Opposite.op g) ≫ singularCochainsQ.map (Opposite.op f) := by
  change singularCochainsQ.map ((f ≫ g).op) =
    singularCochainsQ.map g.op ≫ singularCochainsQ.map f.op
  rw [op_comp]
  exact Functor.map_comp singularCochainsQ (Opposite.op g) (Opposite.op f)

end Realization
end Boundary
