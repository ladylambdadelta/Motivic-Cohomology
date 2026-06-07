import Boundary.Realization.AffineComplexPoints
import Boundary.Realization.SingularChains

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

namespace Boundary
namespace Realization

/-- The canonical affine Betti chain complex on an affine smooth `ℂ`-scheme, evaluated on the
top affine open. -/
abbrev smAffineBettiChains
    (X : AffineSmOver ℂ) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  smAffineOpenCanonicalBettiChains X.obj (affineSmOverTop X)

/-- The canonical Betti chain map induced by a morphism of affine smooth `ℂ`-schemes. -/
abbrev smAffineBettiChainsMap
    {X Y : AffineSmOver ℂ} (f : X ⟶ Y) :
    smAffineBettiChains X ⟶ smAffineBettiChains Y :=
  smOverHom_affineComplexPointsChainsMap f (affineSmOverTop Y) (affineSmOverTop X)
    (affineSmOverTop_le_preimage f)

@[simp]
theorem smAffineBettiChainsMap_id
    (X : AffineSmOver ℂ) :
    smAffineBettiChainsMap (X := X) (Y := X) (𝟙 X) = 𝟙 (smAffineBettiChains X) := by
  have htop :
      smOverHom_affineComplexPointsTopMap (𝟙 X)
          (affineSmOverTop X) (affineSmOverTop X)
          (affineSmOverTop_le_preimage (𝟙 X)) =
        𝟙 (smAffineOpenComplexPointsTopCat X.obj (affineSmOverTop X)) := by
    rw [show affineSmOverTop_le_preimage (𝟙 X) = le_rfl from Subsingleton.elim _ _]
    exact smOverHom_affineComplexPointsTopMap_id (X := X.obj) (U := affineSmOverTop X)
  simpa [smAffineBettiChains, smAffineBettiChainsMap, smAffineOpenCanonicalBettiChains,
    smOverHom_affineComplexPointsChainsMap] using congrArg singularChainsQ.map htop

theorem smAffineBettiChainsMap_comp
    {X Y Z : AffineSmOver ℂ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smAffineBettiChainsMap (X := X) (Y := Z) (f ≫ g) =
      smAffineBettiChainsMap f ≫ smAffineBettiChainsMap g := by
  have htop :=
    smOverHom_affineComplexPointsTopMap_comp
      (X := X.obj) (Y := Y.obj) (Z := Z.obj)
      (f : Boundary.SmOverHom X.obj Y.obj) (g : Boundary.SmOverHom Y.obj Z.obj)
      (affineSmOverTop Z) (affineSmOverTop Y) (affineSmOverTop X)
      (affineSmOverTop_le_preimage g) (affineSmOverTop_le_preimage f)
  change smAffineBettiChainsMap (X := X) (Y := Z) (f ≫ g) =
      smAffineBettiChainsMap (X := X) (Y := Y) f ≫ smAffineBettiChainsMap (X := Y) (Y := Z) g
  have htop := smOverHom_affineComplexPointsTopMap_comp
      (X := X.obj) (Y := Y.obj) (Z := Z.obj)
      (f : Boundary.SmOverHom X.obj Y.obj) (g : Boundary.SmOverHom Y.obj Z.obj)
      (affineSmOverTop Z) (affineSmOverTop Y) (affineSmOverTop X)
      (affineSmOverTop_le_preimage g) (affineSmOverTop_le_preimage f)
  simpa [smAffineBettiChains, smAffineBettiChainsMap, smAffineOpenCanonicalBettiChains,
    smOverHom_affineComplexPointsChainsMap, Functor.map_comp] using
    congrArg singularChainsQ.map htop.symm

/-- The canonical affine Betti functor on affine smooth `ℂ`-schemes. -/
noncomputable def smAffineBettiChainsFunctor :
    AffineSmOver ℂ ⥤ ChainComplex (ModuleCat ℚ) ℕ where
  obj X := smAffineBettiChains X
  map {X Y} f := smAffineBettiChainsMap f
  map_id X := smAffineBettiChainsMap_id X
  map_comp f g := by
    exact smAffineBettiChainsMap_comp f g

end Realization
end Boundary
