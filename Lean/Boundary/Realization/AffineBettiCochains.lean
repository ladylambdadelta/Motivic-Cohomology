import Boundary.Realization.AffineComplexPoints
import Boundary.Realization.SingularCochains

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

namespace Boundary
namespace Realization

/-- Canonical affine-open Betti cochains from canonical affine complex points. -/
abbrev smAffineOpenCanonicalBettiCochains
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    CochainComplex (ModuleCat ℚ) ℕ :=
  singularCochainsQ.obj (Opposite.op (smAffineOpenComplexPointsTopCat X U))

/-- Canonical affine-open Betti cochain restriction induced by a morphism in `Sm/ℂ`. -/
abbrev smOverHom_affineComplexPointsCochainsMap
    {X Y : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    smAffineOpenCanonicalBettiCochains Y U ⟶ smAffineOpenCanonicalBettiCochains X V :=
  singularCochainsQ.map (Opposite.op (smOverHom_affineComplexPointsTopMap f U V e))

/-- The canonical affine-open Betti cochain presheaf on a fixed smooth `ℂ`-scheme. -/
noncomputable def smAffineOpenCanonicalBettiCochainsPresheaf
    (X : Geometry.SmSchemeOver ℂ) :
    X.scheme.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat ℚ) ℕ where
  obj U := smAffineOpenCanonicalBettiCochains X (Opposite.unop U)
  map {U V} i :=
    smOverHom_affineComplexPointsCochainsMap (X := X) (Y := X) (𝟙 X)
      (Opposite.unop U) (Opposite.unop V) i.unop.le
  map_id U := by
    change singularCochainsQ.map
        (Opposite.op
          (smOverHom_affineComplexPointsTopMap (𝟙 X)
            (Opposite.unop U) (Opposite.unop U) le_rfl)) =
      𝟙 (singularCochainsQ.obj
        (Opposite.op (smAffineOpenComplexPointsTopCat X (Opposite.unop U))))
    rw [smOverHom_affineComplexPointsTopMap_id (X := X) (U := Opposite.unop U)]
    exact singularCochainsQ.map_id
      (Opposite.op (smAffineOpenComplexPointsTopCat X (Opposite.unop U)))
  map_comp {U V W} i j := by
    have htop :
        smOverHom_affineComplexPointsTopMap (𝟙 X)
            (Opposite.unop V) (Opposite.unop W) j.unop.le ≫
          smOverHom_affineComplexPointsTopMap (𝟙 X)
            (Opposite.unop U) (Opposite.unop V) i.unop.le =
        smOverHom_affineComplexPointsTopMap (𝟙 X)
          (Opposite.unop U) (Opposite.unop W)
          (le_trans j.unop.le i.unop.le) := by
      exact smOverHom_affineComplexPointsTopMap_comp
        (X := X) (Y := X) (Z := X) (𝟙 X) (𝟙 X)
        (U := Opposite.unop U) (V := Opposite.unop V) (W := Opposite.unop W)
        (e₁ := i.unop.le) (e₂ := j.unop.le)
    simpa [smOverHom_affineComplexPointsCochainsMap, htop]
      using
        singularCochainsQ_map_op_comp
          (smOverHom_affineComplexPointsTopMap (𝟙 X)
            (Opposite.unop V) (Opposite.unop W) j.unop.le)
          (smOverHom_affineComplexPointsTopMap (𝟙 X)
            (Opposite.unop U) (Opposite.unop V) i.unop.le)

end Realization
end Boundary
