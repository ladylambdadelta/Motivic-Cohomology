import Boundary.Realization.AffineComplexModelDatum
import Boundary.Realization.AffineComplexModelMaps

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Boundary
namespace Realization

/-- The chosen affine complex-model map attached to a morphism in `Sm/ℂ`
and a compatible pair of affine opens. -/
noncomputable def smOverHom_chosenAffineComplexModelMap
    {X Y : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    smAffineOpenComplexModel X V → smAffineOpenComplexModel Y U :=
  smOverHom_affineComplexModelMap f U V e
    (smAffineOpenComplexModelPresentation X V)
    (smAffineOpenComplexModelEquations X V)
    (smAffineOpenComplexModelPresentation Y U)
    (smAffineOpenComplexModelEquations Y U)
    (smAffineOpenComplexModelPresentation_surjective X V)
    (smAffineOpenComplexModelEquations_span X V)
    (smAffineOpenComplexModelEquations_span Y U)

theorem smOverHom_chosenAffineComplexModelMap_continuous
    {X Y : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    Continuous (smOverHom_chosenAffineComplexModelMap f U V e) := by
  simpa [smOverHom_chosenAffineComplexModelMap] using
    smOverHom_affineComplexModelMap_continuous f U V e
      (smAffineOpenComplexModelPresentation X V)
      (smAffineOpenComplexModelEquations X V)
      (smAffineOpenComplexModelPresentation Y U)
      (smAffineOpenComplexModelEquations Y U)
      (smAffineOpenComplexModelPresentation_surjective X V)
      (smAffineOpenComplexModelEquations_span X V)
      (smAffineOpenComplexModelEquations_span Y U)

end Realization
end Boundary
