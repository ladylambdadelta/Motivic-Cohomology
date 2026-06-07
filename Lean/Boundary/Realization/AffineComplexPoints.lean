import Boundary.Realization.AffineComplexPolynomials
import Boundary.Realization.SingularChains
import Boundary.SmOver

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

universe u

namespace Boundary
namespace Realization

variable {X Y Z : Geometry.SmSchemeOver ℂ}

local instance
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    Algebra ℂ Γ(X.scheme, (U : X.scheme.Opens)) :=
  smSchemeOpenSectionAlgebra (k := ℂ) X U


/-- Canonical affine complex points of an affine open in `Sm/ℂ`, defined as `ℂ`-algebra maps
from its section ring to `ℂ`. -/
abbrev smAffineOpenComplexPoints
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :=
  Γ(X.scheme, (U : X.scheme.Opens)) →ₐ[ℂ] ℂ

instance smAffineOpenComplexPoints.instTopologicalSpace
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    TopologicalSpace (smAffineOpenComplexPoints X U) :=
  TopologicalSpace.induced
    (fun φ : smAffineOpenComplexPoints X U => (φ : Γ(X.scheme, (U : X.scheme.Opens)) → ℂ))
    inferInstance

/-- Evaluation at a section is continuous for the canonical affine complex-point topology. -/
theorem continuous_eval_smAffineOpenComplexPoints
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens)
    (s : Γ(X.scheme, (U : X.scheme.Opens))) :
    Continuous fun φ : smAffineOpenComplexPoints X U => φ s := by
  change Continuous
    ((fun f : Γ(X.scheme, (U : X.scheme.Opens)) → ℂ => f s) ∘
      (fun φ : smAffineOpenComplexPoints X U => (φ : Γ(X.scheme, (U : X.scheme.Opens)) → ℂ)))
  exact (continuous_apply s).comp continuous_induced_dom

/-- The canonical contravariant map on affine complex points induced by a morphism in `Sm/ℂ`
on compatible affine opens. -/
noncomputable def smOverHom_affineComplexPointsMap
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    smAffineOpenComplexPoints X V → smAffineOpenComplexPoints Y U :=
  fun φ => φ.comp (smOverHom_appLEAlgHom f U V e)

@[simp]
theorem smOverHom_affineComplexPointsMap_apply
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens))
    (φ : smAffineOpenComplexPoints X V)
    (s : Γ(Y.scheme, (U : Y.scheme.Opens))) :
    smOverHom_affineComplexPointsMap f U V e φ s =
      φ ((smOverHom_appLEAlgHom f U V e) s) := rfl

/-- The canonical affine complex-points map is continuous for the induced topology. -/
theorem smOverHom_affineComplexPointsMap_continuous
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    Continuous (smOverHom_affineComplexPointsMap f U V e) := by
  refine continuous_induced_rng.2 ?_
  refine continuous_pi ?_
  intro s
  change Continuous (fun φ : smAffineOpenComplexPoints X V =>
    φ ((smOverHom_appLEAlgHom f U V e) s))
  exact continuous_eval_smAffineOpenComplexPoints X V ((smOverHom_appLEAlgHom f U V e) s)

@[simp]
theorem smOverHom_affineComplexPointsMap_id
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    smOverHom_affineComplexPointsMap (X := X) (Y := X) (𝟙 X) U U le_rfl = id := by
  ext φ s
  rw [smOverHom_affineComplexPointsMap, smOverHom_appLEAlgHom_id]
  rfl

theorem smOverHom_affineComplexPointsMap_comp
    {X Y Z : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y) (g : Boundary.SmOverHom Y Z)
    (U : Z.scheme.affineOpens) (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
    (e₁ : (V : Y.scheme.Opens) ≤ g.hom ⁻¹ᵁ (U : Z.scheme.Opens))
    (e₂ : (W : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (V : Y.scheme.Opens)) :
    smOverHom_affineComplexPointsMap g U V e₁ ∘
        smOverHom_affineComplexPointsMap f V W e₂ =
      smOverHom_affineComplexPointsMap (Boundary.SmOverHom.comp f g) U W
        (by
          simpa [Boundary.SmOverHom.comp] using
            (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
              e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le)) := by
  ext φ s
  have hcomp := smOverHom_appLEAlgHom_comp f g U V W e₁ e₂
  change φ ((smOverHom_appLEAlgHom f (U := V) (V := W) e₂)
      ((smOverHom_appLEAlgHom g (U := U) (V := V) e₁) s)) =
    φ ((smOverHom_appLEAlgHom (Boundary.SmOverHom.comp f g) U W
      (by
        simpa [Boundary.SmOverHom.comp] using
          (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
            e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le))) s)
  exact congrArg (fun h => φ (h s)) hcomp

/-- Canonical affine complex points as a `TopCat` object. -/
abbrev smAffineOpenComplexPointsTopCat
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) : TopCat :=
  TopCat.of (smAffineOpenComplexPoints X U)

/-- Canonical affine complex-points map as a `TopCat` morphism. -/
noncomputable def smOverHom_affineComplexPointsTopMap
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    smAffineOpenComplexPointsTopCat X V ⟶ smAffineOpenComplexPointsTopCat Y U :=
  ⟨smOverHom_affineComplexPointsMap f U V e,
    smOverHom_affineComplexPointsMap_continuous f U V e⟩

@[simp]
theorem smOverHom_affineComplexPointsTopMap_id
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    smOverHom_affineComplexPointsTopMap (X := X) (Y := X) (𝟙 X) U U le_rfl =
      𝟙 (smAffineOpenComplexPointsTopCat X U) := by
  ext φ
  exact congrArg (fun h => h φ) (smOverHom_affineComplexPointsMap_id (X := X) (U := U))

theorem smOverHom_affineComplexPointsTopMap_comp
    {X Y Z : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y) (g : Boundary.SmOverHom Y Z)
    (U : Z.scheme.affineOpens) (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
    (e₁ : (V : Y.scheme.Opens) ≤ g.hom ⁻¹ᵁ (U : Z.scheme.Opens))
    (e₂ : (W : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (V : Y.scheme.Opens)) :
    smOverHom_affineComplexPointsTopMap f V W e₂ ≫
        smOverHom_affineComplexPointsTopMap g U V e₁ =
      smOverHom_affineComplexPointsTopMap (Boundary.SmOverHom.comp f g) U W
        (by
          simpa [Boundary.SmOverHom.comp] using
            (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
              e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le)) := by
  ext φ
  exact congrArg (fun h => h φ) (smOverHom_affineComplexPointsMap_comp f g U V W e₁ e₂)

/-- Canonical affine-open Betti chains from canonical affine complex points. -/
abbrev smAffineOpenCanonicalBettiChains
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  singularChainsQ.obj (smAffineOpenComplexPointsTopCat X U)

/-- Canonical affine-open Betti chain map induced by a morphism in `Sm/ℂ`. -/
abbrev smOverHom_affineComplexPointsChainsMap
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens)) :
    smAffineOpenCanonicalBettiChains X V ⟶ smAffineOpenCanonicalBettiChains Y U :=
  singularChainsQ.map (smOverHom_affineComplexPointsTopMap f U V e)

/-- The affine-open canonical Betti chain assignment on a fixed smooth `ℂ`-scheme, viewed as a
covariant functor on affine opens. This is covariant because affine complex points are
contravariant in section rings. -/
noncomputable def smAffineOpenCanonicalBettiChainsFunctor
    (X : Geometry.SmSchemeOver ℂ) :
    X.scheme.affineOpens ⥤ ChainComplex (ModuleCat ℚ) ℕ where
  obj U := smAffineOpenCanonicalBettiChains X U
  map {U V} i :=
    smOverHom_affineComplexPointsChainsMap (X := X) (Y := X) (𝟙 X)
      V U i.le
  map_id U := by
    change singularChainsQ.map (smOverHom_affineComplexPointsTopMap (𝟙 X) U U le_rfl) =
      𝟙 (singularChainsQ.obj (smAffineOpenComplexPointsTopCat X U))
    rw [smOverHom_affineComplexPointsTopMap_id (X := X) (U := U)]
    exact singularChainsQ_map_id (smAffineOpenComplexPointsTopCat X U)
  map_comp {U V W} i j := by
    have htop :
        smOverHom_affineComplexPointsTopMap (𝟙 X) V U i.le ≫
          smOverHom_affineComplexPointsTopMap (𝟙 X) W V j.le =
        smOverHom_affineComplexPointsTopMap (𝟙 X) W U (le_trans i.le j.le) := by
      exact smOverHom_affineComplexPointsTopMap_comp
        (X := X) (Y := X) (Z := X) (𝟙 X) (𝟙 X)
        (U := W) (V := V) (W := U)
        (e₁ := j.le) (e₂ := i.le)
    have hmap := congrArg singularChainsQ.map htop
    rw [singularChainsQ_map_comp] at hmap
    exact hmap.symm

end Realization
end Boundary
