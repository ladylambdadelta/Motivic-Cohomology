import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.LinearAlgebra.Dual

/-!
# Singular chains with rational coefficients

This file constructs the first concrete target-side complex needed for Betti
realization: the singular chain complex of a topological space with
`ℚ`-coefficients.

It does not define a Betti realization of schemes or motives.  The missing
geometric input is still the analytification/topological-space functor for
smooth schemes over the chosen base and the pull-push action of finite
correspondences.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial
open scoped ModuleCat

namespace Boundary
namespace Realization

/-- Linearize a simplicial set degreewise by the free `ℚ`-module functor. -/
def simplicialSetToQModules :
    SSet ⥤ SimplicialObject (ModuleCat ℚ) :=
  (SimplicialObject.whiskering (Type _) (ModuleCat ℚ)).obj
    (ModuleCat.free ℚ)

/-- The singular simplicial `ℚ`-module of a topological space. -/
def singularSimplicialQModule :
    TopCat ⥤ SimplicialObject (ModuleCat ℚ) :=
  TopCat.toSSet ⋙ simplicialSetToQModules

/-- Singular chains with rational coefficients. -/
def singularChainsQ :
    TopCat ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
  singularSimplicialQModule ⋙
    AlgebraicTopology.alternatingFaceMapComplex (ModuleCat ℚ)

/-- Singular chains, viewed with contravariant source and opposite target.

This is not yet cohomology or cochains; it is the categorical opposite of
`singularChainsQ`, useful for composing with contravariant motivic inputs
without choosing a dualization functor. -/
def singularChainsQOp :
    TopCatᵒᵖ ⥤ (ChainComplex (ModuleCat ℚ) ℕ)ᵒᵖ :=
  singularChainsQ.op

/-- The `ℚ`-linear dual of a bundled `ℚ`-module. -/
abbrev moduleCatDualQ (M : ModuleCat ℚ) : ModuleCat ℚ :=
  ModuleCat.of ℚ (Module.Dual ℚ (M : Type _))

/-- The cochain complex obtained by dualizing a chain complex of `ℚ`-modules. -/
noncomputable def dualCochainComplexOfChain
    (C : ChainComplex (ModuleCat ℚ) ℕ) :
    CochainComplex (ModuleCat ℚ) ℕ :=
  CochainComplex.of
    (fun n => moduleCatDualQ (C.X n))
    (fun n => ↟ ((C.d (n + 1) n).dualMap))
    (by
      intro n
      apply LinearMap.ext
      intro φ
      change ((C.X n : Type _) →ₗ[ℚ] ℚ) at φ
      apply LinearMap.ext
      intro x
      change φ ((C.d (n + 1) n) ((C.d (n + 2) (n + 1)) x)) = 0
      have h := C.d_comp_d (n + 2) (n + 1) n
      have happ := congrArg (fun f : C.X (n + 2) ⟶ C.X n => f x) h
      change (C.d (n + 1) n) ((C.d (n + 2) (n + 1)) x) = 0 at happ
      rw [happ]
      exact map_zero φ)

/-- Dualizing a chain map gives the induced cochain map in the opposite direction. -/
noncomputable def dualCochainMapOfChainMap
    {C D : ChainComplex (ModuleCat ℚ) ℕ} (f : C ⟶ D) :
    dualCochainComplexOfChain D ⟶ dualCochainComplexOfChain C :=
  CochainComplex.ofHom
    (fun n => moduleCatDualQ (D.X n))
    (fun n => ↟ ((D.d (n + 1) n).dualMap))
    (by
      intro n
      apply LinearMap.ext
      intro φ
      change ((D.X n : Type _) →ₗ[ℚ] ℚ) at φ
      apply LinearMap.ext
      intro x
      change φ ((D.d (n + 1) n) ((D.d (n + 2) (n + 1)) x)) = 0
      have h := D.d_comp_d (n + 2) (n + 1) n
      have happ := congrArg (fun g : D.X (n + 2) ⟶ D.X n => g x) h
      change (D.d (n + 1) n) ((D.d (n + 2) (n + 1)) x) = 0 at happ
      rw [happ]
      exact map_zero φ)
    (fun n => moduleCatDualQ (C.X n))
    (fun n => ↟ ((C.d (n + 1) n).dualMap))
    (by
      intro n
      apply LinearMap.ext
      intro φ
      change ((C.X n : Type _) →ₗ[ℚ] ℚ) at φ
      apply LinearMap.ext
      intro x
      change φ ((C.d (n + 1) n) ((C.d (n + 2) (n + 1)) x)) = 0
      have h := C.d_comp_d (n + 2) (n + 1) n
      have happ := congrArg (fun g : C.X (n + 2) ⟶ C.X n => g x) h
      change (C.d (n + 1) n) ((C.d (n + 2) (n + 1)) x) = 0 at happ
      rw [happ]
      exact map_zero φ)
    (fun n => ↟ ((f.f n).dualMap))
    (by
      intro n
      apply LinearMap.ext
      intro φ
      change ((D.X n : Type _) →ₗ[ℚ] ℚ) at φ
      apply LinearMap.ext
      intro x
      change φ ((f.f n) ((C.d (n + 1) n) x)) =
        φ ((D.d (n + 1) n) ((f.f (n + 1)) x))
      have h := f.comm (n + 1) n
      have happ := congrArg (fun g : C.X (n + 1) ⟶ D.X n => g x) h
      change (D.d (n + 1) n) ((f.f (n + 1)) x) =
        (f.f n) ((C.d (n + 1) n) x) at happ
      exact congrArg (fun y => φ y) happ.symm)

/-- Singular cochains with rational coefficients. -/
noncomputable def singularCochainsQ :
    TopCatᵒᵖ ⥤ CochainComplex (ModuleCat ℚ) ℕ where
  obj X := dualCochainComplexOfChain (singularChainsQ.obj (Opposite.unop X))
  map {X Y} f :=
    dualCochainMapOfChainMap (singularChainsQ.map (Opposite.unop f))
  map_id X := by
    ext n φ
    change (((singularChainsQ.obj (Opposite.unop X)).X n : Type _) →ₗ[ℚ] ℚ) at φ
    apply LinearMap.ext
    intro z
    change φ (((singularChainsQ.map (𝟙 (Opposite.unop X))).f n) z) = φ z
    rw [singularChainsQ.map_id]
    rfl
  map_comp {X Y Z} f g := by
    ext n φ
    change (((singularChainsQ.obj (Opposite.unop X)).X n : Type _) →ₗ[ℚ] ℚ) at φ
    apply LinearMap.ext
    intro z
    change φ (((singularChainsQ.map (Opposite.unop (f ≫ g))).f n) z) =
      φ
        (((singularChainsQ.map (Opposite.unop f)).f n)
          (((singularChainsQ.map (Opposite.unop g)).f n) z))
    rw [show Opposite.unop (f ≫ g) = Opposite.unop g ≫ Opposite.unop f by rfl]
    rw [singularChainsQ.map_comp]
    rfl

@[simp]
theorem singularSimplicialQModule_obj_obj
    (X : TopCat) (n : SimplexCategoryᵒᵖ) :
    ((singularSimplicialQModule.obj X).obj n : ModuleCat ℚ) =
      (ModuleCat.free ℚ).obj ((TopCat.toSSet.obj X).obj n) :=
  rfl

@[simp]
theorem singularChainsQ_obj_X (X : TopCat) (n : ℕ) :
    ((singularChainsQ.obj X).X n : ModuleCat ℚ) =
      (ModuleCat.free ℚ).obj
        ((TopCat.toSSet.obj X).obj (Opposite.op ([n] : SimplexCategory))) := by
  exact AlgebraicTopology.alternatingFaceMapComplex_obj_X
    (singularSimplicialQModule.obj X) n

@[simp]
theorem singularChainsQ_map_f
    {X Y : TopCat} (f : X ⟶ Y) (n : ℕ) :
    ((singularChainsQ.map f).f n) =
      (ModuleCat.free ℚ).map
        ((TopCat.toSSet.map f).app (Opposite.op ([n] : SimplexCategory))) := by
  exact AlgebraicTopology.alternatingFaceMapComplex_map_f
    (singularSimplicialQModule.map f) n

@[simp]
theorem singularChainsQ_map_id (X : TopCat) :
    singularChainsQ.map (𝟙 X) = 𝟙 (singularChainsQ.obj X) :=
  singularChainsQ.map_id X

@[simp]
theorem singularChainsQ_map_comp
    {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularChainsQ.map (f ≫ g) =
      singularChainsQ.map f ≫ singularChainsQ.map g :=
  singularChainsQ.map_comp f g

@[simp]
theorem singularChainsQOp_obj (X : TopCatᵒᵖ) :
    singularChainsQOp.obj X = Opposite.op (singularChainsQ.obj (Opposite.unop X)) :=
  rfl

@[simp]
theorem singularChainsQOp_map {X Y : TopCatᵒᵖ} (f : X ⟶ Y) :
    singularChainsQOp.map f =
      Opposite.op (singularChainsQ.map (Opposite.unop f)) :=
  rfl

@[simp]
theorem singularChainsQOp_map_id (X : TopCatᵒᵖ) :
    singularChainsQOp.map (𝟙 X) = 𝟙 (singularChainsQOp.obj X) :=
  singularChainsQOp.map_id X

@[simp]
theorem singularChainsQOp_map_comp
    {X Y Z : TopCatᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularChainsQOp.map (f ≫ g) =
      singularChainsQOp.map f ≫ singularChainsQOp.map g :=
  singularChainsQOp.map_comp f g

@[simp]
theorem singularCochainsQ_obj (X : TopCatᵒᵖ) :
    singularCochainsQ.obj X =
      dualCochainComplexOfChain (singularChainsQ.obj (Opposite.unop X)) :=
  rfl

@[simp]
theorem singularCochainsQ_map {X Y : TopCatᵒᵖ} (f : X ⟶ Y) :
    singularCochainsQ.map f =
      dualCochainMapOfChainMap (singularChainsQ.map (Opposite.unop f)) :=
  rfl

end Realization
end Boundary
