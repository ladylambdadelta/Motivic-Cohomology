import Boundary.PolynomialSmoothness.PresentationCombinatorics
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

universe u v

namespace Boundary

noncomputable section

namespace _root_.Algebra

theorem polynomial_C_toAlgebra_eq (R : Type u) [CommRing R] :
    (Polynomial.C : R →+* Polynomial R).toAlgebra = Polynomial.algebraOfAlgebra := by
  apply Algebra.algebra_ext
  intro r
  rfl

theorem mvPolynomial_C_toAlgebra_eq (R : Type u) [CommRing R] (σ : Type v) :
    (MvPolynomial.C : R →+* MvPolynomial σ R).toAlgebra = MvPolynomial.algebra := by
  apply Algebra.algebra_ext
  intro r
  rfl

namespace PreSubmersivePresentation

/-- The coefficients of the differential relation attached to a relation `r`
are given by the Jacobian matrix entries of the presubmersive presentation. -/
theorem differentialsRelations_relation_apply
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels]
    (r i : P.rels) :
    (P.toPresentation.differentialsRelations.relation r) (P.map i) =
      algebraMap P.Ring S (P.jacobiMatrix i r) := by
  change
    (Finsupp.mapRange (algebraMap P.Ring S) (by rw [map_zero])
        ((KaehlerDifferential.mvPolynomialBasis R P.vars).repr
          (KaehlerDifferential.D R P.Ring (P.relation r)))) (P.map i)
      =
        algebraMap P.Ring S (P.jacobiMatrix i r)
  rw [Finsupp.mapRange_apply]
  rw [KaehlerDifferential.mvPolynomialBasis_repr_apply]
  rw [P.jacobiMatrix_apply]

/-- The single-column generators of the differentials relation map are exactly
the Jacobian columns, indexed through the relation-to-variable map. -/
theorem differentialsRelations_map_single_apply
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels]
    (r i : P.rels) :
    (P.toPresentation.differentialsRelations.map (Finsupp.single r 1)) (P.map i) =
      algebraMap P.Ring S (P.jacobiMatrix i r) := by
  rw [(P.toPresentation.differentialsRelations).map_single]
  exact Algebra.PreSubmersivePresentation.differentialsRelations_relation_apply P r i

/-- Under a bijective relation-to-variable map, the finite-function form of the
single-column differential relation is exactly the corresponding Jacobian
column. -/
theorem differentialsRelations_map_single_eq_jacobianColumn
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels] [Finite P.vars] [DecidableEq P.vars]
    (hbij : Function.Bijective P.map)
    (r : P.rels) :
    Finsupp.linearEquivFunOnFinite S S P.vars
        (P.toPresentation.differentialsRelations.map (Finsupp.single r 1))
      =
        fun v =>
          algebraMap P.Ring S
            (P.jacobiMatrix ((Equiv.ofBijective P.map hbij).symm v) r) := by
  let e : P.rels ≃ P.vars := Equiv.ofBijective P.map hbij
  ext v
  obtain ⟨i, rfl⟩ := hbij.surjective v
  have hi : e.symm (P.map i) = i := by
    exact e.symm_apply_eq.mpr rfl
  calc
    (Finsupp.linearEquivFunOnFinite S S P.vars
        (P.toPresentation.differentialsRelations.map (Finsupp.single r 1))) (P.map i)
        =
          (P.toPresentation.differentialsRelations.map (Finsupp.single r 1)) (P.map i) := rfl
    _ = algebraMap P.Ring S (P.jacobiMatrix i r) :=
          Algebra.PreSubmersivePresentation.differentialsRelations_map_single_apply P r i
    _ = algebraMap P.Ring S (P.jacobiMatrix (e.symm (P.map i)) r) := by
          rw [hi]

/-- Coordinate form of the transported single-column differential relation.
This is the pointwise statement behind the Jacobian matrix transport. -/
theorem transported_differentialsRelations_single_apply
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels] [Finite P.vars] [DecidableEq P.vars]
    (hbij : Function.Bijective P.map)
    (r i : P.rels) :
    (((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap)
        ((Finsupp.linearEquivFunOnFinite S S P.vars)
          (P.toPresentation.differentialsRelations.map (Finsupp.single r 1)))) i
      =
        algebraMap P.Ring S (P.jacobiMatrix i r) := by
  let e : P.rels ≃ P.vars := Equiv.ofBijective P.map hbij
  have hcol :=
    Algebra.PreSubmersivePresentation.differentialsRelations_map_single_eq_jacobianColumn
      P hbij r
  have hi : e.symm (e i) = i := e.symm_apply_apply i
  calc
    (((LinearEquiv.funCongrLeft S S e).toLinearMap)
        ((Finsupp.linearEquivFunOnFinite S S P.vars)
          (P.toPresentation.differentialsRelations.map (Finsupp.single r 1)))) i
        =
          (Finsupp.linearEquivFunOnFinite S S P.vars
            (P.toPresentation.differentialsRelations.map (Finsupp.single r 1))) (e i) := rfl
    _ = algebraMap P.Ring S (P.jacobiMatrix (e.symm (e i)) r) :=
          congrFun hcol (e i)
    _ = algebraMap P.Ring S (P.jacobiMatrix i r) := by
          rw [hi]

/-- After identifying source and target finite free modules via a bijective
relation-to-variable map, the differentials relation map is the linear map
given by the Jacobian matrix. -/
theorem differentialsRelations_map_eq_toLin_jacobian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels] [Finite P.vars] [DecidableEq P.vars]
    (hbij : Function.Bijective P.map) :
    ((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap) ∘ₗ
        (Finsupp.linearEquivFunOnFinite S S P.vars).toLinearMap ∘ₗ
        P.toPresentation.differentialsRelations.map ∘ₗ
        (Finsupp.linearEquivFunOnFinite S S P.rels).symm.toLinearMap
      =
        Matrix.toLin
          (Pi.basisFun S P.rels)
          (Pi.basisFun S P.rels)
          ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix) := by
  classical
  let e : P.rels ≃ P.vars := Equiv.ofBijective P.map hbij
  ext r i
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  change
    (((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap)
        ((Finsupp.linearEquivFunOnFinite S S P.vars)
          (P.toPresentation.differentialsRelations.map
            ((Finsupp.linearEquivFunOnFinite S S P.rels).symm (Pi.single r (1 : S)))))) i
      =
        ((Matrix.toLin (Pi.basisFun S P.rels) (Pi.basisFun S P.rels))
          ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix)
          (Pi.single r 1)) i
  rw [Finsupp.linearEquivFunOnFinite_symm_single]
  rw [show Pi.single r (1 : S) = (Pi.basisFun S P.rels) r by
    exact (Pi.basisFun_apply S P.rels r).symm]
  change
    (((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap)
        ((Finsupp.linearEquivFunOnFinite S S P.vars)
          (P.toPresentation.differentialsRelations.map (Finsupp.single r 1)))) i
      =
        ((Matrix.toLin (Pi.basisFun S P.rels) (Pi.basisFun S P.rels))
          ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix)
          ((Pi.basisFun S P.rels) r)) i
  rw [Matrix.toLin_self]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    change
      (((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap)
          ((Finsupp.linearEquivFunOnFinite S S P.vars)
            (P.toPresentation.differentialsRelations.map (Finsupp.single r 1)))) i
        =
          algebraMap P.Ring S (P.jacobiMatrix i r)
    exact
      Algebra.PreSubmersivePresentation.transported_differentialsRelations_single_apply
        P hbij r i
  · intro j _hj hji
    rw [Pi.smul_apply, Pi.basisFun_apply, Pi.single_eq_of_ne' hji, smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- If the relation-to-variable map is bijective and the Jacobian is a unit,
then the differentials relation map is surjective. -/
theorem surjective_differentialsRelations_map_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels] [Finite P.vars] [DecidableEq P.vars]
    (hbij : Function.Bijective P.map)
    (hUnit : IsUnit P.jacobian) :
    Function.Surjective P.toPresentation.differentialsRelations.map := by
  classical
  let e : P.rels ≃ P.vars := Equiv.ofBijective P.map hbij
  let L :
      (P.rels → S) →ₗ[S] (P.rels → S) :=
    ((LinearEquiv.funCongrLeft S S e).toLinearMap) ∘ₗ
      (Finsupp.linearEquivFunOnFinite S S P.vars).toLinearMap ∘ₗ
      P.toPresentation.differentialsRelations.map ∘ₗ
      (Finsupp.linearEquivFunOnFinite S S P.rels).symm.toLinearMap
  have hTransport :
      L =
        Matrix.toLin
          (Pi.basisFun S P.rels)
          (Pi.basisFun S P.rels)
          ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix) := by
    change
      ((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap) ∘ₗ
          (Finsupp.linearEquivFunOnFinite S S P.vars).toLinearMap ∘ₗ
          P.toPresentation.differentialsRelations.map ∘ₗ
          (Finsupp.linearEquivFunOnFinite S S P.rels).symm.toLinearMap
        =
          Matrix.toLin
            (Pi.basisFun S P.rels)
            (Pi.basisFun S P.rels)
            ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix)
    exact Algebra.PreSubmersivePresentation.differentialsRelations_map_eq_toLin_jacobian P hbij
  have hDet :
      IsUnit (((algebraMap P.Ring S).mapMatrix P.jacobiMatrix).det) := by
    rw [← RingHom.map_det, ← P.jacobian_eq_jacobiMatrix_det]
    exact hUnit
  have hLsurj : Function.Surjective L := by
    rw [hTransport]
    exact LinearMap.range_eq_top.mp
      (Matrix.range_toLin_eq_top (b := Pi.basisFun S P.rels)
        ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix) hDet)
  intro y
  obtain ⟨x, hx⟩ := hLsurj
    (((LinearEquiv.funCongrLeft S S e).toLinearMap)
      ((Finsupp.linearEquivFunOnFinite S S P.vars) y))
  refine ⟨(Finsupp.linearEquivFunOnFinite S S P.rels).symm x, ?_⟩
  apply (Finsupp.linearEquivFunOnFinite S S P.vars).injective
  apply (LinearEquiv.funCongrLeft S S e).injective
  change
    (((LinearEquiv.funCongrLeft S S e).toLinearMap)
        ((Finsupp.linearEquivFunOnFinite S S P.vars)
          (P.toPresentation.differentialsRelations.map
            ((Finsupp.linearEquivFunOnFinite S S P.rels).symm x))))
      =
        (((LinearEquiv.funCongrLeft S S e).toLinearMap)
          ((Finsupp.linearEquivFunOnFinite S S P.vars) y))
  exact hx

/-- If the relation-to-variable map is bijective and the Jacobian is a unit,
then the differentials relation map is bijective. -/
theorem bijective_differentialsRelations_map_of_bijective
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.PreSubmersivePresentation R S)
    [Fintype P.rels] [DecidableEq P.rels] [Finite P.vars] [DecidableEq P.vars]
    (hbij : Function.Bijective P.map)
    (hUnit : IsUnit P.jacobian) :
    Function.Bijective P.toPresentation.differentialsRelations.map := by
  classical
  refine
    ⟨?_,
      Algebra.PreSubmersivePresentation.surjective_differentialsRelations_map_of_bijective
        P hbij hUnit⟩
  let e : P.rels ≃ P.vars := Equiv.ofBijective P.map hbij
  let L :
      (P.rels → S) →ₗ[S] (P.rels → S) :=
    ((LinearEquiv.funCongrLeft S S e).toLinearMap) ∘ₗ
      (Finsupp.linearEquivFunOnFinite S S P.vars).toLinearMap ∘ₗ
      P.toPresentation.differentialsRelations.map ∘ₗ
      (Finsupp.linearEquivFunOnFinite S S P.rels).symm.toLinearMap
  have hTransport :
      L =
        Matrix.toLin
          (Pi.basisFun S P.rels)
          (Pi.basisFun S P.rels)
          ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix) := by
    change
      ((LinearEquiv.funCongrLeft S S (Equiv.ofBijective P.map hbij)).toLinearMap) ∘ₗ
          (Finsupp.linearEquivFunOnFinite S S P.vars).toLinearMap ∘ₗ
          P.toPresentation.differentialsRelations.map ∘ₗ
          (Finsupp.linearEquivFunOnFinite S S P.rels).symm.toLinearMap
        =
          Matrix.toLin
            (Pi.basisFun S P.rels)
            (Pi.basisFun S P.rels)
            ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix)
    exact Algebra.PreSubmersivePresentation.differentialsRelations_map_eq_toLin_jacobian P hbij
  have hDet :
      IsUnit (((algebraMap P.Ring S).mapMatrix P.jacobiMatrix).det) := by
    rw [← RingHom.map_det, ← P.jacobian_eq_jacobiMatrix_det]
    exact hUnit
  have hLinj : Function.Injective L := by
    rw [hTransport]
    exact LinearMap.ker_eq_bot.mp
      (Matrix.ker_toLin_eq_bot (b := Pi.basisFun S P.rels)
        ((algebraMap P.Ring S).mapMatrix P.jacobiMatrix) hDet)
  intro x y hxy
  apply (Finsupp.linearEquivFunOnFinite S S P.rels).injective
  apply hLinj
  have hxy' :
      (((LinearEquiv.funCongrLeft S S e).toLinearMap)
          ((Finsupp.linearEquivFunOnFinite S S P.vars)
            (P.toPresentation.differentialsRelations.map x)))
        =
      (((LinearEquiv.funCongrLeft S S e).toLinearMap)
          ((Finsupp.linearEquivFunOnFinite S S P.vars)
            (P.toPresentation.differentialsRelations.map y))) := by
    exact congrArg
      (((LinearEquiv.funCongrLeft S S e).toLinearMap) ∘ₗ
        (Finsupp.linearEquivFunOnFinite S S P.vars).toLinearMap) hxy
  change
    (((LinearEquiv.funCongrLeft S S e).toLinearMap)
        ((Finsupp.linearEquivFunOnFinite S S P.vars)
          (P.toPresentation.differentialsRelations.map
            ((Finsupp.linearEquivFunOnFinite S S P.rels).symm
              ((Finsupp.linearEquivFunOnFinite S S P.rels) x)))))
      =
        (((LinearEquiv.funCongrLeft S S e).toLinearMap)
          ((Finsupp.linearEquivFunOnFinite S S P.vars)
            (P.toPresentation.differentialsRelations.map
              ((Finsupp.linearEquivFunOnFinite S S P.rels).symm
                ((Finsupp.linearEquivFunOnFinite S S P.rels) y)))))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact hxy'

end PreSubmersivePresentation
end _root_.Algebra

end

end Boundary
