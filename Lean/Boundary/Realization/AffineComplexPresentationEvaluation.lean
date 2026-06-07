import Boundary.Realization.AffineComplexModelMaps

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Boundary
namespace Realization

/-- A point of a finite polynomial zero locus induces a canonical `ℂ`-algebra point of any affine
presentation with that relation ideal, by evaluation and descent through the quotient by the kernel
of the presentation map. -/
noncomputable def affineComplexPointsOfPresentation
    {n m : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    (fA : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hfA : Function.Surjective fA)
    (hp : Ideal.span (Set.range p) = RingHom.ker fA.toRingHom) :
    finitePolynomialZeroSet p → (A →ₐ[ℂ] ℂ) :=
  fun z =>
    let evalz : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ := MvPolynomial.aeval z.1
    let hker : ∀ φ : MvPolynomial (Fin n) ℂ, φ ∈ RingHom.ker fA.toRingHom → evalz φ = 0 := by
      intro φ hφ
      apply eval_eq_zero_of_mem_span z.2
      simpa [hp] using hφ
    (Ideal.Quotient.liftₐ (RingHom.ker fA.toRingHom) evalz hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective (f := fA) hfA).symm.toAlgHom

@[simp]
theorem affineComplexPointsOfPresentation_apply
    {n m : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    (fA : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hfA : Function.Surjective fA)
    (hp : Ideal.span (Set.range p) = RingHom.ker fA.toRingHom)
    (z : finitePolynomialZeroSet p)
    (φ : MvPolynomial (Fin n) ℂ) :
    affineComplexPointsOfPresentation fA p hfA hp z (fA φ) =
      MvPolynomial.eval z.1 φ := by
  have hq :
      (Ideal.quotientKerAlgEquivOfSurjective hfA).symm (fA φ) =
        Ideal.Quotient.mk (RingHom.ker fA.toRingHom) φ := by
    apply (Ideal.quotientKerAlgEquivOfSurjective hfA).symm_apply_eq.mpr
    have h := Ideal.quotientKerAlgEquivOfSurjective_apply (f := fA) hfA
      (Ideal.Quotient.mk (RingHom.ker fA.toRingHom) φ)
    exact h.symm
  dsimp [affineComplexPointsOfPresentation]
  change
    Ideal.Quotient.liftₐ (RingHom.ker fA.toRingHom) (MvPolynomial.aeval z.1)
      (fun ψ hψ => by
        apply eval_eq_zero_of_mem_span z.2
        rw [← hp] at hψ
        exact hψ)
      ((Ideal.quotientKerAlgEquivOfSurjective hfA).symm.toAlgHom (fA φ)) =
    MvPolynomial.eval z.1 φ
  have hq' :
      ((Ideal.quotientKerAlgEquivOfSurjective hfA).symm.toAlgHom) (fA φ) =
        Ideal.Quotient.mk (RingHom.ker fA.toRingHom) φ := hq
  rw [hq', Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

@[simp]
theorem affineComplexPointsOfPresentation_X
    {n m : ℕ} {A : Type*} [CommRing A] [Algebra ℂ A]
    (fA : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)
    (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hfA : Function.Surjective fA)
    (hp : Ideal.span (Set.range p) = RingHom.ker fA.toRingHom)
    (z : finitePolynomialZeroSet p)
    (i : Fin n) :
    affineComplexPointsOfPresentation fA p hfA hp z (fA (MvPolynomial.X i)) = z.1 i := by
  rw [affineComplexPointsOfPresentation_apply]
  rw [MvPolynomial.eval_X]

/-- For an affine open in `Sm/ℂ`, one can choose a finite polynomial model whose identity
map is realized by the coordinate tuple `X`. -/
theorem smAffineOpen_exists_affineComplexModel_id
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens) :
    ∃ (m r : ℕ)
      (fU : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (U : X.scheme.Opens)))
      (p : Fin r → MvPolynomial (Fin m) ℂ),
      Function.Surjective fU ∧
        Ideal.span (Set.range p) = RingHom.ker fU.toRingHom ∧
        finitePolynomialZeroSetMap p (fun i : Fin m => MvPolynomial.X i) p
          (fun i => by
            change
              (MvPolynomial.bind₁ (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℂ)) (p i) ∈
                Ideal.span (Set.range p)
            rw [MvPolynomial.bind₁_X_left]
            exact
              (Ideal.subset_span ⟨i, rfl⟩ :
                p i ∈ Ideal.span (Set.range p))) = id := by
  obtain ⟨m, r, fU, p, hfU, hpU⟩ :=
    smAffineOpenSections_finiteEquationsAlgHom_baseField (X := X) (U := U)
  refine ⟨m, r, fU, p, hfU, hpU, ?_⟩
  exact finitePolynomialZeroSetMap_id p

/-- If the chosen affine presentation sends the coordinate variables to themselves under the
identity section map, then the local affine complex-model map for the identity morphism is `id`. -/
theorem smOverHom_affineComplexModelMap_id
    (X : Geometry.SmSchemeOver ℂ) (U : X.scheme.affineOpens)
    {m r : ℕ}
    (fU : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (U : X.scheme.Opens)))
    (p : Fin r → MvPolynomial (Fin m) ℂ)
    (hfU : Function.Surjective fU)
    (hpU : Ideal.span (Set.range p) = RingHom.ker fU.toRingHom)
    (hX : ∀ i : Fin m,
      affinePresentationLiftTuple fU fU (smOverHom_appLEAlgHom (X := X) (Y := X) (𝟙 X) U U le_rfl) hfU i =
        MvPolynomial.X i) :
    smOverHom_affineComplexModelMap (X := X) (Y := X) (𝟙 X) U U le_rfl
      fU p fU p hfU hpU hpU = id := by
  ext z i
  rw [smOverHom_affineComplexModelMap_coe]
  simpa [finitePolynomialMap, smOverHom_appLEAlgHom_id] using
    congrArg (MvPolynomial.eval z.1) (hX i)

end Realization
end Boundary
