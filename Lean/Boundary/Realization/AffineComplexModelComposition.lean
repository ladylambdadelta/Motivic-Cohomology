import Boundary.Realization.AffineComplexPointsBridge

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Boundary
namespace Realization

/-! The composition formulas for the affine complex-model maps are kept in a separate owner file.
They are downstream of the presentation-lift API, but still upstream of the chosen-model
continuity bridge. -/

/-! The substituted polynomial tuple attached to two composable affine-open section maps
realizes the composite section map on target coordinate functions. -/
set_option maxHeartbeats 400000 in
theorem smOverHom_affinePresentation_bind₁_comp_spec
    {X Y Z : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y) (g : Boundary.SmOverHom Y Z)
    (U : Z.scheme.affineOpens) (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
    (e₁ : (V : Y.scheme.Opens) ≤ g.hom ⁻¹ᵁ (U : Z.scheme.Opens))
    (e₂ : (W : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (V : Y.scheme.Opens))
    {m n l : ℕ}
    (fW : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (W : X.scheme.Opens)))
    (fV : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.scheme, (V : Y.scheme.Opens)))
    (fU : MvPolynomial (Fin l) ℂ →ₐ[ℂ] Γ(Z.scheme, (U : Z.scheme.Opens)))
    (hfW : Function.Surjective fW)
    (hfV : Function.Surjective fV) :
    let qf := affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW
    let qg := affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV
    let qfg : Fin l → MvPolynomial (Fin m) ℂ := fun i => MvPolynomial.bind₁ qf (qg i)
    ∀ i,
      fW (qfg i) =
        (smOverHom_appLEAlgHom (Boundary.SmOverHom.comp f g) U W
          (by
            simpa [Boundary.SmOverHom.comp] using
              (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
                e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le)))
          (fU (MvPolynomial.X i)) := by
  dsimp
  intro i
  calc
    fW (MvPolynomial.bind₁
        (affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW)
        (affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV i))
      = (smOverHom_appLEAlgHom f V W e₂)
          (fV (affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV i)) := by
            exact affinePresentation_bind₁_eval
              fW fV (smOverHom_appLEAlgHom f V W e₂)
              (affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW)
              (affinePresentationLiftTuple_spec fW fV (smOverHom_appLEAlgHom f V W e₂) hfW)
              _
    _ = (smOverHom_appLEAlgHom f V W e₂)
          ((smOverHom_appLEAlgHom g U V e₁) (fU (MvPolynomial.X i))) := by
            rw [affinePresentationLiftTuple_spec fV fU (smOverHom_appLEAlgHom g U V e₁) hfV i]
    _ = (smOverHom_appLEAlgHom (Boundary.SmOverHom.comp f g) U W
          (by
            simpa [Boundary.SmOverHom.comp] using
              (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
                e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le)))
          (fU (MvPolynomial.X i)) := by
            have hcomp := smOverHom_appLEAlgHom_comp f g U V W e₁ e₂
            exact congrArg (fun h =>
              h (fU (MvPolynomial.X i))) hcomp

/-- The substituted tuple for two composable affine-open section maps satisfies the
ideal-compatibility condition for the composite section map. -/
theorem smOverHom_affinePresentation_bind₁_comp_generators_mem_span
    {X Y Z : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y) (g : Boundary.SmOverHom Y Z)
    (U : Z.scheme.affineOpens) (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
    (e₁ : (V : Y.scheme.Opens) ≤ g.hom ⁻¹ᵁ (U : Z.scheme.Opens))
    (e₂ : (W : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (V : Y.scheme.Opens))
    {m n l r t : ℕ}
    (fW : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (W : X.scheme.Opens)))
    (p : Fin r → MvPolynomial (Fin m) ℂ)
    (fV : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.scheme, (V : Y.scheme.Opens)))
    (fU : MvPolynomial (Fin l) ℂ →ₐ[ℂ] Γ(Z.scheme, (U : Z.scheme.Opens)))
    (w : Fin t → MvPolynomial (Fin l) ℂ)
    (hfW : Function.Surjective fW)
    (hfV : Function.Surjective fV)
    (hp : Ideal.span (Set.range p) = RingHom.ker fW.toRingHom)
    (hw : Ideal.span (Set.range w) = RingHom.ker fU.toRingHom) :
    let qf := affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW
    let qg := affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV
    let qfg : Fin l → MvPolynomial (Fin m) ℂ := fun i => MvPolynomial.bind₁ qf (qg i)
    ∀ i, MvPolynomial.bind₁ qfg (w i) ∈ Ideal.span (Set.range p) := by
  dsimp
  let qfg : Fin l → MvPolynomial (Fin m) ℂ :=
    fun i => MvPolynomial.bind₁
      (affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW)
      (affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV i)
  refine affinePresentation_bind₁_generators_mem_span
    fW fU
    (smOverHom_appLEAlgHom (Boundary.SmOverHom.comp f g) U W
      (by
        simpa [Boundary.SmOverHom.comp] using
          (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
            e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le)))
    p w hp hw qfg ?_
  intro i
  change fW
      (MvPolynomial.bind₁
        (affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW)
        (affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV i)) =
    (smOverHom_appLEAlgHom (Boundary.SmOverHom.comp f g) U W
      (by
        simpa [Boundary.SmOverHom.comp] using
          (show (W : X.scheme.Opens) ≤ (f.hom ≫ g.hom) ⁻¹ᵁ (U : Z.scheme.Opens) from
            e₂.trans ((TopologicalSpace.Opens.map f.hom.base).map (homOfLE e₁)).le)))
      (fU (MvPolynomial.X i))
  exact smOverHom_affinePresentation_bind₁_comp_spec
    f g U V W e₁ e₂ fW fV fU hfW hfV i

/-- For composable morphisms in `Sm/ℂ`, the induced affine complex-model maps compose as the
single-step map defined by substituting the chosen polynomial lift tuples. -/
theorem smOverHom_affineComplexModelMap_comp
    {X Y Z : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y) (g : Boundary.SmOverHom Y Z)
    (U : Z.scheme.affineOpens) (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
    (e₁ : (V : Y.scheme.Opens) ≤ g.hom ⁻¹ᵁ (U : Z.scheme.Opens))
    (e₂ : (W : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (V : Y.scheme.Opens))
    {m n l r s t : ℕ}
    (fW : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (W : X.scheme.Opens)))
    (p : Fin r → MvPolynomial (Fin m) ℂ)
    (fV : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.scheme, (V : Y.scheme.Opens)))
    (v : Fin s → MvPolynomial (Fin n) ℂ)
    (fU : MvPolynomial (Fin l) ℂ →ₐ[ℂ] Γ(Z.scheme, (U : Z.scheme.Opens)))
    (w : Fin t → MvPolynomial (Fin l) ℂ)
    (hfW : Function.Surjective fW)
    (hfV : Function.Surjective fV)
    (hp : Ideal.span (Set.range p) = RingHom.ker fW.toRingHom)
    (hv : Ideal.span (Set.range v) = RingHom.ker fV.toRingHom)
    (hw : Ideal.span (Set.range w) = RingHom.ker fU.toRingHom) :
    let qf := affinePresentationLiftTuple fW fV (smOverHom_appLEAlgHom f V W e₂) hfW
    let qg := affinePresentationLiftTuple fV fU (smOverHom_appLEAlgHom g U V e₁) hfV
    let hqf :
        ∀ i, MvPolynomial.bind₁ qf (v i) ∈ Ideal.span (Set.range p) :=
      affinePresentation_liftTuple_generators_mem_span
        fW fV (smOverHom_appLEAlgHom f V W e₂) hfW p v hp hv
    let hqg :
        ∀ i, MvPolynomial.bind₁ qg (w i) ∈ Ideal.span (Set.range v) :=
      affinePresentation_liftTuple_generators_mem_span
        fV fU (smOverHom_appLEAlgHom g U V e₁) hfV v w hv hw
    let qfg : Fin l → MvPolynomial (Fin m) ℂ := fun i => MvPolynomial.bind₁ qf (qg i)
    let hqfg :
        ∀ i, MvPolynomial.bind₁ qfg (w i) ∈ Ideal.span (Set.range p) := by
      intro i
      simpa [qfg, MvPolynomial.bind₁_bind₁] using bind₁_mem_span_of_range p qf v hqf (hqg i)
    finitePolynomialZeroSetMap v qg w hqg ∘ finitePolynomialZeroSetMap p qf v hqf =
      finitePolynomialZeroSetMap p qfg w hqfg := by
  dsimp
  exact finitePolynomialZeroSetMap_comp p _ _ v w _ _


end Realization
end Boundary
