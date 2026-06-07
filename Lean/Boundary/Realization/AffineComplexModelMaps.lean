import Boundary.Realization.AffineComplexPolynomials

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Boundary
namespace Realization

/-- The affine complex-model map attached to a morphism in `Sm/ℂ` and chosen affine polynomial
presentations of source and target section rings. -/
noncomputable def smOverHom_affineComplexModelMap
    {X Y : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
  (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens))
    {m n r s : ℕ}
    (fV : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (V : X.scheme.Opens)))
    (p : Fin r → MvPolynomial (Fin m) ℂ)
    (fU : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.scheme, (U : Y.scheme.Opens)))
    (t : Fin s → MvPolynomial (Fin n) ℂ)
    (hfV : Function.Surjective fV)
    (hpV : Ideal.span (Set.range p) = RingHom.ker fV.toRingHom)
    (htU : Ideal.span (Set.range t) = RingHom.ker fU.toRingHom) :
    finitePolynomialZeroSet p → finitePolynomialZeroSet t :=
  let g : Γ(Y.scheme, (U : Y.scheme.Opens)) →ₐ[ℂ] Γ(X.scheme, (V : X.scheme.Opens)) :=
    smOverHom_appLEAlgHom f U V e
  let q :=
    @affinePresentationLiftTuple
      (m := m) (n := n)
      (A := Γ(X.scheme, (V : X.scheme.Opens)))
      (B := Γ(Y.scheme, (U : Y.scheme.Opens)))
      _ _ _ _
      fV fU g hfV
  let hq :
      ∀ i, MvPolynomial.bind₁ q (t i) ∈ Ideal.span (Set.range p) :=
    @affinePresentation_liftTuple_generators_mem_span
      (m := m) (n := n) (r := r) (s := s)
      (A := Γ(X.scheme, (V : X.scheme.Opens)))
      (B := Γ(Y.scheme, (U : Y.scheme.Opens)))
      _ _ _ _
      fV fU g hfV p t hpV htU
  finitePolynomialZeroSetMap p q t hq

@[simp]
theorem smOverHom_affineComplexModelMap_coe
    {X Y : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens))
    {m n r s : ℕ}
    (fV : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (V : X.scheme.Opens)))
    (p : Fin r → MvPolynomial (Fin m) ℂ)
    (fU : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.scheme, (U : Y.scheme.Opens)))
    (t : Fin s → MvPolynomial (Fin n) ℂ)
  (hfV : Function.Surjective fV)
  (hpV : Ideal.span (Set.range p) = RingHom.ker fV.toRingHom)
  (htU : Ideal.span (Set.range t) = RingHom.ker fU.toRingHom)
  (z : finitePolynomialZeroSet p) :
  (smOverHom_affineComplexModelMap f U V e fV p fU t hfV hpV htU z : Fin n → ℂ) =
      finitePolynomialMap
        (@affinePresentationLiftTuple
          (m := m) (n := n)
          (A := Γ(X.scheme, (V : X.scheme.Opens)))
          (B := Γ(Y.scheme, (U : Y.scheme.Opens)))
          _ _ _ _
          fV fU (smOverHom_appLEAlgHom f U V e) hfV)
        z.1 := by
  simp [smOverHom_affineComplexModelMap]

theorem smOverHom_affineComplexModelMap_continuous
    {X Y : Geometry.SmSchemeOver ℂ}
    (f : Boundary.SmOverHom X Y)
    (U : Y.scheme.affineOpens) (V : X.scheme.affineOpens)
    (e : (V : X.scheme.Opens) ≤ f.hom ⁻¹ᵁ (U : Y.scheme.Opens))
    {m n r s : ℕ}
    (fV : MvPolynomial (Fin m) ℂ →ₐ[ℂ] Γ(X.scheme, (V : X.scheme.Opens)))
    (p : Fin r → MvPolynomial (Fin m) ℂ)
  (fU : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Γ(Y.scheme, (U : Y.scheme.Opens)))
  (t : Fin s → MvPolynomial (Fin n) ℂ)
  (hfV : Function.Surjective fV)
  (hpV : Ideal.span (Set.range p) = RingHom.ker fV.toRingHom)
  (htU : Ideal.span (Set.range t) = RingHom.ker fU.toRingHom) :
  Continuous (smOverHom_affineComplexModelMap f U V e fV p fU t hfV hpV htU) := by
  simp [smOverHom_affineComplexModelMap]
  exact continuous_finitePolynomialZeroSetMap p
    (@affinePresentationLiftTuple
      (m := m) (n := n)
      (A := Γ(X.scheme, (V : X.scheme.Opens)))
      (B := Γ(Y.scheme, (U : Y.scheme.Opens)))
      _ _ _ _
      fV fU (smOverHom_appLEAlgHom f U V e) hfV)
    t
    (@affinePresentation_liftTuple_generators_mem_span
      (m := m) (n := n) (r := r) (s := s)
      (A := Γ(X.scheme, (V : X.scheme.Opens)))
      (B := Γ(Y.scheme, (U : Y.scheme.Opens)))
      _ _ _ _
      fV fU (smOverHom_appLEAlgHom f U V e) hfV p t hpV htU)

end Realization
end Boundary
