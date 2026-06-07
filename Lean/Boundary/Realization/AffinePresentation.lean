import Geometry.Schemes.Basic
import Mathlib.RingTheory.FinitePresentation

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Boundary
namespace Realization

variable {k : Type u} [Field k] [PerfectField k]

/-- The base global-sections ring `Γ(Spec k, ⊤)`. This is canonically isomorphic to `k`,
but keeping the owner construction at the level of global sections avoids introducing
noncanonical scalar-identification choices into affine presentation theorems. -/
abbrev smBaseSectionRing :=
  Γ(Spec (CommRingCat.of k), ⊤)

/-- The canonical ring equivalence from the base field to the section ring of `Spec k`. -/
abbrev smBaseSectionRingEquiv :
    k ≃+* smBaseSectionRing (k := k) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv

/-- The ring hom on sections of an affine open in a smooth `k`-scheme,
induced by the structure map to `Spec k`. -/
abbrev smAffineOpenSectionRingHom
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    smBaseSectionRing (k := k) →+*
      Γ(X.scheme, (U : X.scheme.Opens)) :=
  X.structMap.appLE ⊤ U (by simp)

/-- Sections on an affine open of a smooth finite-type `k`-scheme are of finite type over
the base global-sections ring. -/
theorem smAffineOpenSections_finiteType
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
      (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
    Algebra.FiniteType (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  exact (Geometry.SmSchemeOver.locallyOfFiniteType_structMap X).finiteType_of_affine_subset
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ U (by simp)

/-- Sections on an affine open of a smooth finite-type `k`-scheme are finitely presented over
the base global-sections ring. Since `k` is a field, `Γ(Spec k, ⊤)` is Noetherian. -/
theorem smAffineOpenSections_finitePresentation
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
      (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
    Algebra.FinitePresentation (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  letI : IsNoetherianRing (smBaseSectionRing (k := k)) := by
    apply isNoetherianRing_of_ringEquiv k
    exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  exact
    (Algebra.FinitePresentation.of_finiteType
      (R := smBaseSectionRing (k := k))
      (A := Γ(X.scheme, (U : X.scheme.Opens)))).mp
      (smAffineOpenSections_finiteType (k := k) X U)

/-- An affine open in a smooth finite-type `k`-scheme admits a quotient presentation by a
polynomial ring in finitely many variables over `Γ(Spec k, ⊤)`. -/
theorem smAffineOpenSections_quotient_mvPolynomial
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
      (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
    ∃ (n : ℕ)
      (f : MvPolynomial (Fin n) (smBaseSectionRing (k := k)) →ₐ[smBaseSectionRing (k := k)]
        Γ(X.scheme, (U : X.scheme.Opens))), Function.Surjective f := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  exact
    (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp
      (smAffineOpenSections_finiteType (k := k) X U)

/-- An affine open in a smooth finite-type `k`-scheme admits a quotient presentation by a
polynomial ring over the actual base field `k`. This is the affine algebra input needed
for constructing complex-point models when `k = ℂ`. -/
theorem smAffineOpenSections_quotient_mvPolynomial_baseField
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →+* Γ(X.scheme, (U : X.scheme.Opens))),
      Function.Surjective f := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  obtain ⟨n, f, hf⟩ := smAffineOpenSections_quotient_mvPolynomial (k := k) X U
  refine ⟨n, f.toRingHom.comp (MvPolynomial.mapEquiv (Fin n) (smBaseSectionRingEquiv (k := k))).toRingHom, ?_⟩
  intro x
  rcases hf x with ⟨p, rfl⟩
  refine ⟨(MvPolynomial.mapEquiv (Fin n) (smBaseSectionRingEquiv (k := k))).symm p, ?_⟩
  exact congrArg f ((MvPolynomial.mapEquiv (Fin n) (smBaseSectionRingEquiv (k := k))).apply_symm_apply p)

/-- An affine open in a smooth finite-type `k`-scheme admits a finitely presented polynomial
quotient over `Γ(Spec k, ⊤)`: finitely many variables and a finitely generated kernel. -/
theorem smAffineOpenSections_finitePresentation_data
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
      (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
    ∃ (n : ℕ)
      (f : MvPolynomial (Fin n) (smBaseSectionRing (k := k)) →ₐ[smBaseSectionRing (k := k)]
        Γ(X.scheme, (U : X.scheme.Opens))),
        Function.Surjective f ∧ f.toRingHom.ker.FG := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  letI : Algebra.FinitePresentation (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    smAffineOpenSections_finitePresentation (k := k) X U
  exact
    Algebra.FinitePresentation.out
      (R := smBaseSectionRing (k := k))
      (A := Γ(X.scheme, (U : X.scheme.Opens)))

/-- An affine open in a smooth finite-type `k`-scheme admits a finitely presented polynomial
quotient over the actual base field `k`: finitely many variables and a finitely generated
relation ideal. This is the algebraic input needed to cut out affine `ℂ`-points by finitely
many equations when `k = ℂ`. -/
theorem smAffineOpenSections_finitePresentation_data_baseField
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →+* Γ(X.scheme, (U : X.scheme.Opens))),
      Function.Surjective f ∧ f.ker.FG := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  obtain ⟨n, f, hf, hker⟩ := smAffineOpenSections_finitePresentation_data (k := k) X U
  let e : MvPolynomial (Fin n) k ≃+* MvPolynomial (Fin n) (smBaseSectionRing (k := k)) :=
    MvPolynomial.mapEquiv (Fin n) (smBaseSectionRingEquiv (k := k))
  refine ⟨n, f.toRingHom.comp e.toRingHom, ?_, ?_⟩
  · intro x
    rcases hf x with ⟨p, rfl⟩
    refine ⟨e.symm p, ?_⟩
    exact congrArg f (e.apply_symm_apply p)
  · refine Ideal.fg_ker_comp e.toRingHom f.toRingHom ?_ hker e.surjective
    erw [RingHom.ker_coe_equiv e]
    exact Submodule.fg_bot

/-- The relation ideal of an affine open in a smooth finite-type `k`-scheme can be generated by
finitely many explicit polynomials over `k`. This is the direct affine zero-locus input for
Betti-style complex points when `k = ℂ`. -/
theorem smAffineOpenSections_finiteEquations_baseField
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    ∃ (n m : ℕ) (f : MvPolynomial (Fin n) k →+* Γ(X.scheme, (U : X.scheme.Opens)))
      (p : Fin m → MvPolynomial (Fin n) k),
      Function.Surjective f ∧ Ideal.span (Set.range p) = RingHom.ker f := by
  obtain ⟨n, f, hf, hker⟩ := smAffineOpenSections_finitePresentation_data_baseField (k := k) X U
  obtain ⟨m, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  refine ⟨n, m, f, p, hf, ?_⟩
  exact hp

/-- The base-field affine presentation can be chosen as an actual `k`-algebra hom on sections. -/
theorem smAffineOpenSections_finitePresentationDataAlgHom_baseField
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    letI : Algebra k Γ(X.scheme, (U : X.scheme.Opens)) :=
      (((smAffineOpenSectionRingHom (k := k) X U).comp
        (smBaseSectionRingEquiv (k := k)).toRingHom).toAlgebra)
    ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] Γ(X.scheme, (U : X.scheme.Opens))),
      Function.Surjective f ∧ f.toRingHom.ker.FG := by
  letI : Algebra (smBaseSectionRing (k := k)) Γ(X.scheme, (U : X.scheme.Opens)) :=
    (smAffineOpenSectionRingHom (k := k) X U).toAlgebra
  letI : Algebra k Γ(X.scheme, (U : X.scheme.Opens)) :=
    (((smAffineOpenSectionRingHom (k := k) X U).comp
      (smBaseSectionRingEquiv (k := k)).toRingHom).toAlgebra)
  obtain ⟨n, f, hf, hker⟩ := smAffineOpenSections_finitePresentation_data (k := k) X U
  let e : MvPolynomial (Fin n) k ≃+* MvPolynomial (Fin n) (smBaseSectionRing (k := k)) :=
    MvPolynomial.mapEquiv (Fin n) (smBaseSectionRingEquiv (k := k))
  let f' : MvPolynomial (Fin n) k →ₐ[k] Γ(X.scheme, (U : X.scheme.Opens)) :=
    { toRingHom := f.toRingHom.comp e.toRingHom
      commutes' := by
        intro c
        change f (e (MvPolynomial.C c)) = _
        calc
          f (e (MvPolynomial.C c))
              = f (MvPolynomial.C ((smBaseSectionRingEquiv (k := k)) c)) := by
                  simp [e]
          _ = algebraMap (smBaseSectionRing (k := k)) _ ((smBaseSectionRingEquiv (k := k)) c) := by
                simp
          _ = algebraMap k Γ(X.scheme, (U : X.scheme.Opens)) c := rfl }
  haveI : RingHomSurjective f.toRingHom := ⟨hf⟩
  refine ⟨n, f', ?_, ?_⟩
  · intro y
    rcases hf y with ⟨z, rfl⟩
    rcases e.surjective z with ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  exact Ideal.fg_ker_comp e.toRingHom f.toRingHom
    (by
      erw [RingHom.ker_coe_equiv e]
      exact Submodule.fg_bot)
    hker e.surjective

/-- The base-field affine presentation can be chosen as an actual finite family of equations for
the kernel of a `k`-algebra hom on sections. -/
theorem smAffineOpenSections_finiteEquationsAlgHom_baseField
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    letI : Algebra k Γ(X.scheme, (U : X.scheme.Opens)) :=
      (((smAffineOpenSectionRingHom (k := k) X U).comp
        (smBaseSectionRingEquiv (k := k)).toRingHom).toAlgebra)
    ∃ (n m : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] Γ(X.scheme, (U : X.scheme.Opens)))
      (p : Fin m → MvPolynomial (Fin n) k),
      Function.Surjective f ∧ Ideal.span (Set.range p) = RingHom.ker f.toRingHom := by
  letI : Algebra k Γ(X.scheme, (U : X.scheme.Opens)) :=
    (((smAffineOpenSectionRingHom (k := k) X U).comp
      (smBaseSectionRingEquiv (k := k)).toRingHom).toAlgebra)
  obtain ⟨n, f, hf, hker⟩ :=
    smAffineOpenSections_finitePresentationDataAlgHom_baseField (k := k) X U
  obtain ⟨m, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  refine ⟨n, m, f, p, hf, ?_⟩
  exact hp

end Realization
end Boundary
