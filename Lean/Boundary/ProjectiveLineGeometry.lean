import Boundary.A1Geometry
import Boundary.SmOver
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Boundary-side projective line geometry

This file is the Boundary-side owner for the projective line.

It provides the raw projective scheme `Proj(k[x₀, x₁])`, the induced map to the
base `Spec k`, affine chart computations, smoothness and finite-type proofs,
the resulting object of `Sm/k`, and its canonical basepoint.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

variable (k : Type u) [Field k] [PerfectField k]

/-- The standard degree grading on the homogeneous coordinate ring `k[x₀, x₁]`. -/
abbrev boundaryProjectiveLineGrading : ℕ → Submodule k (MvPolynomial (Fin 2) k) :=
  MvPolynomial.homogeneousSubmodule (Fin 2) k

local instance boundaryProjectiveLineGradedMonoid :
    SetLike.GradedMonoid (boundaryProjectiveLineGrading k) :=
  MvPolynomial.HomogeneousSubmodule.gradedMonoid

local instance boundaryProjectiveLineGradedAlgebra :
    GradedAlgebra (boundaryProjectiveLineGrading k) :=
  MvPolynomial.gradedAlgebra

/-- The raw projective scheme `Proj(k[x₀, x₁])`. -/
abbrev boundaryProjectiveLineScheme : Scheme :=
  AlgebraicGeometry.Proj (boundaryProjectiveLineGrading k)

/-- The two standard homogeneous coordinates on `k[x₀, x₁]`. -/
abbrev boundaryProjectiveLineCoordinate (i : Fin 2) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X i

theorem boundaryProjectiveLineCoordinate_mem_degree_one (i : Fin 2) :
    boundaryProjectiveLineCoordinate k i ∈ boundaryProjectiveLineGrading k 1 := by
  exact
    (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 2) (R := k) 1
      (boundaryProjectiveLineCoordinate k i)).2 <|
      by
        simpa [boundaryProjectiveLineCoordinate] using
          (MvPolynomial.isHomogeneous_X (σ := Fin 2) (R := k) i)

/-- The degree-zero subring of the homogeneous coordinate ring. -/
abbrev boundaryProjectiveLineDegreeZeroRing : Type _ :=
  ↥(boundaryProjectiveLineGrading k 0)

/-- Constants in `k` define degree-zero homogeneous polynomials. -/
abbrev boundaryProjectiveLineDegreeZeroRingHom :
    k →+* boundaryProjectiveLineDegreeZeroRing k :=
  { toFun := fun a => ⟨MvPolynomial.C a,
      (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 2) (R := k) 0
        (MvPolynomial.C a)).2 <|
        MvPolynomial.isHomogeneous_C (σ := Fin 2) (R := k) a⟩
    map_one' := Subtype.ext <| by simp
    map_mul' := by
      intro a b
      exact Subtype.ext <| by simp
    map_zero' := Subtype.ext <| by simp
    map_add' := by
      intro a b
      exact Subtype.ext <| by simp }

/-- The homogeneous degree-zero localization away from the `i`-th coordinate. -/
abbrev boundaryProjectiveLineCoordinateAwayRing (i : Fin 2) :=
  HomogeneousLocalization.Away
    (boundaryProjectiveLineGrading k)
    (boundaryProjectiveLineCoordinate k i)

/-- The homogeneous-localization value map as an additive map. This is the
normalization bridge used to push finite support sums from the degree-zero
homogeneous localization into the ordinary Away localization. -/
def boundaryProjectiveLineHomogeneousLocalizationValAddMonoidHom (i : Fin 2) :
    boundaryProjectiveLineCoordinateAwayRing (k := k) i →+
      Localization.Away (boundaryProjectiveLineCoordinate k i) where
  toFun := HomogeneousLocalization.val
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

/-- Dehomogenization on the `x₀` chart sends `x₀ ↦ 1` and `x₁ ↦ t`. -/
abbrev boundaryProjectiveLineX0Dehom : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom (Polynomial.C : k →+* Polynomial k)
    (fun i : Fin 2 => Fin.cases (1 : Polynomial k) (fun _ => Polynomial.X) i)

theorem boundaryProjectiveLineX0Dehom_coordinate_zero :
    boundaryProjectiveLineX0Dehom (k := k) (boundaryProjectiveLineCoordinate k 0) = 1 := by
  simp [boundaryProjectiveLineX0Dehom, boundaryProjectiveLineCoordinate]

theorem boundaryProjectiveLineX0Dehom_monomial
    (d : Fin 2 →₀ ℕ) (a : k) :
    boundaryProjectiveLineX0Dehom (k := k) (MvPolynomial.monomial d a) =
      Polynomial.C a * Polynomial.X ^ d 1 := by
  rw [boundaryProjectiveLineX0Dehom, MvPolynomial.eval₂Hom_monomial]
  simpa [Fin.prod_univ_succ, mul_assoc, mul_left_comm, mul_comm]

/-- The forward chart map on `Away x₀`, viewed through the underlying localization. -/
abbrev boundaryProjectiveLineX0AwayToPolynomial :
    boundaryProjectiveLineCoordinateAwayRing (k := k) 0 →+* Polynomial k := by
  let liftMap : Localization.Away (boundaryProjectiveLineCoordinate k 0) →+* Polynomial k :=
    Localization.awayLift (boundaryProjectiveLineX0Dehom (k := k))
      (boundaryProjectiveLineCoordinate k 0)
      (by
        rw [boundaryProjectiveLineX0Dehom_coordinate_zero (k := k)]
        exact isUnit_one)
  let valMap : HomogeneousLocalization.Away (boundaryProjectiveLineGrading k)
      (boundaryProjectiveLineCoordinate k 0) →+*
        Localization.Away (boundaryProjectiveLineCoordinate k 0) :=
    algebraMap _ _
  exact RingHom.comp liftMap valMap

/-- Constants in `k` give degree-zero classes on the `x₀` chart. -/
abbrev boundaryProjectiveLineX0ConstantsToAway :
    k →+* boundaryProjectiveLineCoordinateAwayRing (k := k) 0 :=
  (HomogeneousLocalization.fromZeroRingHom
      (boundaryProjectiveLineGrading k)
      (Submonoid.powers (boundaryProjectiveLineCoordinate k 0))).comp
    (boundaryProjectiveLineDegreeZeroRingHom k)

/-- The affine coordinate `t = x₁ / x₀` on the `x₀` chart. -/
def boundaryProjectiveLineX0AffineCoordinate :
    boundaryProjectiveLineCoordinateAwayRing (k := k) 0 :=
  HomogeneousLocalization.mk
    ⟨1,
      ⟨boundaryProjectiveLineCoordinate k 1,
        boundaryProjectiveLineCoordinate_mem_degree_one k 1⟩,
      ⟨boundaryProjectiveLineCoordinate k 0,
        boundaryProjectiveLineCoordinate_mem_degree_one k 0⟩,
      by
        refine ⟨1, ?_⟩
        simp [boundaryProjectiveLineCoordinate]⟩

/-- The inverse-direction ring map for the `x₀` chart, sending `t` to `x₁ / x₀`. -/
abbrev boundaryProjectiveLineX0PolynomialToAway :
    Polynomial k →+* boundaryProjectiveLineCoordinateAwayRing (k := k) 0 :=
  Polynomial.eval₂RingHom
    (boundaryProjectiveLineX0ConstantsToAway (k := k))
    (boundaryProjectiveLineX0AffineCoordinate (k := k))

@[simp] theorem boundaryProjectiveLineX0PolynomialToAway_C (a : k) :
    boundaryProjectiveLineX0PolynomialToAway (k := k) (Polynomial.C a) =
      boundaryProjectiveLineX0ConstantsToAway (k := k) a := by
  simp [boundaryProjectiveLineX0PolynomialToAway]

@[simp] theorem boundaryProjectiveLineX0PolynomialToAway_X :
    boundaryProjectiveLineX0PolynomialToAway (k := k) Polynomial.X =
      boundaryProjectiveLineX0AffineCoordinate (k := k) := by
  simp [boundaryProjectiveLineX0PolynomialToAway]

theorem boundaryProjectiveLineX0AwayToPolynomial_affineCoordinate :
    boundaryProjectiveLineX0AwayToPolynomial (k := k)
      (boundaryProjectiveLineX0AffineCoordinate (k := k)) = Polynomial.X := by
  rw [boundaryProjectiveLineX0AwayToPolynomial, RingHom.comp_apply]
  change Localization.awayLift (boundaryProjectiveLineX0Dehom (k := k))
      (boundaryProjectiveLineCoordinate k 0) _
      (HomogeneousLocalization.val (boundaryProjectiveLineX0AffineCoordinate (k := k))) =
    Polynomial.X
  unfold boundaryProjectiveLineX0AffineCoordinate
  rw [HomogeneousLocalization.val_mk]
  simpa [boundaryProjectiveLineX0AffineCoordinate, boundaryProjectiveLineX0Dehom,
    boundaryProjectiveLineCoordinate] using
    (Localization.awayLift_mk
      (f := boundaryProjectiveLineX0Dehom (k := k))
      (r := boundaryProjectiveLineCoordinate k 0)
      (a := boundaryProjectiveLineCoordinate k 1)
      (v := (1 : Polynomial k))
      (hv := by
        rw [boundaryProjectiveLineX0Dehom_coordinate_zero (k := k)]
        simp)
      (j := 1))

theorem boundaryProjectiveLineX0AwayToPolynomial_constants (a : k) :
    boundaryProjectiveLineX0AwayToPolynomial (k := k)
      (boundaryProjectiveLineX0ConstantsToAway (k := k) a) = Polynomial.C a := by
  rw [boundaryProjectiveLineX0AwayToPolynomial, RingHom.comp_apply]
  change Localization.awayLift (boundaryProjectiveLineX0Dehom (k := k))
      (boundaryProjectiveLineCoordinate k 0) _
      (HomogeneousLocalization.val (boundaryProjectiveLineX0ConstantsToAway (k := k) a)) =
    Polynomial.C a
  unfold boundaryProjectiveLineX0ConstantsToAway
  simp [RingHom.comp_apply, HomogeneousLocalization.val_mk, boundaryProjectiveLineDegreeZeroRingHom]
  simpa [boundaryProjectiveLineX0Dehom, boundaryProjectiveLineDegreeZeroRingHom] using
    (Localization.awayLift_mk
      (f := boundaryProjectiveLineX0Dehom (k := k))
      (r := boundaryProjectiveLineCoordinate k 0)
      (a := MvPolynomial.C a)
      (v := (1 : Polynomial k))
      (hv := by
        rw [boundaryProjectiveLineX0Dehom_coordinate_zero (k := k)]
        simp)
      (j := 0))

@[simp] theorem boundaryProjectiveLineX0ConstantsToAway_val (a : k) :
    HomogeneousLocalization.val (boundaryProjectiveLineX0ConstantsToAway (k := k) a) =
      Localization.mk (MvPolynomial.C a) ⟨1, by refine ⟨0, ?_⟩; simp⟩ := by
  unfold boundaryProjectiveLineX0ConstantsToAway boundaryProjectiveLineDegreeZeroRingHom
  rfl

theorem boundaryProjectiveLineX0Polynomial_leftInverse :
    RingHom.comp
      (boundaryProjectiveLineX0AwayToPolynomial (k := k))
      (boundaryProjectiveLineX0PolynomialToAway (k := k)) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, boundaryProjectiveLineX0PolynomialToAway_C,
      boundaryProjectiveLineX0AwayToPolynomial_constants]
    rfl
  · rw [RingHom.comp_apply, boundaryProjectiveLineX0PolynomialToAway_X,
      boundaryProjectiveLineX0AwayToPolynomial_affineCoordinate]
    rfl

theorem boundaryProjectiveLineX0PolynomialToAway_leftInverse :
    Function.LeftInverse
      (boundaryProjectiveLineX0AwayToPolynomial (k := k))
      (boundaryProjectiveLineX0PolynomialToAway (k := k)) := by
  intro p
  exact DFunLike.congr_fun (boundaryProjectiveLineX0Polynomial_leftInverse (k := k)) p

theorem boundaryProjectiveLineX0AwayToPolynomial_surjective :
    Function.Surjective (boundaryProjectiveLineX0AwayToPolynomial (k := k)) :=
  (boundaryProjectiveLineX0PolynomialToAway_leftInverse (k := k)).surjective

theorem boundaryProjectiveLineX0PolynomialToAway_injective :
    Function.Injective (boundaryProjectiveLineX0PolynomialToAway (k := k)) :=
  (boundaryProjectiveLineX0PolynomialToAway_leftInverse (k := k)).injective

theorem boundaryProjectiveLineX0PolynomialToAway_dehom_monomial
    (d : Fin 2 →₀ ℕ) (a : k) :
    let n : ℕ := d 0 + d 1
    boundaryProjectiveLineX0PolynomialToAway (k := k)
        (boundaryProjectiveLineX0Dehom (k := k) (MvPolynomial.monomial d a)) =
      HomogeneousLocalization.mk
        {
          deg := n
          num := ⟨MvPolynomial.monomial d a, by
            have hdtotal : d.degree = d 0 + d 1 := by
              rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
              rw [Finsupp.sum_fintype]
              · rw [Fin.sum_univ_two]
                simp [Pi.one_apply]
              · intro i
                simp
            dsimp [n]
            exact
              (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 2) (R := k) (d 0 + d 1)
                (MvPolynomial.monomial d a)).2
                (MvPolynomial.isHomogeneous_monomial (σ := Fin 2) (R := k) a hdtotal)⟩
          den := ⟨boundaryProjectiveLineCoordinate k 0 ^ n, by
            dsimp [n]
            simpa [boundaryProjectiveLineCoordinate, nsmul_eq_mul] using
              (SetLike.pow_mem_graded (d 0 + d 1)
                (boundaryProjectiveLineCoordinate_mem_degree_one (k := k) 0))⟩
          den_mem := by
            show
              (boundaryProjectiveLineCoordinate k 0 ^ n : MvPolynomial (Fin 2) k) ∈
                Submonoid.powers (boundaryProjectiveLineCoordinate k 0)
            exact ⟨n, rfl⟩
        } := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, boundaryProjectiveLineX0Dehom_monomial,
    map_mul, map_pow, boundaryProjectiveLineX0PolynomialToAway_C,
    boundaryProjectiveLineX0PolynomialToAway_X, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_pow, boundaryProjectiveLineX0ConstantsToAway_val]
  let qOne : Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) :=
    ⟨1, ⟨0, by simp⟩⟩
  let q0 : Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) :=
    ⟨MvPolynomial.X 0, ⟨1, by simp⟩⟩
  let qTot : Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) :=
    ⟨MvPolynomial.X 0 ^ (d 0 + d 1), ⟨d 0 + d 1, rfl⟩⟩
  simp [boundaryProjectiveLineX0AffineCoordinate, HomogeneousLocalization.val_mk,
    boundaryProjectiveLineCoordinate, qOne, q0, qTot]
  change
    Localization.mk (MvPolynomial.C a) qOne *
        Localization.mk (MvPolynomial.X 1) q0 ^ d 1 =
      Localization.mk (MvPolynomial.monomial d a) qTot
  rw [Localization.mk_eq_mk'_apply (MvPolynomial.C a) qOne,
    Localization.mk_eq_mk'_apply (MvPolynomial.X 1) q0,
    Localization.mk_eq_mk'_apply (MvPolynomial.monomial d a) qTot]
  rw [← IsLocalization.mk'_pow
      (M := Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k))
      (S := Localization (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k))),
    ← IsLocalization.mk'_mul
      (M := Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k))
      (S := Localization (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)))]
  apply IsLocalization.mk'_eq_of_eq'
    (M := Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k))
    (S := Localization (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 2) k)))
  simp [qOne, q0, qTot, Submonoid.coe_one, Submonoid.coe_mul,
    MvPolynomial.monomial_eq, boundaryProjectiveLineCoordinate, Fin.prod_univ_two,
    pow_add, mul_assoc, mul_left_comm, mul_comm]

theorem boundaryProjectiveLineX0PolynomialToAway_dehom_of_mem_degree
    {φ : MvPolynomial (Fin 2) k} {n : ℕ}
    (hφ : φ ∈ boundaryProjectiveLineGrading k n) :
    boundaryProjectiveLineX0PolynomialToAway (k := k)
        (boundaryProjectiveLineX0Dehom (k := k) φ) =
      HomogeneousLocalization.mk
        {
          deg := n
          num := ⟨φ, hφ⟩
          den := ⟨boundaryProjectiveLineCoordinate k 0 ^ n, by
            simpa [boundaryProjectiveLineCoordinate, nsmul_eq_mul] using
              (SetLike.pow_mem_graded n
                (boundaryProjectiveLineCoordinate_mem_degree_one (k := k) 0))⟩
          den_mem := by
            show
              (boundaryProjectiveLineCoordinate k 0 ^ n : MvPolynomial (Fin 2) k) ∈
                Submonoid.powers (boundaryProjectiveLineCoordinate k 0)
            exact ⟨n, rfl⟩
        } := by
  have hhom : φ.IsHomogeneous n := hφ
  apply HomogeneousLocalization.val_injective
  let qn : Submonoid.powers (boundaryProjectiveLineCoordinate k 0) :=
    ⟨boundaryProjectiveLineCoordinate k 0 ^ n, ⟨n, rfl⟩⟩
  change
    HomogeneousLocalization.val ((boundaryProjectiveLineX0PolynomialToAway (k := k))
      ((boundaryProjectiveLineX0Dehom (k := k)) φ)) =
      Localization.mk φ qn
  have hsumφ :
      (boundaryProjectiveLineX0PolynomialToAway (k := k))
          ((boundaryProjectiveLineX0Dehom (k := k)) φ) =
        ∑ d in φ.support,
          (boundaryProjectiveLineX0PolynomialToAway (k := k))
            ((boundaryProjectiveLineX0Dehom (k := k))
              (MvPolynomial.monomial d (MvPolynomial.coeff d φ))) := by
    calc
      (boundaryProjectiveLineX0PolynomialToAway (k := k))
          ((boundaryProjectiveLineX0Dehom (k := k)) φ)
        = (boundaryProjectiveLineX0PolynomialToAway (k := k))
            ((boundaryProjectiveLineX0Dehom (k := k))
              (∑ d in φ.support, MvPolynomial.monomial d (MvPolynomial.coeff d φ))) :=
            congrArg
              (fun p =>
                (boundaryProjectiveLineX0PolynomialToAway (k := k))
                  ((boundaryProjectiveLineX0Dehom (k := k)) p))
              φ.as_sum
      _ = (boundaryProjectiveLineX0PolynomialToAway (k := k))
            (∑ d in φ.support,
              (boundaryProjectiveLineX0Dehom (k := k))
                (MvPolynomial.monomial d (MvPolynomial.coeff d φ))) := by
            rw [map_sum]
      _ = ∑ d in φ.support,
            (boundaryProjectiveLineX0PolynomialToAway (k := k))
              ((boundaryProjectiveLineX0Dehom (k := k))
                (MvPolynomial.monomial d (MvPolynomial.coeff d φ))) := by
            rw [map_sum]
  calc
    HomogeneousLocalization.val ((boundaryProjectiveLineX0PolynomialToAway (k := k))
        ((boundaryProjectiveLineX0Dehom (k := k)) φ))
      = HomogeneousLocalization.val
          (∑ d in φ.support,
            (boundaryProjectiveLineX0PolynomialToAway (k := k))
              ((boundaryProjectiveLineX0Dehom (k := k))
                (MvPolynomial.monomial d (MvPolynomial.coeff d φ)))) :=
          congrArg HomogeneousLocalization.val hsumφ
    _ = ∑ d in φ.support,
        HomogeneousLocalization.val
          ((boundaryProjectiveLineX0PolynomialToAway (k := k))
            ((boundaryProjectiveLineX0Dehom (k := k))
              (MvPolynomial.monomial d (MvPolynomial.coeff d φ)))) := by
          exact map_sum
            (boundaryProjectiveLineHomogeneousLocalizationValAddMonoidHom (k := k) 0)
            (fun d =>
              (boundaryProjectiveLineX0PolynomialToAway (k := k))
                ((boundaryProjectiveLineX0Dehom (k := k))
                  (MvPolynomial.monomial d (MvPolynomial.coeff d φ))))
            φ.support
    _ = ∑ d in φ.support,
          Localization.mk (MvPolynomial.monomial d (MvPolynomial.coeff d φ))
            qn := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hdweight :
            Finsupp.weight (fun _ : Fin 2 => (1 : ℕ)) d = n :=
          hhom (d := d) (MvPolynomial.mem_support_iff.mp hd)
        have hddeg : d.degree = n := by
          simpa [Finsupp.degree_eq_weight_one] using hdweight
        have hdtotal : d.degree = d 0 + d 1 := by
          rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
          rw [Finsupp.sum_fintype]
          · rw [Fin.sum_univ_two]
            simp [Pi.one_apply]
          · intro i
            simp
        have hs : d 0 + d 1 = n := hdtotal.symm.trans hddeg
        have hterm := congrArg HomogeneousLocalization.val
          (boundaryProjectiveLineX0PolynomialToAway_dehom_monomial (k := k) d
            (MvPolynomial.coeff d φ))
        dsimp only at hterm
        simpa [boundaryProjectiveLineCoordinate, hs] using hterm
      _ = Localization.mk (∑ d in φ.support, MvPolynomial.monomial d (MvPolynomial.coeff d φ))
          qn := by
        symm
        exact Localization.mk_sum _ _ _
      _ = Localization.mk φ qn := by
        exact congrArg (fun p => Localization.mk p qn) φ.as_sum.symm

theorem boundaryProjectiveLineX0PolynomialToAway_surjective :
    Function.Surjective (boundaryProjectiveLineX0PolynomialToAway (k := k)) := by
  intro z
  obtain ⟨⟨n, ⟨φ, hφ⟩, ⟨b, hbdeg⟩, hbmem⟩, rfl⟩ :=
    HomogeneousLocalization.mk_surjective
      (𝒜 := boundaryProjectiveLineGrading k)
      (x := Submonoid.powers (boundaryProjectiveLineCoordinate k 0)) z
  rcases hbmem with ⟨m, hmemb⟩
  have hmdeg :
      (boundaryProjectiveLineCoordinate k 0 ^ m : MvPolynomial (Fin 2) k) ∈
        boundaryProjectiveLineGrading k n := by
    simpa [hmemb] using hbdeg
  have hpowdeg :
      (boundaryProjectiveLineCoordinate k 0 ^ m : MvPolynomial (Fin 2) k) ∈
        boundaryProjectiveLineGrading k m := by
    simpa [boundaryProjectiveLineCoordinate, nsmul_eq_mul] using
      (SetLike.pow_mem_graded m (boundaryProjectiveLineCoordinate_mem_degree_one (k := k) 0))
  have hcoord_ne : (boundaryProjectiveLineCoordinate k 0 : MvPolynomial (Fin 2) k) ≠ 0 := by
    simpa [boundaryProjectiveLineCoordinate] using
      (MvPolynomial.X_ne_zero (n := (0 : Fin 2)) :
        (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ≠ 0)
  have hm : m = n :=
    DirectSum.degree_eq_of_mem_mem (boundaryProjectiveLineGrading k) hpowdeg hmdeg
      (pow_ne_zero m hcoord_ne)
  refine ⟨boundaryProjectiveLineX0Dehom (k := k) φ, ?_⟩
  have hb' : b = boundaryProjectiveLineCoordinate k 0 ^ n := by
    calc
      b = boundaryProjectiveLineCoordinate k 0 ^ m := hmemb.symm
      _ = boundaryProjectiveLineCoordinate k 0 ^ n := by simpa [hm]
  subst b
  simpa using boundaryProjectiveLineX0PolynomialToAway_dehom_of_mem_degree (k := k) hφ

/-- Dehomogenization on the `x₁` chart sends `x₀ ↦ s` and `x₁ ↦ 1`. -/
abbrev boundaryProjectiveLineX1Dehom : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom (Polynomial.C : k →+* Polynomial k)
    (fun i : Fin 2 => Fin.cases Polynomial.X (fun _ => 1) i)

theorem boundaryProjectiveLineX1Dehom_coordinate_one :
    boundaryProjectiveLineX1Dehom (k := k) (boundaryProjectiveLineCoordinate k 1) = 1 := by
  simp only [boundaryProjectiveLineX1Dehom, boundaryProjectiveLineCoordinate,
    MvPolynomial.eval₂Hom_X']
  rw [show (1 : Fin 2) = Fin.succ 0 by rfl]
  rfl

theorem boundaryProjectiveLineX1Dehom_monomial
    (d : Fin 2 →₀ ℕ) (a : k) :
    boundaryProjectiveLineX1Dehom (k := k) (MvPolynomial.monomial d a) =
      Polynomial.C a * Polynomial.X ^ d 0 := by
  rw [boundaryProjectiveLineX1Dehom, MvPolynomial.eval₂Hom_monomial]
  simpa [Fin.prod_univ_succ, mul_assoc, mul_left_comm, mul_comm]

/-- The forward chart map on `Away x₁`, viewed through the underlying localization. -/
abbrev boundaryProjectiveLineX1AwayToPolynomial :
    boundaryProjectiveLineCoordinateAwayRing (k := k) 1 →+* Polynomial k := by
  let liftMap : Localization.Away (boundaryProjectiveLineCoordinate k 1) →+* Polynomial k :=
    Localization.awayLift (boundaryProjectiveLineX1Dehom (k := k))
      (boundaryProjectiveLineCoordinate k 1)
      (by
        rw [boundaryProjectiveLineX1Dehom_coordinate_one (k := k)]
        exact isUnit_one)
  let valMap : HomogeneousLocalization.Away (boundaryProjectiveLineGrading k)
      (boundaryProjectiveLineCoordinate k 1) →+*
        Localization.Away (boundaryProjectiveLineCoordinate k 1) :=
    algebraMap _ _
  exact RingHom.comp liftMap
    valMap

/-- Constants in `k` give degree-zero classes on the `x₁` chart. -/
abbrev boundaryProjectiveLineX1ConstantsToAway :
    k →+* boundaryProjectiveLineCoordinateAwayRing (k := k) 1 :=
  (HomogeneousLocalization.fromZeroRingHom
      (boundaryProjectiveLineGrading k)
      (Submonoid.powers (boundaryProjectiveLineCoordinate k 1))).comp
    (boundaryProjectiveLineDegreeZeroRingHom k)

/-- The affine coordinate `s = x₀ / x₁` on the `x₁` chart. -/
def boundaryProjectiveLineX1AffineCoordinate :
    boundaryProjectiveLineCoordinateAwayRing (k := k) 1 :=
  HomogeneousLocalization.mk
    ⟨1,
      ⟨boundaryProjectiveLineCoordinate k 0,
        boundaryProjectiveLineCoordinate_mem_degree_one k 0⟩,
      ⟨boundaryProjectiveLineCoordinate k 1,
        boundaryProjectiveLineCoordinate_mem_degree_one k 1⟩,
      by
        refine ⟨1, ?_⟩
        simp [boundaryProjectiveLineCoordinate]⟩

/-- The inverse-direction ring map for the `x₁` chart, sending `s` to `x₀ / x₁`. -/
abbrev boundaryProjectiveLineX1PolynomialToAway :
    Polynomial k →+* boundaryProjectiveLineCoordinateAwayRing (k := k) 1 :=
  Polynomial.eval₂RingHom
    (boundaryProjectiveLineX1ConstantsToAway (k := k))
    (boundaryProjectiveLineX1AffineCoordinate (k := k))

@[simp] theorem boundaryProjectiveLineX1PolynomialToAway_C (a : k) :
    boundaryProjectiveLineX1PolynomialToAway (k := k) (Polynomial.C a) =
      boundaryProjectiveLineX1ConstantsToAway (k := k) a := by
  simp [boundaryProjectiveLineX1PolynomialToAway]

@[simp] theorem boundaryProjectiveLineX1PolynomialToAway_X :
    boundaryProjectiveLineX1PolynomialToAway (k := k) Polynomial.X =
      boundaryProjectiveLineX1AffineCoordinate (k := k) := by
  simp [boundaryProjectiveLineX1PolynomialToAway]

theorem boundaryProjectiveLineX1AwayToPolynomial_affineCoordinate :
  boundaryProjectiveLineX1AwayToPolynomial (k := k)
    (boundaryProjectiveLineX1AffineCoordinate (k := k)) = Polynomial.X := by
  rw [boundaryProjectiveLineX1AwayToPolynomial, RingHom.comp_apply]
  change Localization.awayLift (boundaryProjectiveLineX1Dehom (k := k))
      (boundaryProjectiveLineCoordinate k 1) _
      (HomogeneousLocalization.val (boundaryProjectiveLineX1AffineCoordinate (k := k))) =
    Polynomial.X
  unfold boundaryProjectiveLineX1AffineCoordinate
  rw [HomogeneousLocalization.val_mk]
  simpa [boundaryProjectiveLineX1AffineCoordinate, boundaryProjectiveLineX1Dehom,
    boundaryProjectiveLineCoordinate] using
    (Localization.awayLift_mk
      (f := boundaryProjectiveLineX1Dehom (k := k))
      (r := boundaryProjectiveLineCoordinate k 1)
      (a := boundaryProjectiveLineCoordinate k 0)
      (v := (1 : Polynomial k))
      (hv := by
        rw [boundaryProjectiveLineX1Dehom_coordinate_one (k := k)]
        simp)
      (j := 1))

theorem boundaryProjectiveLineX1AwayToPolynomial_constants (a : k) :
  boundaryProjectiveLineX1AwayToPolynomial (k := k)
    (boundaryProjectiveLineX1ConstantsToAway (k := k) a) = Polynomial.C a := by
  rw [boundaryProjectiveLineX1AwayToPolynomial, RingHom.comp_apply]
  change Localization.awayLift (boundaryProjectiveLineX1Dehom (k := k))
      (boundaryProjectiveLineCoordinate k 1) _
      (HomogeneousLocalization.val (boundaryProjectiveLineX1ConstantsToAway (k := k) a)) =
    Polynomial.C a
  unfold boundaryProjectiveLineX1ConstantsToAway
  simp [RingHom.comp_apply, HomogeneousLocalization.val_mk, boundaryProjectiveLineDegreeZeroRingHom]
  simpa [boundaryProjectiveLineX1Dehom, boundaryProjectiveLineDegreeZeroRingHom] using
    (Localization.awayLift_mk
      (f := boundaryProjectiveLineX1Dehom (k := k))
      (r := boundaryProjectiveLineCoordinate k 1)
      (a := MvPolynomial.C a)
      (v := (1 : Polynomial k))
      (hv := by
        rw [boundaryProjectiveLineX1Dehom_coordinate_one (k := k)]
        simp)
      (j := 0))

@[simp] theorem boundaryProjectiveLineX1ConstantsToAway_val (a : k) :
    HomogeneousLocalization.val (boundaryProjectiveLineX1ConstantsToAway (k := k) a) =
      Localization.mk (MvPolynomial.C a) ⟨1, by refine ⟨0, ?_⟩; simp⟩ := by
  unfold boundaryProjectiveLineX1ConstantsToAway boundaryProjectiveLineDegreeZeroRingHom
  rfl

theorem boundaryProjectiveLineX1Polynomial_leftInverse :
    RingHom.comp
      (boundaryProjectiveLineX1AwayToPolynomial (k := k))
      (boundaryProjectiveLineX1PolynomialToAway (k := k)) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [RingHom.comp_apply, boundaryProjectiveLineX1PolynomialToAway_C,
      boundaryProjectiveLineX1AwayToPolynomial_constants]
    rfl
  · rw [RingHom.comp_apply, boundaryProjectiveLineX1PolynomialToAway_X,
      boundaryProjectiveLineX1AwayToPolynomial_affineCoordinate]
    rfl

theorem boundaryProjectiveLineX1PolynomialToAway_leftInverse :
    Function.LeftInverse
      (boundaryProjectiveLineX1AwayToPolynomial (k := k))
      (boundaryProjectiveLineX1PolynomialToAway (k := k)) := by
  intro p
  exact DFunLike.congr_fun (boundaryProjectiveLineX1Polynomial_leftInverse (k := k)) p

theorem boundaryProjectiveLineX1AwayToPolynomial_surjective :
    Function.Surjective (boundaryProjectiveLineX1AwayToPolynomial (k := k)) :=
  (boundaryProjectiveLineX1PolynomialToAway_leftInverse (k := k)).surjective

theorem boundaryProjectiveLineX1PolynomialToAway_injective :
    Function.Injective (boundaryProjectiveLineX1PolynomialToAway (k := k)) :=
  (boundaryProjectiveLineX1PolynomialToAway_leftInverse (k := k)).injective

theorem boundaryProjectiveLineX1PolynomialToAway_dehom_monomial
    (d : Fin 2 →₀ ℕ) (a : k) :
    let n : ℕ := d 0 + d 1
    boundaryProjectiveLineX1PolynomialToAway (k := k)
        (boundaryProjectiveLineX1Dehom (k := k) (MvPolynomial.monomial d a)) =
      HomogeneousLocalization.mk
        {
          deg := n
          num := ⟨MvPolynomial.monomial d a, by
            have hdtotal : d.degree = d 0 + d 1 := by
              rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
              rw [Finsupp.sum_fintype]
              · rw [Fin.sum_univ_two]
                simp [Pi.one_apply]
              · intro i
                simp
            dsimp [n]
            exact
              (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 2) (R := k) (d 0 + d 1)
                (MvPolynomial.monomial d a)).2
                (MvPolynomial.isHomogeneous_monomial (σ := Fin 2) (R := k) a hdtotal)⟩
          den := ⟨boundaryProjectiveLineCoordinate k 1 ^ n, by
            dsimp [n]
            simpa [boundaryProjectiveLineCoordinate, nsmul_eq_mul] using
              (SetLike.pow_mem_graded (d 0 + d 1)
                (boundaryProjectiveLineCoordinate_mem_degree_one (k := k) 1))⟩
          den_mem := by
            show
              (boundaryProjectiveLineCoordinate k 1 ^ n : MvPolynomial (Fin 2) k) ∈
                Submonoid.powers (boundaryProjectiveLineCoordinate k 1)
            exact ⟨n, rfl⟩
        } := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mk, boundaryProjectiveLineX1Dehom_monomial,
    map_mul, map_pow, boundaryProjectiveLineX1PolynomialToAway_C,
    boundaryProjectiveLineX1PolynomialToAway_X, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_pow, boundaryProjectiveLineX1ConstantsToAway_val]
  let qOne : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) :=
    ⟨1, ⟨0, by simp⟩⟩
  let q1 : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) :=
    ⟨MvPolynomial.X 1, ⟨1, by simp⟩⟩
  let qTot : Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) :=
    ⟨MvPolynomial.X 1 ^ (d 0 + d 1), ⟨d 0 + d 1, rfl⟩⟩
  simp [boundaryProjectiveLineX1AffineCoordinate, HomogeneousLocalization.val_mk,
    boundaryProjectiveLineCoordinate, qOne, q1, qTot]
  change
    Localization.mk (MvPolynomial.C a) qOne *
        Localization.mk (MvPolynomial.X 0) q1 ^ d 0 =
      Localization.mk (MvPolynomial.monomial d a) qTot
  rw [Localization.mk_eq_mk'_apply (MvPolynomial.C a) qOne,
    Localization.mk_eq_mk'_apply (MvPolynomial.X 0) q1,
    Localization.mk_eq_mk'_apply (MvPolynomial.monomial d a) qTot]
  rw [← IsLocalization.mk'_pow
      (M := Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k))
      (S := Localization (Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k))),
    ← IsLocalization.mk'_mul
      (M := Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k))
      (S := Localization (Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)))]
  apply IsLocalization.mk'_eq_of_eq'
    (M := Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k))
    (S := Localization (Submonoid.powers (MvPolynomial.X 1 : MvPolynomial (Fin 2) k)))
  simp [qOne, q1, qTot, Submonoid.coe_one, Submonoid.coe_mul,
    MvPolynomial.monomial_eq, boundaryProjectiveLineCoordinate, Fin.prod_univ_two,
    pow_add, mul_assoc, mul_left_comm, mul_comm]

theorem boundaryProjectiveLineX1PolynomialToAway_dehom_of_mem_degree
    {φ : MvPolynomial (Fin 2) k} {n : ℕ}
    (hφ : φ ∈ boundaryProjectiveLineGrading k n) :
    boundaryProjectiveLineX1PolynomialToAway (k := k)
        (boundaryProjectiveLineX1Dehom (k := k) φ) =
      HomogeneousLocalization.mk
        {
          deg := n
          num := ⟨φ, hφ⟩
          den := ⟨boundaryProjectiveLineCoordinate k 1 ^ n, by
            simpa [boundaryProjectiveLineCoordinate, nsmul_eq_mul] using
              (SetLike.pow_mem_graded n
                (boundaryProjectiveLineCoordinate_mem_degree_one (k := k) 1))⟩
          den_mem := by
            show
              (boundaryProjectiveLineCoordinate k 1 ^ n : MvPolynomial (Fin 2) k) ∈
                Submonoid.powers (boundaryProjectiveLineCoordinate k 1)
            exact ⟨n, rfl⟩
        } := by
  have hhom : φ.IsHomogeneous n := hφ
  apply HomogeneousLocalization.val_injective
  let qn : Submonoid.powers (boundaryProjectiveLineCoordinate k 1) :=
    ⟨boundaryProjectiveLineCoordinate k 1 ^ n, ⟨n, rfl⟩⟩
  change
    HomogeneousLocalization.val ((boundaryProjectiveLineX1PolynomialToAway (k := k))
      ((boundaryProjectiveLineX1Dehom (k := k)) φ)) =
      Localization.mk φ qn
  have hsumφ :
      (boundaryProjectiveLineX1PolynomialToAway (k := k))
          ((boundaryProjectiveLineX1Dehom (k := k)) φ) =
        ∑ d in φ.support,
          (boundaryProjectiveLineX1PolynomialToAway (k := k))
            ((boundaryProjectiveLineX1Dehom (k := k))
              (MvPolynomial.monomial d (MvPolynomial.coeff d φ))) := by
    calc
      (boundaryProjectiveLineX1PolynomialToAway (k := k))
          ((boundaryProjectiveLineX1Dehom (k := k)) φ)
        = (boundaryProjectiveLineX1PolynomialToAway (k := k))
            ((boundaryProjectiveLineX1Dehom (k := k))
              (∑ d in φ.support, MvPolynomial.monomial d (MvPolynomial.coeff d φ))) :=
            congrArg
              (fun p =>
                (boundaryProjectiveLineX1PolynomialToAway (k := k))
                  ((boundaryProjectiveLineX1Dehom (k := k)) p))
              φ.as_sum
      _ = (boundaryProjectiveLineX1PolynomialToAway (k := k))
            (∑ d in φ.support,
              (boundaryProjectiveLineX1Dehom (k := k))
                (MvPolynomial.monomial d (MvPolynomial.coeff d φ))) := by
            rw [map_sum]
      _ = ∑ d in φ.support,
            (boundaryProjectiveLineX1PolynomialToAway (k := k))
              ((boundaryProjectiveLineX1Dehom (k := k))
                (MvPolynomial.monomial d (MvPolynomial.coeff d φ))) := by
            rw [map_sum]
  calc
    HomogeneousLocalization.val ((boundaryProjectiveLineX1PolynomialToAway (k := k))
        ((boundaryProjectiveLineX1Dehom (k := k)) φ))
      = HomogeneousLocalization.val
          (∑ d in φ.support,
            (boundaryProjectiveLineX1PolynomialToAway (k := k))
              ((boundaryProjectiveLineX1Dehom (k := k))
                (MvPolynomial.monomial d (MvPolynomial.coeff d φ)))) :=
          congrArg HomogeneousLocalization.val hsumφ
    _ = ∑ d in φ.support,
        HomogeneousLocalization.val
          ((boundaryProjectiveLineX1PolynomialToAway (k := k))
            ((boundaryProjectiveLineX1Dehom (k := k))
              (MvPolynomial.monomial d (MvPolynomial.coeff d φ)))) := by
          exact map_sum
            (boundaryProjectiveLineHomogeneousLocalizationValAddMonoidHom (k := k) 1)
            (fun d =>
              (boundaryProjectiveLineX1PolynomialToAway (k := k))
                ((boundaryProjectiveLineX1Dehom (k := k))
                  (MvPolynomial.monomial d (MvPolynomial.coeff d φ))))
            φ.support
    _ = ∑ d in φ.support,
          Localization.mk (MvPolynomial.monomial d (MvPolynomial.coeff d φ))
            qn := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hdweight :
            Finsupp.weight (fun _ : Fin 2 => (1 : ℕ)) d = n :=
          hhom (d := d) (MvPolynomial.mem_support_iff.mp hd)
        have hddeg : d.degree = n := by
          simpa [Finsupp.degree_eq_weight_one] using hdweight
        have hdtotal : d.degree = d 0 + d 1 := by
          rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply]
          rw [Finsupp.sum_fintype]
          · rw [Fin.sum_univ_two]
            simp [Pi.one_apply]
          · intro i
            simp
        have hs : d 0 + d 1 = n := hdtotal.symm.trans hddeg
        have hterm := congrArg HomogeneousLocalization.val
          (boundaryProjectiveLineX1PolynomialToAway_dehom_monomial (k := k) d
            (MvPolynomial.coeff d φ))
        dsimp only at hterm
        simpa [boundaryProjectiveLineCoordinate, hs] using hterm
      _ = Localization.mk (∑ d in φ.support, MvPolynomial.monomial d (MvPolynomial.coeff d φ))
          qn := by
        symm
        exact Localization.mk_sum _ _ _
      _ = Localization.mk φ qn := by
        exact congrArg (fun p => Localization.mk p qn) φ.as_sum.symm

theorem boundaryProjectiveLine_coeff_zero_eq_zero_of_projZeroRingHom_eq_zero
    {φ : MvPolynomial (Fin 2) k}
    (h :
      GradedRing.projZeroRingHom (boundaryProjectiveLineGrading k) φ = 0) :
    MvPolynomial.coeff (0 : Fin 2 →₀ ℕ) φ = 0 := by
  have hcomp :
      MvPolynomial.homogeneousComponent 0 φ = 0 := by
    have hdecomp :
        (DirectSum.decompose (boundaryProjectiveLineGrading k) φ 0 :
          MvPolynomial (Fin 2) k) = 0 := by
      simpa [GradedRing.projZeroRingHom] using h
    have hdecomp' :
        (MvPolynomial.decomposition.decompose' φ 0 :
          MvPolynomial (Fin 2) k) = 0 := by
      simpa [boundaryProjectiveLineGrading, DirectSum.Decomposition.decompose'_eq] using hdecomp
    rw [MvPolynomial.decomposition.decompose'_apply] at hdecomp'
    exact hdecomp'
  have hcoeff :=
    congrArg (MvPolynomial.coeff (0 : Fin 2 →₀ ℕ)) hcomp
  simpa [MvPolynomial.homogeneousComponent_zero, MvPolynomial.coeff_C] using hcoeff

theorem boundaryProjectiveLineX1PolynomialToAway_surjective :
    Function.Surjective (boundaryProjectiveLineX1PolynomialToAway (k := k)) := by
  intro z
  obtain ⟨⟨n, ⟨φ, hφ⟩, ⟨b, hbdeg⟩, hbmem⟩, rfl⟩ :=
    HomogeneousLocalization.mk_surjective
      (𝒜 := boundaryProjectiveLineGrading k)
      (x := Submonoid.powers (boundaryProjectiveLineCoordinate k 1)) z
  rcases hbmem with ⟨m, hmemb⟩
  have hmdeg :
      (boundaryProjectiveLineCoordinate k 1 ^ m : MvPolynomial (Fin 2) k) ∈
        boundaryProjectiveLineGrading k n := by
    simpa [hmemb] using hbdeg
  have hpowdeg :
      (boundaryProjectiveLineCoordinate k 1 ^ m : MvPolynomial (Fin 2) k) ∈
        boundaryProjectiveLineGrading k m := by
    simpa [boundaryProjectiveLineCoordinate, nsmul_eq_mul] using
      (SetLike.pow_mem_graded m (boundaryProjectiveLineCoordinate_mem_degree_one (k := k) 1))
  have hcoord_ne : (boundaryProjectiveLineCoordinate k 1 : MvPolynomial (Fin 2) k) ≠ 0 := by
    simpa [boundaryProjectiveLineCoordinate] using
      (MvPolynomial.X_ne_zero (n := (1 : Fin 2)) :
        (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ≠ 0)
  have hm : m = n :=
    DirectSum.degree_eq_of_mem_mem (boundaryProjectiveLineGrading k) hpowdeg hmdeg
      (pow_ne_zero m hcoord_ne)
  refine ⟨boundaryProjectiveLineX1Dehom (k := k) φ, ?_⟩
  have hb' : b = boundaryProjectiveLineCoordinate k 1 ^ n := by
    calc
      b = boundaryProjectiveLineCoordinate k 1 ^ m := hmemb.symm
      _ = boundaryProjectiveLineCoordinate k 1 ^ n := by simpa [hm]
  subst b
  simpa using boundaryProjectiveLineX1PolynomialToAway_dehom_of_mem_degree (k := k) hφ

theorem boundaryProjectiveLine_iSup_coordinate_basicOpen_eq_top :
    (⨆ i : Fin 2,
      AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
        (boundaryProjectiveLineCoordinate k i)) = ⊤ := by
  refine AlgebraicGeometry.Proj.iSup_basicOpen_eq_top
      (𝒜 := boundaryProjectiveLineGrading k)
      (f := boundaryProjectiveLineCoordinate k) ?_
  intro φ hφ
  simpa [boundaryProjectiveLineCoordinate] using
    (show φ ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin 2))) from by
      rw [MvPolynomial.mem_ideal_span_X_image]
      intro m hm
      have hcoeff0 : MvPolynomial.coeff 0 φ = 0 := by
        have hirr :
            GradedRing.projZeroRingHom (boundaryProjectiveLineGrading k) φ = 0 := by
          simpa [HomogeneousIdeal.mem_irrelevant_iff] using hφ
        exact boundaryProjectiveLine_coeff_zero_eq_zero_of_projZeroRingHom_eq_zero
          (k := k) hirr
      have hmne : m ≠ 0 := by
        intro hm0
        exact (MvPolynomial.mem_support_iff.mp (hm0 ▸ hm)) hcoeff0
      by_cases h0 : m 0 = 0
      · refine ⟨1, by simp, ?_⟩
        intro h1
        apply hmne
        ext i
        fin_cases i
        · exact h0
        · exact h1
      · exact ⟨0, by simp, h0⟩)

/-- The `i`-th standard basic open is affine, with the usual `Away` chart. -/
abbrev boundaryProjectiveLineCoordinateBasicOpenIsoSpec (i : Fin 2) :
    (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
      (boundaryProjectiveLineCoordinate k i)).toScheme ≅
      Spec (CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) i)) :=
  AlgebraicGeometry.Proj.basicOpenIsoSpec
    (boundaryProjectiveLineGrading k)
    (boundaryProjectiveLineCoordinate k i)
    (boundaryProjectiveLineCoordinate_mem_degree_one k i)
    (by simp)

/-- The affine chart immersion for the `i`-th standard coordinate basic open. -/
abbrev boundaryProjectiveLineCoordinateAwayι (i : Fin 2) :
    Spec (CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) i)) ⟶
      boundaryProjectiveLineScheme k :=
  AlgebraicGeometry.Proj.awayι
    (boundaryProjectiveLineGrading k)
    (boundaryProjectiveLineCoordinate k i)
    (boundaryProjectiveLineCoordinate_mem_degree_one k i)
    (by simp)

/-- The canonical structural morphism from `Proj(k[x₀, x₁])` to the spectrum of
its degree-zero ring. -/
abbrev boundaryProjectiveLineStructMapToDegreeZero :
  boundaryProjectiveLineScheme k ⟶ Spec (CommRingCat.of (boundaryProjectiveLineDegreeZeroRing k)) :=
  AlgebraicGeometry.Proj.toSpecZero (boundaryProjectiveLineGrading k)

/-- The canonical morphism from the degree-zero affine base of `Proj(k[x₀,x₁])`
to `Spec k`, induced by constant polynomials. -/
abbrev boundaryProjectiveLineDegreeZeroToBase :
  Spec (CommRingCat.of (boundaryProjectiveLineDegreeZeroRing k)) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (boundaryProjectiveLineDegreeZeroRingHom k))

/-- The raw projective-line structural morphism to the actual base `Spec k`. -/
abbrev boundaryProjectiveLineOverSpec :
    boundaryProjectiveLineScheme k ⟶ Spec (CommRingCat.of k) :=
  boundaryProjectiveLineStructMapToDegreeZero k ≫ boundaryProjectiveLineDegreeZeroToBase k

/-- The `x₁`-chart structural morphism to the base is the constant-class map
from `k` into the chart ring. -/
theorem boundaryProjectiveLineX0ChartToBase :
    boundaryProjectiveLineCoordinateAwayι (k := k) 0 ≫ boundaryProjectiveLineOverSpec k =
      Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k))) := by
  rw [boundaryProjectiveLineOverSpec, ← Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  change Spec.map
      (CommRingCat.ofHom (boundaryProjectiveLineDegreeZeroRingHom k) ≫
        CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom (boundaryProjectiveLineGrading k)
            (Submonoid.powers (boundaryProjectiveLineCoordinate k 0)))) =
    Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k)))
  rfl

/-- The `x₁`-chart structural morphism to the base is the constant-class map
from `k` into the chart ring. -/
theorem boundaryProjectiveLineX1ChartToBase :
    boundaryProjectiveLineCoordinateAwayι (k := k) 1 ≫ boundaryProjectiveLineOverSpec k =
      Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k))) := by
  rw [boundaryProjectiveLineOverSpec, ← Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero]
  rw [← Spec.map_comp]
  change Spec.map
      (CommRingCat.ofHom (boundaryProjectiveLineDegreeZeroRingHom k) ≫
        CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom (boundaryProjectiveLineGrading k)
            (Submonoid.powers (boundaryProjectiveLineCoordinate k 1)))) =
    Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k)))
  rfl

/-- Constructive witness data for the `x₀`-chart: an explicit ring equivalence
with `k[t]` that matches the structural map to `Spec k`. -/
structure BoundaryProjectiveLineX0ChartConstructionData where
  ringEquiv : boundaryProjectiveLineCoordinateAwayRing (k := k) 0 ≃+* Polynomial k
  commutes :
    ringEquiv.toRingHom.comp (boundaryProjectiveLineX0ConstantsToAway (k := k)) = Polynomial.C

/-- Constructive witness data for the `x₁`-chart: an explicit ring equivalence
with `k[t]` that matches the structural map to `Spec k`. -/
structure BoundaryProjectiveLineX1ChartConstructionData where
  ringEquiv : boundaryProjectiveLineCoordinateAwayRing (k := k) 1 ≃+* Polynomial k
  commutes :
    ringEquiv.toRingHom.comp (boundaryProjectiveLineX1ConstantsToAway (k := k)) = Polynomial.C

/-- Combined constructive witness data for the two standard affine charts of
the concrete Boundary-side projective line. -/
structure BoundaryProjectiveLineConstructionData where
  x0Chart : BoundaryProjectiveLineX0ChartConstructionData (k := k)
  x1Chart : BoundaryProjectiveLineX1ChartConstructionData (k := k)

noncomputable def boundaryProjectiveLineX0ChartConstructionData :
    BoundaryProjectiveLineX0ChartConstructionData (k := k) where
  ringEquiv :=
    (RingEquiv.ofBijective (boundaryProjectiveLineX0PolynomialToAway (k := k))
      ⟨boundaryProjectiveLineX0PolynomialToAway_injective (k := k),
        boundaryProjectiveLineX0PolynomialToAway_surjective (k := k)⟩).symm
  commutes := by
    apply DFunLike.ext
    intro a
    change
      (RingEquiv.ofBijective (boundaryProjectiveLineX0PolynomialToAway (k := k))
        ⟨boundaryProjectiveLineX0PolynomialToAway_injective (k := k),
          boundaryProjectiveLineX0PolynomialToAway_surjective (k := k)⟩).symm
          (boundaryProjectiveLineX0ConstantsToAway (k := k) a) = Polynomial.C a
    rw [← boundaryProjectiveLineX0PolynomialToAway_C (k := k) a]
    exact
      (RingEquiv.ofBijective (boundaryProjectiveLineX0PolynomialToAway (k := k))
        ⟨boundaryProjectiveLineX0PolynomialToAway_injective (k := k),
          boundaryProjectiveLineX0PolynomialToAway_surjective (k := k)⟩).symm_apply_apply
        (Polynomial.C a)

noncomputable def boundaryProjectiveLineX1ChartConstructionData :
    BoundaryProjectiveLineX1ChartConstructionData (k := k) where
  ringEquiv :=
    (RingEquiv.ofBijective (boundaryProjectiveLineX1PolynomialToAway (k := k))
      ⟨boundaryProjectiveLineX1PolynomialToAway_injective (k := k),
        boundaryProjectiveLineX1PolynomialToAway_surjective (k := k)⟩).symm
  commutes := by
    apply DFunLike.ext
    intro a
    change
      (RingEquiv.ofBijective (boundaryProjectiveLineX1PolynomialToAway (k := k))
        ⟨boundaryProjectiveLineX1PolynomialToAway_injective (k := k),
          boundaryProjectiveLineX1PolynomialToAway_surjective (k := k)⟩).symm
          (boundaryProjectiveLineX1ConstantsToAway (k := k) a) = Polynomial.C a
    rw [← boundaryProjectiveLineX1PolynomialToAway_C (k := k) a]
    exact
      (RingEquiv.ofBijective (boundaryProjectiveLineX1PolynomialToAway (k := k))
        ⟨boundaryProjectiveLineX1PolynomialToAway_injective (k := k),
          boundaryProjectiveLineX1PolynomialToAway_surjective (k := k)⟩).symm_apply_apply
        (Polynomial.C a)

noncomputable def boundaryProjectiveLineConstructionData :
    BoundaryProjectiveLineConstructionData (k := k) where
  x0Chart := boundaryProjectiveLineX0ChartConstructionData (k := k)
  x1Chart := boundaryProjectiveLineX1ChartConstructionData (k := k)

/-- An explicit `x₀`-chart equivalence with `k[t]` yields the honest local
finite-type proof for that chart. -/
theorem boundaryProjectiveLineX0ChartLocallyOfFiniteType_of_constructionData
    (data : BoundaryProjectiveLineX0ChartConstructionData (k := k)) :
    LocallyOfFiniteType
      (boundaryProjectiveLineCoordinateAwayι (k := k) 0 ≫ boundaryProjectiveLineOverSpec k) := by
  rw [boundaryProjectiveLineX0ChartToBase]
  let e : CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) 0) ≅
      CommRingCat.of (Polynomial k) := data.ringEquiv.toCommRingCatIso
  letI : IsIso e.hom := e.isIso_hom
  have hring :
      CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k)) ≫ e.hom =
        CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) := by
    simpa [e] using data.commutes
  have hfac :
      Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k))) =
        affineLineStructMap k := by
    rw [← Spec.map_comp]
    simpa [affineLineStructMap] using congrArg Spec.map hring
  have hcomp :
      LocallyOfFiniteType
        (Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k)))) := by
    rw [hfac]
    exact affineLineLocallyOfFiniteType k
  exact
    (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)
      (Spec.map e.hom)
      (Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k))))).mp
      hcomp

/-- An explicit `x₁`-chart equivalence with `k[t]` yields the honest local
finite-type proof for that chart. -/
theorem boundaryProjectiveLineX1ChartLocallyOfFiniteType_of_constructionData
    (data : BoundaryProjectiveLineX1ChartConstructionData (k := k)) :
    LocallyOfFiniteType
      (boundaryProjectiveLineCoordinateAwayι (k := k) 1 ≫ boundaryProjectiveLineOverSpec k) := by
  rw [boundaryProjectiveLineX1ChartToBase]
  let e : CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) 1) ≅
      CommRingCat.of (Polynomial k) := data.ringEquiv.toCommRingCatIso
  letI : IsIso e.hom := e.isIso_hom
  have hring :
      CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k)) ≫ e.hom =
        CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) := by
    simpa [e] using data.commutes
  have hfac :
      Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k))) =
        affineLineStructMap k := by
    rw [← Spec.map_comp]
    simpa [affineLineStructMap] using congrArg Spec.map hring
  have hcomp :
      LocallyOfFiniteType
        (Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k)))) := by
    rw [hfac]
    exact affineLineLocallyOfFiniteType k
  exact
    (MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)
      (Spec.map e.hom)
      (Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k))))).mp
      hcomp

/-- An explicit `x₀`-chart equivalence with `k[t]` yields the honest smoothness
proof for that chart. -/
theorem boundaryProjectiveLineX0ChartSmooth_of_constructionData
    (data : BoundaryProjectiveLineX0ChartConstructionData (k := k)) :
    IsSmooth (boundaryProjectiveLineCoordinateAwayι (k := k) 0 ≫ boundaryProjectiveLineOverSpec k) := by
  rw [boundaryProjectiveLineX0ChartToBase]
  let e : CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) 0) ≅
      CommRingCat.of (Polynomial k) := data.ringEquiv.toCommRingCatIso
  letI : IsIso e.hom := e.isIso_hom
  have hring :
      CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k)) ≫ e.hom =
        CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) := by
    simpa [e] using data.commutes
  have hfac :
      Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k))) =
        affineLineStructMap k := by
    rw [← Spec.map_comp]
    simpa [affineLineStructMap] using congrArg Spec.map hring
  have hcomp :
      IsSmooth
        (Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k)))) := by
    rw [hfac]
    exact polynomialAffineLine_isSmooth k
  exact
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsSmooth)
      (Spec.map e.hom)
      (Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX0ConstantsToAway (k := k))))).mp
      hcomp

/-- An explicit `x₁`-chart equivalence with `k[t]` yields the honest smoothness
proof for that chart. -/
theorem boundaryProjectiveLineX1ChartSmooth_of_constructionData
    (data : BoundaryProjectiveLineX1ChartConstructionData (k := k)) :
    IsSmooth (boundaryProjectiveLineCoordinateAwayι (k := k) 1 ≫ boundaryProjectiveLineOverSpec k) := by
  rw [boundaryProjectiveLineX1ChartToBase]
  let e : CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) 1) ≅
      CommRingCat.of (Polynomial k) := data.ringEquiv.toCommRingCatIso
  letI : IsIso e.hom := e.isIso_hom
  have hring :
      CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k)) ≫ e.hom =
        CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) := by
    simpa [e] using data.commutes
  have hfac :
      Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k))) =
        affineLineStructMap k := by
    rw [← Spec.map_comp]
    simpa [affineLineStructMap] using congrArg Spec.map hring
  have hcomp :
      IsSmooth
        (Spec.map e.hom ≫
          Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k)))) := by
    rw [hfac]
    exact polynomialAffineLine_isSmooth k
  exact
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsSmooth)
      (Spec.map e.hom)
      (Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k))))).mp
      hcomp

/-- The canonical `Proj` structure morphism for the projective line model is
separated. -/
theorem boundaryProjectiveLineSeparatedToDegreeZero :
    IsSeparated (boundaryProjectiveLineStructMapToDegreeZero k) := by
  infer_instance

/-- The scheme `Proj(k[x₀, x₁])` is separated. -/
theorem boundaryProjectiveLineScheme_isSeparated :
    Scheme.IsSeparated (boundaryProjectiveLineScheme k) := by
  infer_instance

/-- Honest chartwise smoothness data for the concrete Boundary-side projective
line over `Spec k`, recorded on the two standard affine opens `D_+(x₀)` and
`D_+(x₁)`. -/
structure BoundaryProjectiveLineSmoothChartData where
  x0ChartSmooth :
    IsSmooth (boundaryProjectiveLineCoordinateAwayι (k := k) 0 ≫ boundaryProjectiveLineOverSpec k)
  x1ChartSmooth :
    IsSmooth (boundaryProjectiveLineCoordinateAwayι (k := k) 1 ≫ boundaryProjectiveLineOverSpec k)

/-- Honest chartwise local finite-type data for the concrete Boundary-side
projective line over `Spec k`, recorded on the two standard affine opens
`D_+(x₀)` and `D_+(x₁)`. -/
structure BoundaryProjectiveLineFiniteTypeChartData where
  x0ChartLocallyOfFiniteType :
    LocallyOfFiniteType
      (boundaryProjectiveLineCoordinateAwayι (k := k) 0 ≫ boundaryProjectiveLineOverSpec k)
  x1ChartLocallyOfFiniteType :
    LocallyOfFiniteType
      (boundaryProjectiveLineCoordinateAwayι (k := k) 1 ≫ boundaryProjectiveLineOverSpec k)

/-- Smoothness of the Boundary-side projective line over `Spec k` reduces to
smoothness on the two standard affine charts. -/
theorem boundaryProjectiveLineSmooth_of_chartData
    (chartData : BoundaryProjectiveLineSmoothChartData (k := k)) :
    IsSmooth (boundaryProjectiveLineOverSpec k) := by
  refine IsLocalAtSource.of_iSup_eq_top
      (P := @IsSmooth)
      (f := boundaryProjectiveLineOverSpec k)
      (fun i : Fin 2 =>
        AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
          (boundaryProjectiveLineCoordinate k i))
      (boundaryProjectiveLine_iSup_coordinate_basicOpen_eq_top (k := k)) ?_
  intro i
  fin_cases i
  · change IsSmooth
        ((AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 0)).ι ≫
          boundaryProjectiveLineOverSpec k)
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac
        (boundaryProjectiveLineCoordinateAwayι (k := k) 0)
        (Scheme.Opens.ι
          (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 0)))
        (congr_arg TopologicalSpace.Opens.carrier
          ((AlgebraicGeometry.Proj.opensRange_awayι
              (𝒜 := boundaryProjectiveLineGrading k)
              (f := boundaryProjectiveLineCoordinate k 0)
              (f_deg := boundaryProjectiveLineCoordinate_mem_degree_one k 0)
              (hm := by simp)).trans
            (Scheme.Opens.opensRange_ι
              (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
                (boundaryProjectiveLineCoordinate k 0))).symm)),
      Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @IsSmooth)]
    exact chartData.x0ChartSmooth
  · change IsSmooth
        ((AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 1)).ι ≫
          boundaryProjectiveLineOverSpec k)
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac
        (boundaryProjectiveLineCoordinateAwayι (k := k) 1)
        (Scheme.Opens.ι
          (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 1)))
        (congr_arg TopologicalSpace.Opens.carrier
          ((AlgebraicGeometry.Proj.opensRange_awayι
              (𝒜 := boundaryProjectiveLineGrading k)
              (f := boundaryProjectiveLineCoordinate k 1)
              (f_deg := boundaryProjectiveLineCoordinate_mem_degree_one k 1)
              (hm := by simp)).trans
            (Scheme.Opens.opensRange_ι
              (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
                (boundaryProjectiveLineCoordinate k 1))).symm)),
      Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @IsSmooth)]
    exact chartData.x1ChartSmooth

/-- Local finite type of the Boundary-side projective line over `Spec k`
reduces to the two standard affine charts. -/
theorem boundaryProjectiveLineLocallyOfFiniteType_of_chartData
    (chartData : BoundaryProjectiveLineFiniteTypeChartData (k := k)) :
    LocallyOfFiniteType (boundaryProjectiveLineOverSpec k) := by
  refine IsLocalAtSource.of_iSup_eq_top
      (P := @LocallyOfFiniteType)
      (f := boundaryProjectiveLineOverSpec k)
      (fun i : Fin 2 =>
        AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
          (boundaryProjectiveLineCoordinate k i))
      (boundaryProjectiveLine_iSup_coordinate_basicOpen_eq_top (k := k)) ?_
  intro i
  fin_cases i
  · change LocallyOfFiniteType
        ((AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 0)).ι ≫
          boundaryProjectiveLineOverSpec k)
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac
        (boundaryProjectiveLineCoordinateAwayι (k := k) 0)
        (Scheme.Opens.ι
          (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 0)))
        (congr_arg TopologicalSpace.Opens.carrier
          ((AlgebraicGeometry.Proj.opensRange_awayι
              (𝒜 := boundaryProjectiveLineGrading k)
              (f := boundaryProjectiveLineCoordinate k 0)
              (f_deg := boundaryProjectiveLineCoordinate_mem_degree_one k 0)
              (hm := by simp)).trans
            (Scheme.Opens.opensRange_ι
              (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
                (boundaryProjectiveLineCoordinate k 0))).symm)),
      Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)]
    exact chartData.x0ChartLocallyOfFiniteType
  · change LocallyOfFiniteType
        ((AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 1)).ι ≫
          boundaryProjectiveLineOverSpec k)
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac
        (boundaryProjectiveLineCoordinateAwayι (k := k) 1)
        (Scheme.Opens.ι
          (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k 1)))
        (congr_arg TopologicalSpace.Opens.carrier
          ((AlgebraicGeometry.Proj.opensRange_awayι
              (𝒜 := boundaryProjectiveLineGrading k)
              (f := boundaryProjectiveLineCoordinate k 1)
              (f_deg := boundaryProjectiveLineCoordinate_mem_degree_one k 1)
              (hm := by simp)).trans
            (Scheme.Opens.opensRange_ι
              (AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
                (boundaryProjectiveLineCoordinate k 1))).symm)),
      Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFiniteType)]
    exact chartData.x1ChartLocallyOfFiniteType

/-- Finite type of the Boundary-side projective line over `Spec k` reduces to
quasi-compactness together with the two chartwise local finite-type proofs. -/
theorem boundaryProjectiveLineFiniteType_of_chartData
    (quasiCompact : QuasiCompact (boundaryProjectiveLineOverSpec k))
    (chartData : BoundaryProjectiveLineFiniteTypeChartData (k := k)) :
    Geometry.IsOfFiniteType (boundaryProjectiveLineOverSpec k) := by
  exact ⟨quasiCompact,
    boundaryProjectiveLineLocallyOfFiniteType_of_chartData (k := k) chartData⟩

/-- The concrete Boundary-side projective line is quasi-compact over the affine
base `Spec k`, because the source is covered by the two compact affine chart
opens `D_+(x₀)` and `D_+(x₁)`. -/
theorem boundaryProjectiveLineOverSpec_quasiCompact :
    QuasiCompact (boundaryProjectiveLineOverSpec k) := by
  let U0 : (boundaryProjectiveLineScheme k).Opens :=
    AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
      (boundaryProjectiveLineCoordinate k 0)
  let U1 : (boundaryProjectiveLineScheme k).Opens :=
    AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
      (boundaryProjectiveLineCoordinate k 1)
  have h0 : IsCompact (U0 : Set (boundaryProjectiveLineScheme k)) := by
    exact (AlgebraicGeometry.Proj.isAffineOpen_basicOpen
      (𝒜 := boundaryProjectiveLineGrading k)
      (f := boundaryProjectiveLineCoordinate k 0)
      (f_deg := boundaryProjectiveLineCoordinate_mem_degree_one k 0)
      (hm := by simp)).isCompact
  have h1 : IsCompact (U1 : Set (boundaryProjectiveLineScheme k)) := by
    exact (AlgebraicGeometry.Proj.isAffineOpen_basicOpen
      (𝒜 := boundaryProjectiveLineGrading k)
      (f := boundaryProjectiveLineCoordinate k 1)
      (f_deg := boundaryProjectiveLineCoordinate_mem_degree_one k 1)
      (hm := by simp)).isCompact
  have hcover : (Set.univ : Set (boundaryProjectiveLineScheme k)) = (U0 : Set _) ∪ (U1 : Set _) := by
    ext x
    constructor
    · intro _
      have hx : x ∈ (⨆ i : Fin 2,
          AlgebraicGeometry.Proj.basicOpen (boundaryProjectiveLineGrading k)
            (boundaryProjectiveLineCoordinate k i) : (boundaryProjectiveLineScheme k).Opens) := by
        exact (boundaryProjectiveLine_iSup_coordinate_basicOpen_eq_top (k := k)).ge (by simp)
      rcases TopologicalSpace.Opens.mem_iSup.mp hx with ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    · intro _
      simp
  haveI : CompactSpace (boundaryProjectiveLineScheme k) := ⟨by
    simpa [hcover] using h0.union h1⟩
  rw [AlgebraicGeometry.quasiCompact_over_affine_iff]
  infer_instance

/-- The base object `Spec k` as an honest object of `Sm/k`. -/
def boundarySpecObject : Geometry.SmSchemeOver k where
  scheme := Spec (CommRingCat.of k)
  structMap := 𝟙 _
  smooth := by
    infer_instance
  separated := by
    infer_instance
  finiteType := by
    constructor <;> infer_instance

/-- Smoothness proof type for the raw projective-line map over `Spec k`. -/
abbrev BoundaryProjectiveLineSmoothOverBaseObligation :=
  IsSmooth (boundaryProjectiveLineOverSpec k)

/-- Finite-type proof type for the raw projective-line map over `Spec k`. -/
abbrev BoundaryProjectiveLineFiniteTypeOverBaseObligation :=
  Geometry.IsOfFiniteType (boundaryProjectiveLineOverSpec k)

/-- Any fully constructive chart witness package yields the honest chartwise
smoothness data needed to glue the projective-line structural morphism. -/
def BoundaryProjectiveLineConstructionData.toSmoothChartData
    (data : BoundaryProjectiveLineConstructionData (k := k)) :
    BoundaryProjectiveLineSmoothChartData (k := k) where
  x0ChartSmooth := boundaryProjectiveLineX0ChartSmooth_of_constructionData (k := k) data.x0Chart
  x1ChartSmooth := boundaryProjectiveLineX1ChartSmooth_of_constructionData (k := k) data.x1Chart

/-- Any fully constructive chart witness package yields the honest chartwise
local finite-type data needed to glue the projective-line structural morphism. -/
def BoundaryProjectiveLineConstructionData.toFiniteTypeChartData
    (data : BoundaryProjectiveLineConstructionData (k := k)) :
    BoundaryProjectiveLineFiniteTypeChartData (k := k) where
  x0ChartLocallyOfFiniteType :=
    boundaryProjectiveLineX0ChartLocallyOfFiniteType_of_constructionData (k := k) data.x0Chart
  x1ChartLocallyOfFiniteType :=
    boundaryProjectiveLineX1ChartLocallyOfFiniteType_of_constructionData (k := k) data.x1Chart

/-- A fully constructive affine-chart package proves global smoothness for the
Boundary-side projective line. -/
theorem boundaryProjectiveLineSmooth_of_constructionData
    (data : BoundaryProjectiveLineConstructionData (k := k)) :
    BoundaryProjectiveLineSmoothOverBaseObligation k := by
  exact boundaryProjectiveLineSmooth_of_chartData (k := k) data.toSmoothChartData

/-- A fully constructive affine-chart package proves global finite type for the
Boundary-side projective line. -/
theorem boundaryProjectiveLineFiniteType_of_constructionData
    (data : BoundaryProjectiveLineConstructionData (k := k)) :
    BoundaryProjectiveLineFiniteTypeOverBaseObligation k := by
  exact boundaryProjectiveLineFiniteType_of_chartData
    (k := k)
    (boundaryProjectiveLineOverSpec_quasiCompact (k := k))
    data.toFiniteTypeChartData

theorem boundaryProjectiveLineSmooth :
    BoundaryProjectiveLineSmoothOverBaseObligation k := by
  exact boundaryProjectiveLineSmooth_of_constructionData
    (k := k)
    (boundaryProjectiveLineConstructionData (k := k))

theorem boundaryProjectiveLineFiniteType :
    BoundaryProjectiveLineFiniteTypeOverBaseObligation k := by
  exact boundaryProjectiveLineFiniteType_of_constructionData
    (k := k)
    (boundaryProjectiveLineConstructionData (k := k))

/-- The raw `Proj` model lifted to the actual Boundary owner surface `Sm/k`,
using the supplied smoothness and finite-type proofs. -/
def boundaryProjectiveLineObject
    (smoothProof : BoundaryProjectiveLineSmoothOverBaseObligation k)
    (finiteTypeProof : BoundaryProjectiveLineFiniteTypeOverBaseObligation k) :
    Geometry.SmSchemeOver k where
  scheme := boundaryProjectiveLineScheme k
  structMap := boundaryProjectiveLineOverSpec k
  smooth := smoothProof
  separated := by
    letI : IsSeparated (boundaryProjectiveLineStructMapToDegreeZero k) :=
      boundaryProjectiveLineSeparatedToDegreeZero k
    infer_instance
  finiteType := finiteTypeProof

noncomputable def boundaryProjectiveLineConcreteObject : Geometry.SmSchemeOver k :=
  boundaryProjectiveLineObject
    (k := k)
    (boundaryProjectiveLineSmooth (k := k))
    (boundaryProjectiveLineFiniteType (k := k))

/-- Type of basepoint maps `Spec k ⟶ P¹_k` compatible with the structure map. -/
abbrev BoundaryProjectiveLineBasepointObligation
    (smoothProof : BoundaryProjectiveLineSmoothOverBaseObligation k)
    (finiteTypeProof : BoundaryProjectiveLineFiniteTypeOverBaseObligation k) :=
  Boundary.SmOverHom
    (boundarySpecObject k)
    (boundaryProjectiveLineObject k smoothProof finiteTypeProof)

/-- Evaluation at the origin on the `x₁`-chart picks out the rational point
`[0:1]` of the concrete projective line. -/
abbrev boundaryProjectiveLineX1BasepointRingHom :
    boundaryProjectiveLineCoordinateAwayRing (k := k) 1 →+* k :=
  (Polynomial.eval₂RingHom (RingHom.id k) (0 : k)).comp
    (boundaryProjectiveLineX1AwayToPolynomial (k := k))

/-- The chosen rational point on the `x₁` chart, viewed before composing with
the open immersion into the projective line. -/
abbrev boundaryProjectiveLineX1BasepointChart :
    Spec (CommRingCat.of k) ⟶
      Spec (CommRingCat.of (boundaryProjectiveLineCoordinateAwayRing (k := k) 1)) :=
  Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1BasepointRingHom (k := k)))

/-- The chosen rational point on the `x₁` chart lies over the base `Spec k`. -/
theorem boundaryProjectiveLineX1BasepointChart_over_base :
    boundaryProjectiveLineX1BasepointChart (k := k) ≫
        Spec.map (CommRingCat.ofHom (boundaryProjectiveLineX1ConstantsToAway (k := k))) =
      𝟙 (Spec (CommRingCat.of k)) := by
  rw [boundaryProjectiveLineX1BasepointChart, ← Spec.map_id, ← Spec.map_comp]
  congr 1
  ext a
  change boundaryProjectiveLineX1BasepointRingHom (k := k)
      (boundaryProjectiveLineX1ConstantsToAway (k := k) a) = a
  rw [boundaryProjectiveLineX1BasepointRingHom, RingHom.comp_apply,
    boundaryProjectiveLineX1AwayToPolynomial_constants]
  simp

/-- Canonical Boundary-side basepoint on `P¹_k`, given by the chart point
`[0:1]` on the standard `x₁` affine chart. -/
def boundaryProjectiveLineCanonicalBasepoint
    (smoothProof : BoundaryProjectiveLineSmoothOverBaseObligation k)
    (finiteTypeProof : BoundaryProjectiveLineFiniteTypeOverBaseObligation k) :
    BoundaryProjectiveLineBasepointObligation k smoothProof finiteTypeProof where
  hom := boundaryProjectiveLineX1BasepointChart (k := k) ≫
    boundaryProjectiveLineCoordinateAwayι (k := k) 1
  over := by
    change (boundaryProjectiveLineX1BasepointChart k ≫
        boundaryProjectiveLineCoordinateAwayι (k := k) 1) ≫
          boundaryProjectiveLineOverSpec k = 𝟙 _
    rw [Category.assoc, boundaryProjectiveLineX1ChartToBase,
      boundaryProjectiveLineX1BasepointChart_over_base]

/-- A basepoint morphism in the Boundary owner surface, once the corresponding
owner obligation has been discharged. -/
def boundaryP1Basepoint
    (smoothProof : BoundaryProjectiveLineSmoothOverBaseObligation k)
    (finiteTypeProof : BoundaryProjectiveLineFiniteTypeOverBaseObligation k)
    (basepoint : BoundaryProjectiveLineBasepointObligation k smoothProof finiteTypeProof) :
    Boundary.SmOverHom
      (boundarySpecObject k)
      (boundaryProjectiveLineObject k smoothProof finiteTypeProof) :=
  basepoint

end

end Boundary
