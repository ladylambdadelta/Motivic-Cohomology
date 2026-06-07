import Boundary.DiagonalDecomposition
import Mathlib.Data.Finsupp.Basic

/-!
# Finite Correspondence Composition Category

This file packages bilinear composition on finite correspondences together with
the corresponding categorical law bundle and the bundled `SmCor(k)` category.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

/-- Honest input for composing geometric prime finite correspondences.

The field `compPrime p q` is the geometric composition of prime correspondence
classes `p : X ⟶ Y` and `q : Y ⟶ Z`, valued in finite correspondences from `X`
to `Z`. A chosen finite irreducible-component decomposition on each object
supplies the diagonal identity correspondence. -/
structure FiniteCorrespondenceCompositionData where
  diagonalDecomposition :
    (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X
  compPrime :
    {X Y Z : Geometry.SmSchemeOver k} →
    PrimeFiniteCorrespondenceGeom X Y →
    PrimeFiniteCorrespondenceGeom Y Z →
    FiniteCorrespondence X Z

namespace FiniteCorrespondenceCompositionData

/-- The diagonal finite correspondence determined by the chosen source-side
decomposition. -/
def id (data : FiniteCorrespondenceCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) : FiniteCorrespondence X X :=
  (data.diagonalDecomposition X).identityFiniteCorrespondence

/-- Bilinear extension of prime correspondence composition to arbitrary finite
correspondences. -/
def comp (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondence X Z :=
  left.sum fun leftPrime leftCoeff =>
    right.sum fun rightPrime rightCoeff =>
      (leftCoeff * rightCoeff) • data.compPrime leftPrime rightPrime

@[simp] theorem id_def (data : FiniteCorrespondenceCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) :
    data.id X = (data.diagonalDecomposition X).identityFiniteCorrespondence :=
  rfl

@[simp] theorem comp_zero_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data (0 : FiniteCorrespondence X Y) right = 0 := by
  rw [FiniteCorrespondenceCompositionData.comp]
  simp

@[simp] theorem comp_zero_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp data left (0 : FiniteCorrespondence Y Z) = 0 := by
  rw [FiniteCorrespondenceCompositionData.comp]
  simp

@[simp] theorem comp_single_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X Y)
    (leftCoeff : ℤ)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data (Finsupp.single leftPrime leftCoeff) right =
      right.sum fun rightPrime rightCoeff =>
        (leftCoeff * rightCoeff) • data.compPrime leftPrime rightPrime := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp]
  simp

@[simp] theorem comp_single_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y)
    (rightPrime : PrimeFiniteCorrespondenceGeom Y Z)
    (rightCoeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data left (Finsupp.single rightPrime rightCoeff) =
      left.sum fun leftPrime leftCoeff =>
        (leftCoeff * rightCoeff) • data.compPrime leftPrime rightPrime := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp]
  simp

@[simp] theorem comp_single_single (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X Y)
    (rightPrime : PrimeFiniteCorrespondenceGeom Y Z)
    (leftCoeff rightCoeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data (Finsupp.single leftPrime leftCoeff)
      (Finsupp.single rightPrime rightCoeff) =
        (leftCoeff * rightCoeff) • data.compPrime leftPrime rightPrime := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp]
  simp

/-- To prove singleton associativity, it is enough to prove the corresponding
bridge after rewriting the inner singleton compositions into scaled prime-level
composites. This isolates the genuine geometric associativity obligation. -/
theorem assoc_single_of_scaled_prime_assoc
    (data : FiniteCorrespondenceCompositionData (k := k))
    (assoc_scaled_prime :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
        (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
        (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            ((fCoeff * gCoeff) •
              (FiniteCorrespondenceCompositionData.compPrime data f g))
            (Finsupp.single h hCoeff) =
              FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single f fCoeff)
                ((gCoeff * hCoeff) •
                  (FiniteCorrespondenceCompositionData.compPrime data g h))) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data
          (FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f fCoeff)
              (FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single g gCoeff) (Finsupp.single h hCoeff)) := by
  intro W X Y Z f fCoeff g gCoeff h hCoeff
  rw [FiniteCorrespondenceCompositionData.comp_single_single,
    FiniteCorrespondenceCompositionData.comp_single_single]
  exact assoc_scaled_prime f fCoeff g gCoeff h hCoeff

theorem comp_add_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left₁ left₂ : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data (left₁ + left₂) right =
      FiniteCorrespondenceCompositionData.comp data left₁ right +
        FiniteCorrespondenceCompositionData.comp data left₂ right := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    Finsupp.sum_add_index'] <;>
    simp [add_mul, add_smul, zero_mul]

theorem comp_add_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y)
    (right₁ right₂ : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data left (right₁ + right₂) =
      FiniteCorrespondenceCompositionData.comp data left right₁ +
        FiniteCorrespondenceCompositionData.comp data left right₂ := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    ← Finsupp.sum_add]
  congr
  ext leftPrime leftCoeff
  rw [Finsupp.sum_add_index'] <;> simp [mul_add, add_smul, zero_mul]

theorem comp_smul_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data (coeff • left) right =
      coeff • FiniteCorrespondenceCompositionData.comp data left right := by
  apply Finsupp.induction_linear left
  · simp
  · intro left₁ left₂ ih₁ ih₂
    rw [smul_add, FiniteCorrespondenceCompositionData.comp_add_left, ih₁, ih₂,
      ← smul_add, FiniteCorrespondenceCompositionData.comp_add_left]
  · intro prime primeCoeff
    apply Finsupp.induction_linear right
    · simp
    · intro right₁ right₂ ihRight₁ ihRight₂
      rw [FiniteCorrespondenceCompositionData.comp_add_right,
        FiniteCorrespondenceCompositionData.comp_add_right, ihRight₁, ihRight₂,
        smul_add]
    · intro rightPrime rightCoeff
      calc
        FiniteCorrespondenceCompositionData.comp data
            (coeff • Finsupp.single prime primeCoeff)
            (Finsupp.single rightPrime rightCoeff)
            = FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single prime (coeff * primeCoeff))
                (Finsupp.single rightPrime rightCoeff) := by
              simp
        _ = coeff • FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single prime primeCoeff)
              (Finsupp.single rightPrime rightCoeff) := by
              rw [FiniteCorrespondenceCompositionData.comp_single_single,
                FiniteCorrespondenceCompositionData.comp_single_single]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

theorem comp_smul_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data left (coeff • right) =
      coeff • FiniteCorrespondenceCompositionData.comp data left right := by
  apply Finsupp.induction_linear right
  · simp
  · intro right₁ right₂ ih₁ ih₂
    rw [smul_add, FiniteCorrespondenceCompositionData.comp_add_right, ih₁, ih₂,
      ← smul_add, FiniteCorrespondenceCompositionData.comp_add_right]
  · intro prime primeCoeff
    apply Finsupp.induction_linear left
    · simp
    · intro left₁ left₂ ihLeft₁ ihLeft₂
      rw [FiniteCorrespondenceCompositionData.comp_add_left,
        FiniteCorrespondenceCompositionData.comp_add_left, ihLeft₁, ihLeft₂,
        smul_add]
    · intro leftPrime leftCoeff
      calc
        FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single leftPrime leftCoeff)
            (coeff • Finsupp.single prime primeCoeff)
            = FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single leftPrime leftCoeff)
                (Finsupp.single prime (coeff * primeCoeff)) := by
              simp
        _ = coeff • FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single leftPrime leftCoeff)
              (Finsupp.single prime primeCoeff) := by
              rw [FiniteCorrespondenceCompositionData.comp_single_single,
                FiniteCorrespondenceCompositionData.comp_single_single]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- To prove the scaled prime associativity bridge, it is enough to prove the
corresponding coefficient-free prime associativity statement. Bilinearity of
`comp` then inserts the three singleton coefficients automatically. -/
theorem assoc_scaled_prime_of_prime_assoc
    (data : FiniteCorrespondenceCompositionData (k := k))
    (assoc_prime :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W X)
        (g : PrimeFiniteCorrespondenceGeom X Y)
        (h : PrimeFiniteCorrespondenceGeom Y Z),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.compPrime data f g)
            (Finsupp.single h 1) =
              FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single f 1)
                (FiniteCorrespondenceCompositionData.compPrime data g h)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data
          ((fCoeff * gCoeff) •
            (FiniteCorrespondenceCompositionData.compPrime data f g))
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f fCoeff)
              ((gCoeff * hCoeff) •
                (FiniteCorrespondenceCompositionData.compPrime data g h)) := by
  intro W X Y Z f fCoeff g gCoeff h hCoeff
  calc
    FiniteCorrespondenceCompositionData.comp data
        ((fCoeff * gCoeff) •
          (FiniteCorrespondenceCompositionData.compPrime data f g))
        (Finsupp.single h hCoeff)
        = FiniteCorrespondenceCompositionData.comp data
            ((fCoeff * gCoeff) •
              (FiniteCorrespondenceCompositionData.compPrime data f g))
            (hCoeff • Finsupp.single h 1) := by
              simp
    _ = hCoeff •
          FiniteCorrespondenceCompositionData.comp data
            ((fCoeff * gCoeff) •
              (FiniteCorrespondenceCompositionData.compPrime data f g))
            (Finsupp.single h 1) := by
              rw [FiniteCorrespondenceCompositionData.comp_smul_right]
    _ = hCoeff •
          ((fCoeff * gCoeff) •
            FiniteCorrespondenceCompositionData.comp data
              (FiniteCorrespondenceCompositionData.compPrime data f g)
              (Finsupp.single h 1)) := by
                rw [FiniteCorrespondenceCompositionData.comp_smul_left]
    _ = (fCoeff * (gCoeff * hCoeff)) •
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.compPrime data f g)
            (Finsupp.single h 1) := by
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = (fCoeff * (gCoeff * hCoeff)) •
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single f 1)
            (FiniteCorrespondenceCompositionData.compPrime data g h) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                congrArg (fun corr => (fCoeff * (gCoeff * hCoeff)) • corr)
                  (assoc_prime f g h)
    _ = fCoeff •
          ((gCoeff * hCoeff) •
            FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime data g h)) := by
                simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = fCoeff •
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single f 1)
            ((gCoeff * hCoeff) •
              (FiniteCorrespondenceCompositionData.compPrime data g h)) := by
                rw [← FiniteCorrespondenceCompositionData.comp_smul_right]
    _ = FiniteCorrespondenceCompositionData.comp data
          (fCoeff • Finsupp.single f 1)
          ((gCoeff * hCoeff) •
            (FiniteCorrespondenceCompositionData.compPrime data g h)) := by
              rw [← FiniteCorrespondenceCompositionData.comp_smul_left]
    _ = FiniteCorrespondenceCompositionData.comp data
          (Finsupp.single f fCoeff)
          ((gCoeff * hCoeff) •
            (FiniteCorrespondenceCompositionData.compPrime data g h)) := by
              simp

/-- Extend left singleton identity against the diagonal correspondence to all
finite correspondences by linearity. -/
theorem id_comp_of_singleton_identities
    (data : FiniteCorrespondenceCompositionData (k := k))
    (id_comp_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.id data X)
            (Finsupp.single prime coeff) =
              Finsupp.single prime coeff)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp data
      (FiniteCorrespondenceCompositionData.id data X) f = f := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    rw [FiniteCorrespondenceCompositionData.comp_add_right, hf₁, hf₂]
  · intro prime coeff
    exact id_comp_single prime coeff

/-- Extend right singleton identity against the diagonal correspondence to all
finite correspondences by linearity. -/
theorem comp_id_of_singleton_identities
    (data : FiniteCorrespondenceCompositionData (k := k))
    (comp_id_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single prime coeff)
            (FiniteCorrespondenceCompositionData.id data Y) =
              Finsupp.single prime coeff)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp data
      f (FiniteCorrespondenceCompositionData.id data Y) = f := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    rw [FiniteCorrespondenceCompositionData.comp_add_left, hf₁, hf₂]
  · intro prime coeff
    exact comp_id_single prime coeff

/-- Extend singleton associativity to all finite correspondences by trilinearity. -/
theorem assoc_of_singleton_associativity
    (data : FiniteCorrespondenceCompositionData (k := k))
    (assoc_single :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
        (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
        (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
            (Finsupp.single h hCoeff) =
              FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single f fCoeff)
                (FiniteCorrespondenceCompositionData.comp data
                  (Finsupp.single g gCoeff) (Finsupp.single h hCoeff)))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W X)
    (g : FiniteCorrespondence X Y)
    (h : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data
      (FiniteCorrespondenceCompositionData.comp data f g) h =
        FiniteCorrespondenceCompositionData.comp data f
          (FiniteCorrespondenceCompositionData.comp data g h) := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    rw [FiniteCorrespondenceCompositionData.comp_add_left,
      FiniteCorrespondenceCompositionData.comp_add_left,
      FiniteCorrespondenceCompositionData.comp_add_left,
      hf₁, hf₂]
  · intro fPrime fCoeff
    apply Finsupp.induction_linear g
    · simp
    · intro g₁ g₂ hg₁ hg₂
      rw [FiniteCorrespondenceCompositionData.comp_add_right,
        FiniteCorrespondenceCompositionData.comp_add_left,
        FiniteCorrespondenceCompositionData.comp_add_left,
        FiniteCorrespondenceCompositionData.comp_add_right,
        hg₁, hg₂]
    · intro gPrime gCoeff
      apply Finsupp.induction_linear h
      · simp
      · intro h₁ h₂ hh₁ hh₂
        rw [FiniteCorrespondenceCompositionData.comp_add_right,
          FiniteCorrespondenceCompositionData.comp_add_right,
          FiniteCorrespondenceCompositionData.comp_add_right,
          hh₁, hh₂]
      · intro hPrime hCoeff
        exact assoc_single fPrime fCoeff gPrime gCoeff hPrime hCoeff

end FiniteCorrespondenceCompositionData

/-- Law package for the correspondence composition determined by
`FiniteCorrespondenceCompositionData`. These are the categorical and additive
properties of finite correspondences once the underlying geometric composition
has been supplied. -/
structure FiniteCorrespondenceCategoryLaws
  (data : FiniteCorrespondenceCompositionData (k := k)) where
  id_comp :
    ∀ {X Y : Geometry.SmSchemeOver k} (f : FiniteCorrespondence X Y),
      FiniteCorrespondenceCompositionData.comp data (FiniteCorrespondenceCompositionData.id data X) f = f
  comp_id :
    ∀ {X Y : Geometry.SmSchemeOver k} (f : FiniteCorrespondence X Y),
      FiniteCorrespondenceCompositionData.comp data f (FiniteCorrespondenceCompositionData.id data Y) = f
  assoc :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : FiniteCorrespondence W X)
      (g : FiniteCorrespondence X Y)
      (h : FiniteCorrespondence Y Z),
        FiniteCorrespondenceCompositionData.comp data
          (FiniteCorrespondenceCompositionData.comp data f g) h =
            FiniteCorrespondenceCompositionData.comp data f
              (FiniteCorrespondenceCompositionData.comp data g h)
  zero_comp :
    ∀ {X Y Z : Geometry.SmSchemeOver k} (f : FiniteCorrespondence Y Z),
      FiniteCorrespondenceCompositionData.comp data (0 : FiniteCorrespondence X Y) f = 0
  comp_zero :
    ∀ {X Y Z : Geometry.SmSchemeOver k} (f : FiniteCorrespondence X Y),
      FiniteCorrespondenceCompositionData.comp data f (0 : FiniteCorrespondence Y Z) = 0
  add_comp :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (f g : FiniteCorrespondence X Y)
      (h : FiniteCorrespondence Y Z),
        FiniteCorrespondenceCompositionData.comp data (f + g) h =
          FiniteCorrespondenceCompositionData.comp data f h +
            FiniteCorrespondenceCompositionData.comp data g h
  comp_add :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (f : FiniteCorrespondence X Y)
      (g h : FiniteCorrespondence Y Z),
        FiniteCorrespondenceCompositionData.comp data f (g + h) =
          FiniteCorrespondenceCompositionData.comp data f g +
            FiniteCorrespondenceCompositionData.comp data f h

namespace FiniteCorrespondenceCategoryLaws

/-- Build the full correspondence category law package from the bilinear
composition formulas together with singleton identity and singleton
associativity laws. -/
def ofSingletonLaws
    (data : FiniteCorrespondenceCompositionData (k := k))
    (id_comp_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.id data X)
            (Finsupp.single prime coeff) =
              Finsupp.single prime coeff)
    (comp_id_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single prime coeff)
            (FiniteCorrespondenceCompositionData.id data Y) =
              Finsupp.single prime coeff)
    (assoc_single :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
        (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
        (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
            (Finsupp.single h hCoeff) =
              FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single f fCoeff)
                (FiniteCorrespondenceCompositionData.comp data
                  (Finsupp.single g gCoeff) (Finsupp.single h hCoeff))) :
    FiniteCorrespondenceCategoryLaws data where
  id_comp := by
    intro X Y f
    exact FiniteCorrespondenceCompositionData.id_comp_of_singleton_identities
      data id_comp_single f
  comp_id := by
    intro X Y f
    exact FiniteCorrespondenceCompositionData.comp_id_of_singleton_identities
      data comp_id_single f
  assoc := by
    intro W X Y Z f g h
    exact FiniteCorrespondenceCompositionData.assoc_of_singleton_associativity
      data assoc_single f g h
  zero_comp := by
    intro X Y Z f
    exact FiniteCorrespondenceCompositionData.comp_zero_left data f
  comp_zero := by
    intro X Y Z f
    exact FiniteCorrespondenceCompositionData.comp_zero_right data f
  add_comp := by
    intro X Y Z f g h
    exact FiniteCorrespondenceCompositionData.comp_add_left data f g h
  comp_add := by
    intro X Y Z f g h
    exact FiniteCorrespondenceCompositionData.comp_add_right data f g h

end FiniteCorrespondenceCategoryLaws

/-- Bundled `SmCor(k)` correspondence category on smooth `k`-schemes.

The objects are smooth schemes over `k`, the morphisms are finite
correspondences, identities come from the chosen diagonal decompositions, and
composition is the bilinear extension of the supplied prime-level composition
law. -/
structure SmCor where
  composition : FiniteCorrespondenceCompositionData (k := k)
  laws : FiniteCorrespondenceCategoryLaws composition

namespace SmCor

/-- Morphisms in the correspondence category are finite correspondences. -/
abbrev Hom (_category : SmCor (k := k))
    (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  FiniteCorrespondence X Y

/-- Identity correspondence in the bundled `SmCor` category. -/
def id (category : SmCor (k := k)) (X : Geometry.SmSchemeOver k) : SmCor.Hom category X X :=
  FiniteCorrespondenceCompositionData.id category.composition X

/-- Composition in the bundled `SmCor` category. -/
def comp (category : SmCor (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category X Y)
    (g : SmCor.Hom category Y Z) : SmCor.Hom category X Z :=
  FiniteCorrespondenceCompositionData.comp category.composition f g

theorem id_comp (category : SmCor (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category X Y) :
    SmCor.comp category (SmCor.id category X) f = f :=
  category.laws.id_comp f

theorem comp_id (category : SmCor (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category X Y) :
    SmCor.comp category f (SmCor.id category Y) = f :=
  category.laws.comp_id f

theorem assoc (category : SmCor (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category W X)
    (g : SmCor.Hom category X Y)
    (h : SmCor.Hom category Y Z) :
    SmCor.comp category (SmCor.comp category f g) h =
      SmCor.comp category f (SmCor.comp category g h) :=
  category.laws.assoc f g h

theorem zero_comp (category : SmCor (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category Y Z) :
    SmCor.comp category (0 : SmCor.Hom category X Y) f = 0 :=
  category.laws.zero_comp f

theorem comp_zero (category : SmCor (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category X Y) :
    SmCor.comp category f (0 : SmCor.Hom category Y Z) = 0 :=
  category.laws.comp_zero f

theorem add_comp (category : SmCor (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f g : SmCor.Hom category X Y)
    (h : SmCor.Hom category Y Z) :
    SmCor.comp category (f + g) h = SmCor.comp category f h + SmCor.comp category g h :=
  category.laws.add_comp f g h

theorem comp_add (category : SmCor (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCor.Hom category X Y)
    (g h : SmCor.Hom category Y Z) :
    SmCor.comp category f (g + h) = SmCor.comp category f g + SmCor.comp category f h :=
  category.laws.comp_add f g h

def categoryStruct (category : SmCor (k := k)) : CategoryStruct (Geometry.SmSchemeOver k) where
  Hom X Y := SmCor.Hom category X Y
  id := SmCor.id category
  comp := fun f g => SmCor.comp category f g

def toCategory (category : SmCor (k := k)) : Category (Geometry.SmSchemeOver k) where
  Hom X Y := SmCor.Hom category X Y
  id := SmCor.id category
  comp := fun f g => SmCor.comp category f g
  id_comp := SmCor.id_comp category
  comp_id := SmCor.comp_id category
  assoc := SmCor.assoc category

end SmCor

end

end Boundary
