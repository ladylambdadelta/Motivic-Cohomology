import Boundary.CorrespondenceRationalization
import Boundary.CompositionCategory
import Boundary.ExternalProduct
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Rational Finite Correspondence Composition

This file lifts integral finite-correspondence composition to rational
coefficients and records the compatibility with coefficient extension.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

namespace FiniteCorrespondenceCompositionData

/-- Rational identity correspondence induced by the chosen diagonal
decomposition. -/
def idQ (data : FiniteCorrespondenceCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) : RationalFiniteCorrespondence X X :=
  (data.diagonalDecomposition X).identityFiniteCorrespondenceQ

@[simp] theorem idQ_eq_toRational_id (data : FiniteCorrespondenceCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) :
    data.idQ X = FiniteCorrespondence.toRational (data.id X) :=
  rfl

/-- Bilinear extension of prime correspondence composition to rational finite
correspondences. -/
def compQ (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : RationalFiniteCorrespondence X Y)
    (right : RationalFiniteCorrespondence Y Z) :
    RationalFiniteCorrespondence X Z :=
  left.sum fun leftPrime leftCoeff =>
    right.sum fun rightPrime rightCoeff =>
      (leftCoeff * rightCoeff) • FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime)

@[simp] theorem idQ_def (data : FiniteCorrespondenceCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) :
    data.idQ X = (data.diagonalDecomposition X).identityFiniteCorrespondenceQ :=
  rfl

@[simp] theorem compQ_zero_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (right : RationalFiniteCorrespondence Y Z) :
    data.compQ (0 : RationalFiniteCorrespondence X Y) right = 0 := by
  rw [FiniteCorrespondenceCompositionData.compQ]
  simp

@[simp] theorem compQ_zero_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : RationalFiniteCorrespondence X Y) :
    data.compQ left (0 : RationalFiniteCorrespondence Y Z) = 0 := by
  rw [FiniteCorrespondenceCompositionData.compQ]
  simp

theorem compQ_add_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left₁ left₂ : RationalFiniteCorrespondence X Y)
    (right : RationalFiniteCorrespondence Y Z) :
    data.compQ (left₁ + left₂) right = data.compQ left₁ right + data.compQ left₂ right := by
  classical
  rw [FiniteCorrespondenceCompositionData.compQ,
    FiniteCorrespondenceCompositionData.compQ,
    FiniteCorrespondenceCompositionData.compQ,
    Finsupp.sum_add_index'] <;>
    simp [add_mul, add_smul, zero_mul]

theorem compQ_add_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : RationalFiniteCorrespondence X Y)
    (right₁ right₂ : RationalFiniteCorrespondence Y Z) :
    data.compQ left (right₁ + right₂) = data.compQ left right₁ + data.compQ left right₂ := by
  classical
  rw [FiniteCorrespondenceCompositionData.compQ,
    FiniteCorrespondenceCompositionData.compQ,
    FiniteCorrespondenceCompositionData.compQ,
    ← Finsupp.sum_add]
  congr
  ext leftPrime leftCoeff
  rw [Finsupp.sum_add_index'] <;> simp [mul_add, add_smul, zero_mul]

@[simp] theorem compQ_single_single (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X Y)
    (rightPrime : PrimeFiniteCorrespondenceGeom Y Z)
    (leftCoeff rightCoeff : ℚ) :
    data.compQ (Finsupp.single leftPrime leftCoeff)
      (Finsupp.single rightPrime rightCoeff) =
        (leftCoeff * rightCoeff) • FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime) := by
  classical
  rw [FiniteCorrespondenceCompositionData.compQ]
  simp

theorem compQ_smul_left (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : RationalFiniteCorrespondence X Y)
    (right : RationalFiniteCorrespondence Y Z) :
    data.compQ (coeff • left) right = coeff • data.compQ left right := by
  apply Finsupp.induction_linear left
  · simp
  · intro left₁ left₂ ihLeft₁ ihLeft₂
    rw [smul_add, FiniteCorrespondenceCompositionData.compQ_add_left, ihLeft₁, ihLeft₂,
      ← smul_add, FiniteCorrespondenceCompositionData.compQ_add_left]
  · intro prime primeCoeff
    apply Finsupp.induction_linear right
    · simp
    · intro right₁ right₂ ihRight₁ ihRight₂
      rw [FiniteCorrespondenceCompositionData.compQ_add_right,
        FiniteCorrespondenceCompositionData.compQ_add_right, ihRight₁, ihRight₂,
        smul_add]
    · intro rightPrime rightCoeff
      calc
        data.compQ (coeff • Finsupp.single prime primeCoeff)
            (Finsupp.single rightPrime rightCoeff)
            = data.compQ (Finsupp.single prime (coeff * primeCoeff))
                (Finsupp.single rightPrime rightCoeff) := by
              simp
        _ = coeff • data.compQ (Finsupp.single prime primeCoeff)
              (Finsupp.single rightPrime rightCoeff) := by
              rw [FiniteCorrespondenceCompositionData.compQ_single_single,
                FiniteCorrespondenceCompositionData.compQ_single_single]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

theorem compQ_smul_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : RationalFiniteCorrespondence X Y)
    (right : RationalFiniteCorrespondence Y Z) :
    data.compQ left (coeff • right) = coeff • data.compQ left right := by
  apply Finsupp.induction_linear right
  · simp
  · intro right₁ right₂ ihRight₁ ihRight₂
    rw [smul_add, FiniteCorrespondenceCompositionData.compQ_add_right, ihRight₁, ihRight₂,
      ← smul_add, FiniteCorrespondenceCompositionData.compQ_add_right]
  · intro prime primeCoeff
    apply Finsupp.induction_linear left
    · simp
    · intro left₁ left₂ ihLeft₁ ihLeft₂
      rw [FiniteCorrespondenceCompositionData.compQ_add_left,
        FiniteCorrespondenceCompositionData.compQ_add_left, ihLeft₁, ihLeft₂,
        smul_add]
    · intro leftPrime leftCoeff
      calc
        data.compQ (Finsupp.single leftPrime leftCoeff)
            (coeff • Finsupp.single prime primeCoeff)
            = data.compQ (Finsupp.single leftPrime leftCoeff)
                (Finsupp.single prime (coeff * primeCoeff)) := by
              simp
        _ = coeff • data.compQ (Finsupp.single leftPrime leftCoeff)
              (Finsupp.single prime primeCoeff) := by
              rw [FiniteCorrespondenceCompositionData.compQ_single_single,
                FiniteCorrespondenceCompositionData.compQ_single_single]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- Rational composition agrees with integral composition after coefficient
extension from `ℤ` to `ℚ`. -/
theorem compQ_toRational (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    data.compQ (FiniteCorrespondence.toRational left) (FiniteCorrespondence.toRational right) =
      FiniteCorrespondence.toRational (data.comp left right) := by
  classical
  apply Finsupp.induction_linear left
  · simp
  · intro left₁ left₂ ihLeft₁ ihLeft₂
    rw [FiniteCorrespondence.toRational_add, FiniteCorrespondenceCompositionData.compQ_add_left,
      FiniteCorrespondenceCompositionData.comp_add_left, FiniteCorrespondence.toRational_add,
      ihLeft₁, ihLeft₂]
  · intro leftPrime leftCoeff
    apply Finsupp.induction_linear right
    · simp
    · intro right₁ right₂ ihRight₁ ihRight₂
      rw [FiniteCorrespondence.toRational_add, FiniteCorrespondenceCompositionData.compQ_add_right,
        FiniteCorrespondenceCompositionData.comp_add_right, FiniteCorrespondence.toRational_add,
        ihRight₁, ihRight₂]
    · intro rightPrime rightCoeff
      calc
        data.compQ (FiniteCorrespondence.toRational (Finsupp.single leftPrime leftCoeff))
            (FiniteCorrespondence.toRational (Finsupp.single rightPrime rightCoeff))
            = data.compQ ((leftCoeff : ℚ) • Finsupp.single leftPrime (1 : ℚ))
                ((rightCoeff : ℚ) • Finsupp.single rightPrime (1 : ℚ)) := by
                  rw [FiniteCorrespondence.toRational_single,
                    FiniteCorrespondence.toRational_single]
                  simp
        _ = ((leftCoeff : ℚ) * (rightCoeff : ℚ)) •
              data.compQ (Finsupp.single leftPrime (1 : ℚ))
                (Finsupp.single rightPrime (1 : ℚ)) := by
                  rw [FiniteCorrespondenceCompositionData.compQ_smul_left,
                    FiniteCorrespondenceCompositionData.compQ_smul_right]
                  rw [smul_smul]
        _ = ((leftCoeff : ℚ) * (rightCoeff : ℚ)) •
              FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime) := by
                rw [FiniteCorrespondenceCompositionData.compQ_single_single]
                simp [smul_smul, mul_assoc]
        _ = (((leftCoeff * rightCoeff : ℤ) : ℚ)) •
              FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime) := by
                simp using congrArg
                  (fun coeff : ℚ => coeff • FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime))
                  (Int.cast_mul leftCoeff rightCoeff).symm
        _ = FiniteCorrespondence.toRational
              ((leftCoeff * rightCoeff) • data.compPrime leftPrime rightPrime) := by
                ext prime
                rw [FiniteCorrespondence.toRational_smul]
                simp
        _ = (data.comp (Finsupp.single leftPrime leftCoeff)
              (Finsupp.single rightPrime rightCoeff)).toRational := by
                rw [FiniteCorrespondenceCompositionData.comp_single_single]

end FiniteCorrespondenceCompositionData

/-- Bundled `SmCor_Q(k)` category obtained by rationalizing the morphism groups
of an integral `SmCor(k)` package. -/
structure SmCorQ where
  integral : SmCor (k := k)

namespace SmCorQ

open _root_.Boundary.FiniteCorrespondence

/-- Morphisms in the rationalized correspondence category are rational finite
correspondences. -/
abbrev Hom (_category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  RationalFiniteCorrespondence X Y

/-- Identity correspondence in the bundled `SmCor_Q` category. -/
def id (category : SmCorQ (k := k)) (X : Geometry.SmSchemeOver k) :
    SmCorQ.Hom category X X :=
  category.integral.composition.idQ X

/-- Composition in the bundled `SmCor_Q` category. -/
def comp (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y)
    (g : SmCorQ.Hom category Y Z) : SmCorQ.Hom category X Z :=
  category.integral.composition.compQ f g

@[simp] theorem id_eq_toRational_id (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k) :
    category.id X = FiniteCorrespondence.toRational (category.integral.id X) :=
  category.integral.composition.idQ_eq_toRational_id X

/-- Rational composition agrees with integral composition after extending
coefficients from `ℤ` to `ℚ`. -/
theorem comp_eq_toRational_comp (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y)
    (g : FiniteCorrespondence Y Z) :
    category.comp (FiniteCorrespondence.toRational f) (FiniteCorrespondence.toRational g) =
      FiniteCorrespondence.toRational (category.integral.comp f g) :=
  category.integral.composition.compQ_toRational f g

theorem zero_comp (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category Y Z) :
    category.comp (0 : SmCorQ.Hom category X Y) f = 0 :=
  FiniteCorrespondenceCompositionData.compQ_zero_left category.integral.composition f

theorem comp_zero (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp f (0 : SmCorQ.Hom category Y Z) = 0 :=
  FiniteCorrespondenceCompositionData.compQ_zero_right category.integral.composition f

theorem add_comp (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f g : SmCorQ.Hom category X Y)
    (h : SmCorQ.Hom category Y Z) :
    category.comp (f + g) h = category.comp f h + category.comp g h :=
  FiniteCorrespondenceCompositionData.compQ_add_left category.integral.composition f g h

theorem comp_add (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y)
    (g h : SmCorQ.Hom category Y Z) :
    category.comp f (g + h) = category.comp f g + category.comp f h :=
  FiniteCorrespondenceCompositionData.compQ_add_right category.integral.composition f g h

theorem smul_comp (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (f : SmCorQ.Hom category X Y)
    (g : SmCorQ.Hom category Y Z) :
    category.comp (coeff • f) g = coeff • category.comp f g :=
  FiniteCorrespondenceCompositionData.compQ_smul_left category.integral.composition coeff f g

theorem comp_smul (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (f : SmCorQ.Hom category X Y)
    (g : SmCorQ.Hom category Y Z) :
    category.comp f (coeff • g) = coeff • category.comp f g :=
  FiniteCorrespondenceCompositionData.compQ_smul_right category.integral.composition coeff f g

section ExternalProductQ

variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]

/-- Bilinear external product on rational finite correspondences. -/
def externalProduct
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    SmCorQ.Hom category (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  left.sum fun leftPrime leftCoeff =>
    right.sum fun rightPrime rightCoeff =>
      (leftCoeff * rightCoeff) •
        FiniteCorrespondence.toRational
          (FiniteCorrespondence.externalProduct (k := k)
            (Finsupp.single leftPrime (1 : ℤ))
            (Finsupp.single rightPrime (1 : ℤ)))

@[simp] theorem externalProduct_zero_left
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : SmCorQ.Hom category X2 Y2) :
    category.externalProduct (0 : SmCorQ.Hom category X1 Y1) right = 0 := by
  rw [SmCorQ.externalProduct]
  simp

@[simp] theorem externalProduct_zero_right
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X1 Y1) :
    category.externalProduct left (0 : SmCorQ.Hom category X2 Y2) = 0 := by
  rw [SmCorQ.externalProduct]
  simp

theorem externalProduct_add_left
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    category.externalProduct (left1 + left2) right =
      category.externalProduct left1 right + category.externalProduct left2 right := by
  classical
  rw [SmCorQ.externalProduct, SmCorQ.externalProduct, SmCorQ.externalProduct,
    Finsupp.sum_add_index'] <;>
    simp [add_mul, add_smul, zero_mul]

theorem externalProduct_add_right
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X1 Y1)
    (right1 right2 : SmCorQ.Hom category X2 Y2) :
    category.externalProduct left (right1 + right2) =
      category.externalProduct left right1 + category.externalProduct left right2 := by
  classical
  rw [SmCorQ.externalProduct, SmCorQ.externalProduct, SmCorQ.externalProduct, ← Finsupp.sum_add]
  congr
  ext leftPrime leftCoeff
  rw [Finsupp.sum_add_index'] <;> simp [mul_add, add_smul, zero_mul]

@[simp] theorem externalProduct_single_single
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℚ) :
    category.externalProduct (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) •
        FiniteCorrespondence.toRational
          (FiniteCorrespondence.externalProduct (k := k)
            (Finsupp.single leftPrime (1 : ℤ))
            (Finsupp.single rightPrime (1 : ℤ))) := by
  classical
  rw [SmCorQ.externalProduct]
  simp

theorem externalProduct_smul_left
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    category.externalProduct (coeff • left) right =
      coeff • category.externalProduct left right := by
  apply Finsupp.induction_linear left
  · rw [SmCorQ.externalProduct]
    simp
  · intro left₁ left₂ ihLeft₁ ihLeft₂
    rw [smul_add, SmCorQ.externalProduct_add_left, ihLeft₁, ihLeft₂,
      ← smul_add, SmCorQ.externalProduct_add_left]
  · intro leftPrime leftCoeff
    apply Finsupp.induction_linear right
    · rw [SmCorQ.externalProduct]
      simp
    · intro right₁ right₂ ihRight₁ ihRight₂
      rw [SmCorQ.externalProduct_add_right, SmCorQ.externalProduct_add_right,
        ihRight₁, ihRight₂, smul_add]
    · intro rightPrime rightCoeff
      calc
        category.externalProduct (coeff • Finsupp.single leftPrime leftCoeff)
            (Finsupp.single rightPrime rightCoeff)
            = category.externalProduct (Finsupp.single leftPrime (coeff * leftCoeff))
                (Finsupp.single rightPrime rightCoeff) := by
              simp
        _ = coeff • category.externalProduct (Finsupp.single leftPrime leftCoeff)
              (Finsupp.single rightPrime rightCoeff) := by
              rw [SmCorQ.externalProduct_single_single,
                SmCorQ.externalProduct_single_single]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

theorem externalProduct_smul_right
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    category.externalProduct left (coeff • right) =
      coeff • category.externalProduct left right := by
  apply Finsupp.induction_linear right
  · rw [SmCorQ.externalProduct]
    simp
  · intro right₁ right₂ ihRight₁ ihRight₂
    rw [smul_add, SmCorQ.externalProduct_add_right, ihRight₁, ihRight₂,
      ← smul_add, SmCorQ.externalProduct_add_right]
  · intro rightPrime rightCoeff
    apply Finsupp.induction_linear left
    · rw [SmCorQ.externalProduct]
      simp
    · intro left₁ left₂ ihLeft₁ ihLeft₂
      rw [SmCorQ.externalProduct_add_left, SmCorQ.externalProduct_add_left,
        ihLeft₁, ihLeft₂, smul_add]
    · intro leftPrime leftCoeff
      calc
        category.externalProduct (Finsupp.single leftPrime leftCoeff)
            (coeff • Finsupp.single rightPrime rightCoeff)
            = category.externalProduct (Finsupp.single leftPrime leftCoeff)
                (Finsupp.single rightPrime (coeff * rightCoeff)) := by
              simp
        _ = coeff • category.externalProduct (Finsupp.single leftPrime leftCoeff)
              (Finsupp.single rightPrime rightCoeff) := by
              rw [SmCorQ.externalProduct_single_single,
                SmCorQ.externalProduct_single_single]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- Rational external product agrees with integral external product after
coefficient extension from `ℤ` to `ℚ`. -/
theorem externalProduct_toRational
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    category.externalProduct
        (FiniteCorrespondence.toRational left)
        (FiniteCorrespondence.toRational right) =
      FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProduct (k := k) left right) := by
  classical
  apply Finsupp.induction_linear left
  · rw [SmCorQ.externalProduct]
    simp
  · intro left1 left2 ih1 ih2
    rw [FiniteCorrespondence.toRational_add, SmCorQ.externalProduct_add_left,
      FiniteCorrespondence.externalProduct_add_left, FiniteCorrespondence.toRational_add,
      ih1, ih2]
  · intro leftPrime leftCoeff
    apply Finsupp.induction_linear right
    · rw [SmCorQ.externalProduct]
      simp
    · intro right1 right2 ih1 ih2
      rw [FiniteCorrespondence.toRational_add, SmCorQ.externalProduct_add_right,
        FiniteCorrespondence.externalProduct_add_right, FiniteCorrespondence.toRational_add,
        ih1, ih2]
    · intro rightPrime rightCoeff
      calc
        category.externalProduct
            (FiniteCorrespondence.toRational (Finsupp.single leftPrime leftCoeff))
            (FiniteCorrespondence.toRational (Finsupp.single rightPrime rightCoeff))
            =
          category.externalProduct
            ((leftCoeff : ℚ) • Finsupp.single leftPrime (1 : ℚ))
            ((rightCoeff : ℚ) • Finsupp.single rightPrime (1 : ℚ)) := by
              rw [FiniteCorrespondence.toRational_single,
                FiniteCorrespondence.toRational_single]
              simp
        _ = ((leftCoeff : ℚ) * (rightCoeff : ℚ)) •
              category.externalProduct
                (Finsupp.single leftPrime (1 : ℚ))
                (Finsupp.single rightPrime (1 : ℚ)) := by
              rw [SmCorQ.externalProduct_smul_left, SmCorQ.externalProduct_smul_right]
              rw [smul_smul]
        _ = ((leftCoeff : ℚ) * (rightCoeff : ℚ)) •
              FiniteCorrespondence.toRational
                (FiniteCorrespondence.externalProduct (k := k)
                  (Finsupp.single leftPrime (1 : ℤ))
                  (Finsupp.single rightPrime (1 : ℤ))) := by
              have hOne :
                  category.externalProduct
                      (Finsupp.single leftPrime (1 : ℚ))
                      (Finsupp.single rightPrime (1 : ℚ)) =
                    FiniteCorrespondence.toRational
                      (FiniteCorrespondence.externalProduct (k := k)
                        (Finsupp.single leftPrime (1 : ℤ))
                        (Finsupp.single rightPrime (1 : ℤ))) := by
                rw [SmCorQ.externalProduct_single_single]
                simp
              exact congrArg
                (fun corr => ((leftCoeff : ℚ) * (rightCoeff : ℚ)) • corr)
                hOne
        _ = FiniteCorrespondence.toRational
              (FiniteCorrespondence.externalProduct (k := k)
                (Finsupp.single leftPrime leftCoeff)
                (Finsupp.single rightPrime rightCoeff)) := by
              ext prime
              simp [FiniteCorrespondence.externalProduct_single_single,
                FiniteCorrespondence.toRational_smul, FiniteCorrespondence.toRational_single,
                smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- Bifunctoriality core: rational external product interchanges with
composition in `SmCorQ`, assuming the prime-level interchange statement for the
underlying integral composition package. -/
theorem externalProduct_comp_interchange
    (category : SmCorQ (k := k))
    (hPrime :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
          FiniteCorrespondence.externalProduct (k := k)
              (FiniteCorrespondenceCompositionData.compPrime
                category.integral.composition f g)
              (FiniteCorrespondenceCompositionData.compPrime
                category.integral.composition f' g')
            =
              FiniteCorrespondenceCompositionData.comp category.integral.composition
                (FiniteCorrespondence.externalProduct (k := k)
                  (Finsupp.single f (1 : ℤ))
                  (Finsupp.single f' (1 : ℤ)))
                (FiniteCorrespondence.externalProduct (k := k)
                  (Finsupp.single g (1 : ℤ))
                  (Finsupp.single g' (1 : ℤ))))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W1 X1)
    (g : SmCorQ.Hom category X1 Y1)
    (f' : SmCorQ.Hom category W2 X2)
    (g' : SmCorQ.Hom category X2 Y2) :
    category.externalProduct (category.comp f g) (category.comp f' g')
      = category.comp (category.externalProduct f f')
          (category.externalProduct g g') := by
  apply Finsupp.induction_linear f
  · rw [category.zero_comp, SmCorQ.externalProduct_zero_left,
      SmCorQ.externalProduct_zero_left, category.zero_comp]
  · intro f1 f2 ih1 ih2
    rw [SmCorQ.add_comp, SmCorQ.externalProduct_add_left, ih1, ih2,
      SmCorQ.externalProduct_add_left, SmCorQ.add_comp]
  · intro fPrime fCoeff
    apply Finsupp.induction_linear g
    · rw [category.comp_zero, SmCorQ.externalProduct_zero_left,
        SmCorQ.externalProduct_zero_left, category.comp_zero]
    · intro g1 g2 ihg1 ihg2
      rw [SmCorQ.comp_add, SmCorQ.externalProduct_add_left, ihg1, ihg2,
        SmCorQ.externalProduct_add_left, SmCorQ.comp_add]
    · intro gPrime gCoeff
      apply Finsupp.induction_linear f'
      · rw [category.zero_comp, SmCorQ.externalProduct_zero_right,
          SmCorQ.externalProduct_zero_right, category.zero_comp]
      · intro f1' f2' ihf1' ihf2'
        rw [SmCorQ.add_comp, SmCorQ.externalProduct_add_right, ihf1', ihf2',
          SmCorQ.externalProduct_add_right, SmCorQ.add_comp]
      · intro fPrime' fCoeff'
        apply Finsupp.induction_linear g'
        · rw [category.comp_zero, SmCorQ.externalProduct_zero_right,
            SmCorQ.externalProduct_zero_right, category.comp_zero]
        · intro g1' g2' ihg1' ihg2'
          rw [SmCorQ.comp_add, SmCorQ.externalProduct_add_right, ihg1', ihg2',
            SmCorQ.externalProduct_add_right, SmCorQ.comp_add]
        · intro gPrime' gCoeff'
          let ff' : FiniteCorrespondence (overBaseProductObject W1 W2)
              (overBaseProductObject X1 X2) :=
            FiniteCorrespondence.externalProduct (k := k)
              (Finsupp.single fPrime (1 : ℤ))
              (Finsupp.single fPrime' (1 : ℤ))
          let gg' : FiniteCorrespondence (overBaseProductObject X1 X2)
              (overBaseProductObject Y1 Y2) :=
            FiniteCorrespondence.externalProduct (k := k)
              (Finsupp.single gPrime (1 : ℤ))
              (Finsupp.single gPrime' (1 : ℤ))
          let fg : FiniteCorrespondence W1 Y1 :=
            category.integral.composition.compPrime fPrime gPrime
          let f'g' : FiniteCorrespondence W2 Y2 :=
            category.integral.composition.compPrime fPrime' gPrime'
          have hRat := congrArg FiniteCorrespondence.toRational
            (hPrime fPrime gPrime fPrime' gPrime')
          have hLeft :
              category.externalProduct
                  (category.comp (Finsupp.single fPrime fCoeff)
                    (Finsupp.single gPrime gCoeff))
                  (category.comp (Finsupp.single fPrime' fCoeff')
                    (Finsupp.single gPrime' gCoeff'))
                = (fCoeff * gCoeff * (fCoeff' * gCoeff')) •
                    FiniteCorrespondence.toRational
                      (FiniteCorrespondence.externalProduct (k := k) fg f'g') := by
            have hNorm :
                category.externalProduct
                    ((fCoeff * gCoeff) • FiniteCorrespondence.toRational fg)
                    ((fCoeff' * gCoeff') • FiniteCorrespondence.toRational f'g') =
                (fCoeff * gCoeff * (fCoeff' * gCoeff')) •
                    FiniteCorrespondence.toRational
                      (FiniteCorrespondence.externalProduct (k := k) fg f'g') := by
              rw [SmCorQ.externalProduct_smul_left, SmCorQ.externalProduct_smul_right,
                SmCorQ.externalProduct_toRational]
              rw [smul_smul]
            have hCompRight :
                category.comp (Finsupp.single fPrime' fCoeff')
                    (Finsupp.single gPrime' gCoeff') =
                  (fCoeff' * gCoeff') • FiniteCorrespondence.toRational f'g' := by
              rw [SmCorQ.comp, FiniteCorrespondenceCompositionData.compQ_single_single]
            rw [SmCorQ.comp, FiniteCorrespondenceCompositionData.compQ_single_single, hCompRight]
            exact hNorm
          have hRight :
              category.comp
                  (category.externalProduct (Finsupp.single fPrime fCoeff)
                    (Finsupp.single fPrime' fCoeff'))
                  (category.externalProduct (Finsupp.single gPrime gCoeff)
                    (Finsupp.single gPrime' gCoeff'))
                = (fCoeff * fCoeff' * (gCoeff * gCoeff')) •
                    FiniteCorrespondence.toRational
                      (category.integral.composition.comp ff' gg') := by
            have hExtLeft :
                category.externalProduct (Finsupp.single fPrime fCoeff)
                    (Finsupp.single fPrime' fCoeff') =
                  (fCoeff * fCoeff') • FiniteCorrespondence.toRational ff' := by
              have hNorm :
                  category.externalProduct
                      (fCoeff • Finsupp.single fPrime (1 : ℚ))
                      (fCoeff' • Finsupp.single fPrime' (1 : ℚ)) =
                    (fCoeff * fCoeff') • FiniteCorrespondence.toRational ff' := by
                have hOne :
                    category.externalProduct
                        (Finsupp.single fPrime (1 : ℚ))
                        (Finsupp.single fPrime' (1 : ℚ)) =
                      FiniteCorrespondence.toRational ff' := by
                  simp [ff'] using
                    SmCorQ.externalProduct_toRational (category := category)
                      (Finsupp.single fPrime (1 : ℤ))
                      (Finsupp.single fPrime' (1 : ℤ))
                rw [SmCorQ.externalProduct_smul_left, SmCorQ.externalProduct_smul_right]
                rw [hOne]
                simp [smul_smul, mul_assoc]
              simp using hNorm
            have hExtRight :
                category.externalProduct (Finsupp.single gPrime gCoeff)
                    (Finsupp.single gPrime' gCoeff') =
                  (gCoeff * gCoeff') • FiniteCorrespondence.toRational gg' := by
              have hNorm :
                  category.externalProduct
                      (gCoeff • Finsupp.single gPrime (1 : ℚ))
                      (gCoeff' • Finsupp.single gPrime' (1 : ℚ)) =
                    (gCoeff * gCoeff') • FiniteCorrespondence.toRational gg' := by
                have hOne :
                    category.externalProduct
                        (Finsupp.single gPrime (1 : ℚ))
                        (Finsupp.single gPrime' (1 : ℚ)) =
                      FiniteCorrespondence.toRational gg' := by
                  simp [gg'] using
                    SmCorQ.externalProduct_toRational (category := category)
                      (Finsupp.single gPrime (1 : ℤ))
                      (Finsupp.single gPrime' (1 : ℤ))
                rw [SmCorQ.externalProduct_smul_left, SmCorQ.externalProduct_smul_right]
                rw [hOne]
                simp [smul_smul, mul_assoc]
              simp using hNorm
            calc
              category.comp
                  (category.externalProduct (Finsupp.single fPrime fCoeff)
                    (Finsupp.single fPrime' fCoeff'))
                  (category.externalProduct (Finsupp.single gPrime gCoeff)
                    (Finsupp.single gPrime' gCoeff'))
                  = category.comp
                      ((fCoeff * fCoeff') • FiniteCorrespondence.toRational ff')
                      ((gCoeff * gCoeff') • FiniteCorrespondence.toRational gg') := by
                        rw [hExtLeft, hExtRight]
              _ = (fCoeff * fCoeff' * (gCoeff * gCoeff')) •
                    category.comp (FiniteCorrespondence.toRational ff')
                      (FiniteCorrespondence.toRational gg') := by
                    rw [SmCorQ.smul_comp, SmCorQ.comp_smul]
                    rw [smul_smul]
              _ = (fCoeff * fCoeff' * (gCoeff * gCoeff')) •
                    FiniteCorrespondence.toRational
                      (category.integral.composition.comp ff' gg') := by
                    rw [SmCorQ.comp_eq_toRational_comp]
                    rfl
          have hCoeff :
              fCoeff * gCoeff * (fCoeff' * gCoeff') =
                fCoeff * fCoeff' * (gCoeff * gCoeff') := by
            calc
              fCoeff * gCoeff * (fCoeff' * gCoeff') =
                  fCoeff * (gCoeff * (fCoeff' * gCoeff')) := by rw [mul_assoc]
              _ = fCoeff * ((gCoeff * fCoeff') * gCoeff') := by
                    rw [← mul_assoc gCoeff fCoeff' gCoeff']
              _ = fCoeff * ((fCoeff' * gCoeff) * gCoeff') := by rw [mul_comm gCoeff fCoeff']
              _ = fCoeff * (fCoeff' * (gCoeff * gCoeff')) := by
                    rw [mul_assoc fCoeff' gCoeff gCoeff']
              _ = fCoeff * fCoeff' * (gCoeff * gCoeff') := by rw [← mul_assoc]
          calc
            category.externalProduct
                (category.comp (Finsupp.single fPrime fCoeff)
                  (Finsupp.single gPrime gCoeff))
                (category.comp (Finsupp.single fPrime' fCoeff')
                  (Finsupp.single gPrime' gCoeff'))
              = (fCoeff * gCoeff * (fCoeff' * gCoeff')) •
                  FiniteCorrespondence.toRational
                    (FiniteCorrespondence.externalProduct (k := k) fg f'g') := hLeft
            _ = (fCoeff * gCoeff * (fCoeff' * gCoeff')) •
                  FiniteCorrespondence.toRational
                    (category.integral.composition.comp ff' gg') := by
                  exact congrArg
                    (fun corr => (fCoeff * gCoeff * (fCoeff' * gCoeff')) • corr)
                    hRat
            _ = (fCoeff * fCoeff' * (gCoeff * gCoeff')) •
                  FiniteCorrespondence.toRational
                    (category.integral.composition.comp ff' gg') := by
                  rw [hCoeff]
            _ = category.comp
                  (category.externalProduct (Finsupp.single fPrime fCoeff)
                    (Finsupp.single fPrime' fCoeff'))
                  (category.externalProduct (Finsupp.single gPrime gCoeff)
                    (Finsupp.single gPrime' gCoeff')) := hRight.symm

end ExternalProductQ

/-- Owner-level alias for the right-ordered tensor rationalization comparison. -/
noncomputable def homTensorWithRatLinearEquiv (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k} := by
  letI : Module ℚ (TensorProduct ℤ (FiniteCorrespondence X Y) ℚ) :=
    instModuleRightTensorWithRat (X := X) (Y := Y)
  exact rightTensorWithRatLinearEquiv (X := X) (Y := Y)

@[simp] theorem homTensorWithRatLinearEquiv_tmul (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (corr : FiniteCorrespondence X Y) (q : ℚ) :
    homTensorWithRatLinearEquiv category (corr ⊗ₜ[ℤ] q) =
      q • toRational corr := by
  letI : Module ℚ (TensorProduct ℤ (FiniteCorrespondence X Y) ℚ) :=
    instModuleRightTensorWithRat (X := X) (Y := Y)
  exact
    rightTensorWithRatLinearEquiv_tmul (X := X) (Y := Y) corr q

@[simp] theorem id_eq_homTensorWithRatLinearEquiv_id_tmul_one
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k) :
    homTensorWithRatLinearEquiv category
        ((category.integral.id X) ⊗ₜ[ℤ] (1 : ℚ)) = category.id X := by
  rw [homTensorWithRatLinearEquiv_tmul, id_eq_toRational_id]
  simp using (one_smul ℚ (category.id X))

theorem comp_homTensorWithRatLinearEquiv_tmul_tmul
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y) (leftCoeff : ℚ)
    (right : FiniteCorrespondence Y Z) (rightCoeff : ℚ) :
    category.comp
        (homTensorWithRatLinearEquiv category (left ⊗ₜ[ℤ] leftCoeff))
        (homTensorWithRatLinearEquiv category (right ⊗ₜ[ℤ] rightCoeff)) =
      homTensorWithRatLinearEquiv category
        ((category.integral.comp left right) ⊗ₜ[ℤ] (leftCoeff * rightCoeff)) := by
  rw [homTensorWithRatLinearEquiv_tmul,
    homTensorWithRatLinearEquiv_tmul,
    smul_comp,
    comp_smul,
    comp_eq_toRational_comp,
    homTensorWithRatLinearEquiv_tmul]
  simp [smul_smul, mul_assoc]

private theorem id_comp_single_one (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) :
    category.comp (category.id X) (Finsupp.single prime (1 : ℚ)) =
      Finsupp.single prime (1 : ℚ) := by
  let f : FiniteCorrespondence X Y := Finsupp.single prime (1 : ℤ)
  calc
    category.comp (category.id X) (Finsupp.single prime (1 : ℚ))
        = category.comp (FiniteCorrespondence.toRational (category.integral.id X))
            (FiniteCorrespondence.toRational f) := by
              rw [category.id_eq_toRational_id]
              simp [f]
    _ = FiniteCorrespondence.toRational (category.integral.comp (category.integral.id X) f) :=
          category.comp_eq_toRational_comp (category.integral.id X) f
    _ = Finsupp.single prime (1 : ℚ) := by
          simp [f, category.integral.id_comp]

private theorem comp_id_single_one (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) :
    category.comp (Finsupp.single prime (1 : ℚ)) (category.id Y) =
      Finsupp.single prime (1 : ℚ) := by
  let f : FiniteCorrespondence X Y := Finsupp.single prime (1 : ℤ)
  calc
    category.comp (Finsupp.single prime (1 : ℚ)) (category.id Y)
        = category.comp (FiniteCorrespondence.toRational f)
            (FiniteCorrespondence.toRational (category.integral.id Y)) := by
              rw [category.id_eq_toRational_id]
              simp [f]
    _ = FiniteCorrespondence.toRational (category.integral.comp f (category.integral.id Y)) := by
          exact category.comp_eq_toRational_comp f (category.integral.id Y)
    _ = Finsupp.single prime (1 : ℚ) := by
          simp [f, category.integral.comp_id]

/-- Extend left singleton identity for rational correspondences by linearity. -/
private theorem id_comp_of_singleton_identities (category : SmCorQ (k := k))
    (id_comp_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℚ),
          category.comp (category.id X) (Finsupp.single prime coeff) =
            Finsupp.single prime coeff)
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp (category.id X) f = f := by
  apply Finsupp.induction_linear f
  · rw [category.comp_zero]
  · intro f₁ f₂ hf₁ hf₂
    rw [category.comp_add, hf₁, hf₂]
  · intro prime coeff
    exact id_comp_single prime coeff

/-- Extend right singleton identity for rational correspondences by linearity. -/
private theorem comp_id_of_singleton_identities (category : SmCorQ (k := k))
    (comp_id_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℚ),
          category.comp (Finsupp.single prime coeff) (category.id Y) =
            Finsupp.single prime coeff)
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp f (category.id Y) = f := by
  apply Finsupp.induction_linear f
  · rw [category.zero_comp]
  · intro f₁ f₂ hf₁ hf₂
    rw [category.add_comp, hf₁, hf₂]
  · intro prime coeff
    exact comp_id_single prime coeff

private theorem id_comp_single (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℚ) :
    category.comp (category.id X) (Finsupp.single prime coeff) =
      Finsupp.single prime coeff := by
  calc
    category.comp (category.id X) (Finsupp.single prime coeff)
        = category.comp (category.id X) (coeff • Finsupp.single prime (1 : ℚ)) := by
            simp
    _ = coeff • category.comp (category.id X) (Finsupp.single prime (1 : ℚ)) := by
          rw [category.comp_smul]
    _ = coeff • Finsupp.single prime (1 : ℚ) := by
          rw [id_comp_single_one]
    _ = Finsupp.single prime coeff := by
          simp

private theorem comp_id_single (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℚ) :
    category.comp (Finsupp.single prime coeff) (category.id Y) =
      Finsupp.single prime coeff := by
  calc
    category.comp (Finsupp.single prime coeff) (category.id Y)
        = category.comp (coeff • Finsupp.single prime (1 : ℚ)) (category.id Y) := by
            simp
    _ = coeff • category.comp (Finsupp.single prime (1 : ℚ)) (category.id Y) := by
          rw [category.smul_comp]
    _ = coeff • Finsupp.single prime (1 : ℚ) := by
          rw [comp_id_single_one]
    _ = Finsupp.single prime coeff := by
          simp

theorem id_comp (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp (category.id X) f = f :=
  id_comp_of_singleton_identities category (id_comp_single category) f

theorem comp_id (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp f (category.id Y) = f :=
  comp_id_of_singleton_identities category (comp_id_single category) f

private theorem assoc_single_one (category : SmCorQ (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : PrimeFiniteCorrespondenceGeom W X)
    (g : PrimeFiniteCorrespondenceGeom X Y)
    (h : PrimeFiniteCorrespondenceGeom Y Z) :
    category.comp (category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)))
      (Finsupp.single h (1 : ℚ)) =
        category.comp (Finsupp.single f (1 : ℚ))
          (category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
  let fZ : FiniteCorrespondence W X := Finsupp.single f (1 : ℤ)
  let gZ : FiniteCorrespondence X Y := Finsupp.single g (1 : ℤ)
  let hZ : FiniteCorrespondence Y Z := Finsupp.single h (1 : ℤ)
  have hfg : category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)) =
      FiniteCorrespondence.toRational (category.integral.comp fZ gZ) := by
    simpa [fZ, gZ] using category.comp_eq_toRational_comp fZ gZ
  have hgh : category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ)) =
      FiniteCorrespondence.toRational (category.integral.comp gZ hZ) := by
    simpa [gZ, hZ] using category.comp_eq_toRational_comp gZ hZ
  calc
    category.comp (category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)))
        (Finsupp.single h (1 : ℚ))
        = category.comp (FiniteCorrespondence.toRational (category.integral.comp fZ gZ))
            (FiniteCorrespondence.toRational hZ) := by
              simp [hfg, hZ]
    _ = FiniteCorrespondence.toRational
          (category.integral.comp (category.integral.comp fZ gZ) hZ) := by
            exact category.comp_eq_toRational_comp (category.integral.comp fZ gZ) hZ
    _ = FiniteCorrespondence.toRational
          (category.integral.comp fZ (category.integral.comp gZ hZ)) := by
            rw [category.integral.assoc]
    _ = category.comp (FiniteCorrespondence.toRational fZ)
          (FiniteCorrespondence.toRational (category.integral.comp gZ hZ)) := by
            symm
            exact category.comp_eq_toRational_comp fZ (category.integral.comp gZ hZ)
    _ = category.comp (Finsupp.single f (1 : ℚ))
          (category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
            simp [hgh, fZ]

private theorem assoc_single (category : SmCorQ (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℚ)
    (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℚ)
    (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℚ) :
    category.comp
      (category.comp (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
      (Finsupp.single h hCoeff) =
        category.comp (Finsupp.single f fCoeff)
          (category.comp (Finsupp.single g gCoeff) (Finsupp.single h hCoeff)) := by
  have hfg : category.comp (Finsupp.single f fCoeff) (Finsupp.single g gCoeff) =
      (fCoeff * gCoeff) • category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)) := by
    calc
      category.comp (Finsupp.single f fCoeff) (Finsupp.single g gCoeff)
          = category.comp (fCoeff • Finsupp.single f (1 : ℚ)) (gCoeff • Finsupp.single g (1 : ℚ)) := by
              simp
      _ = fCoeff • category.comp (Finsupp.single f (1 : ℚ)) (gCoeff • Finsupp.single g (1 : ℚ)) := by
            rw [category.smul_comp]
      _ = fCoeff • (gCoeff • category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ))) := by
            rw [category.comp_smul]
      _ = (fCoeff * gCoeff) • category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)) := by
            simp [smul_smul, mul_assoc]
  have hgh : category.comp (Finsupp.single g gCoeff) (Finsupp.single h hCoeff) =
      (gCoeff * hCoeff) • category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ)) := by
    calc
      category.comp (Finsupp.single g gCoeff) (Finsupp.single h hCoeff)
          = category.comp (gCoeff • Finsupp.single g (1 : ℚ)) (hCoeff • Finsupp.single h (1 : ℚ)) := by
              simp
      _ = gCoeff • category.comp (Finsupp.single g (1 : ℚ)) (hCoeff • Finsupp.single h (1 : ℚ)) := by
            rw [category.smul_comp]
      _ = gCoeff • (hCoeff • category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
            rw [category.comp_smul]
      _ = (gCoeff * hCoeff) • category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ)) := by
            simp [smul_smul, mul_assoc]
  calc
    category.comp
        (category.comp (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
        (Finsupp.single h hCoeff)
        = category.comp
            ((fCoeff * gCoeff) • category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)))
            (hCoeff • Finsupp.single h (1 : ℚ)) := by
              rw [hfg]
              simp
    _ = hCoeff • category.comp
          ((fCoeff * gCoeff) • category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)))
          (Finsupp.single h (1 : ℚ)) := by
            rw [category.comp_smul]
    _ = (fCoeff * gCoeff * hCoeff) •
          category.comp (category.comp (Finsupp.single f (1 : ℚ)) (Finsupp.single g (1 : ℚ)))
            (Finsupp.single h (1 : ℚ)) := by
              rw [category.smul_comp]
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = (fCoeff * gCoeff * hCoeff) •
          category.comp (Finsupp.single f (1 : ℚ))
            (category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
              rw [assoc_single_one]
    _ = fCoeff • category.comp (Finsupp.single f (1 : ℚ))
          ((gCoeff * hCoeff) • category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
            rw [category.comp_smul]
            simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = category.comp (fCoeff • Finsupp.single f (1 : ℚ))
          ((gCoeff * hCoeff) • category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
            rw [← category.smul_comp]
    _ = category.comp (Finsupp.single f fCoeff)
          (category.comp (Finsupp.single g gCoeff) (Finsupp.single h hCoeff)) := by
            rw [hgh]
            simp

/-- Extend singleton associativity for rational correspondences by trilinearity. -/
private theorem assoc_of_singleton_associativity (category : SmCorQ (k := k))
    (assoc_single :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℚ)
        (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℚ)
        (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℚ),
          category.comp
            (category.comp (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
            (Finsupp.single h hCoeff) =
              category.comp (Finsupp.single f fCoeff)
                (category.comp (Finsupp.single g gCoeff) (Finsupp.single h hCoeff)))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W X)
    (g : SmCorQ.Hom category X Y)
    (h : SmCorQ.Hom category Y Z) :
    category.comp (category.comp f g) h =
      category.comp f (category.comp g h) := by
  apply Finsupp.induction_linear f
  · rw [category.zero_comp, category.zero_comp, category.zero_comp]
  · intro f₁ f₂ hf₁ hf₂
    rw [category.add_comp,
      category.add_comp,
      category.add_comp,
      hf₁, hf₂]
  · intro fPrime fCoeff
    apply Finsupp.induction_linear g
    · rw [category.comp_zero, category.zero_comp, category.zero_comp, category.comp_zero]
    · intro g₁ g₂ hg₁ hg₂
      rw [category.comp_add,
        category.add_comp,
        category.add_comp,
        category.comp_add,
        hg₁, hg₂]
    · intro gPrime gCoeff
      apply Finsupp.induction_linear h
      · rw [category.comp_zero, category.comp_zero, category.comp_zero]
      · intro h₁ h₂ hh₁ hh₂
        rw [category.comp_add,
          category.comp_add,
          category.comp_add,
          hh₁, hh₂]
      · intro hPrime hCoeff
        exact assoc_single fPrime fCoeff gPrime gCoeff hPrime hCoeff

theorem assoc (category : SmCorQ (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W X)
    (g : SmCorQ.Hom category X Y)
    (h : SmCorQ.Hom category Y Z) :
    category.comp (category.comp f g) h =
      category.comp f (category.comp g h) :=
  assoc_of_singleton_associativity category (assoc_single category) f g h

def categoryStruct (category : SmCorQ (k := k)) :
    CategoryStruct.{u + 1} (Geometry.SmSchemeOver k) where
  Hom X Y := SmCorQ.Hom category X Y
  id := SmCorQ.id category
  comp := fun f g => SmCorQ.comp category f g

def toCategory (category : SmCorQ (k := k)) :
    Category.{u + 1} (Geometry.SmSchemeOver k) where
  Hom X Y := SmCorQ.Hom category X Y
  id := SmCorQ.id category
  comp := fun f g => SmCorQ.comp category f g
  id_comp := SmCorQ.id_comp category
  comp_id := SmCorQ.comp_id category
  assoc := SmCorQ.assoc category

end SmCorQ

/-- The category structure on smooth `k`-schemes induced by a chosen `SmCorQ`
package. -/
abbrev SmCorQCat (category : SmCorQ (k := k)) :
    Category.{u + 1} (Geometry.SmSchemeOver k) :=
  SmCorQ.toCategory category

set_option maxHeartbeats 800000 in
def SmCorQCat_preadditive (category : SmCorQ (k := k)) := by
  letI := SmCorQCat category
  exact
    { homGroup := fun X Y => by
        change AddCommGroup (SmCorQ.Hom category X Y)
        infer_instance
      add_comp := by
        intro X Y Z f g h
        change SmCorQ.Hom category X Y at f g
        change SmCorQ.Hom category Y Z at h
        change category.comp (f + g) h = category.comp f h + category.comp g h
        exact category.add_comp f g h
      comp_add := by
        intro X Y Z f g h
        change SmCorQ.Hom category X Y at f
        change SmCorQ.Hom category Y Z at g h
        change category.comp f (g + h) = category.comp f g + category.comp f h
        exact category.comp_add f g h :
      Preadditive (Geometry.SmSchemeOver k) }

set_option maxHeartbeats 800000 in
def SmCorQCat_linear (category : SmCorQ (k := k)) := by
  letI := SmCorQCat category
  letI := SmCorQCat_preadditive category
  exact
    { homModule := fun X Y => by
        change Module ℚ (SmCorQ.Hom category X Y)
        infer_instance
      smul_comp := by
        intro X Y Z r f g
        change SmCorQ.Hom category X Y at f
        change SmCorQ.Hom category Y Z at g
        change category.comp (r • f) g = r • category.comp f g
        exact category.smul_comp r f g
      comp_smul := by
        intro X Y Z f r g
        change SmCorQ.Hom category X Y at f
        change SmCorQ.Hom category Y Z at g
        change category.comp f (r • g) = r • category.comp f g
        exact category.comp_smul r f g :
      CategoryTheory.Linear ℚ (Geometry.SmSchemeOver k) }

set_option maxHeartbeats 800000 in
def SmCorQCat_op_preadditive (category : SmCorQ (k := k)) := by
  letI := SmCorQCat category
  letI := SmCorQCat_preadditive category
  exact (inferInstance : Preadditive (Geometry.SmSchemeOver k)ᵒᵖ)

set_option maxHeartbeats 800000 in
def SmCorQCat_op_linear (category : SmCorQ (k := k)) := by
  letI := SmCorQCat category
  letI := SmCorQCat_preadditive category
  letI := SmCorQCat_linear category
  letI := SmCorQCat_op_preadditive category
  exact
    { homModule := fun X Y => by
        letI := (opEquiv X Y).addCommMonoid
        exact (opEquiv X Y).module ℚ
      smul_comp := by
        intro X Y Z r f g
        apply Quiver.Hom.unop_inj
        change category.comp g.unop (r • f.unop) = r • category.comp g.unop f.unop
        exact category.comp_smul r g.unop f.unop
      comp_smul := by
        intro X Y Z f r g
        apply Quiver.Hom.unop_inj
        change category.comp (r • g.unop) f.unop = r • category.comp g.unop f.unop
        exact category.smul_comp r g.unop f.unop :
      CategoryTheory.Linear ℚ (Geometry.SmSchemeOver k)ᵒᵖ }

end

end Boundary
