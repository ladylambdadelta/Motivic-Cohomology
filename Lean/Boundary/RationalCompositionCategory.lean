import Boundary.CorrespondenceRationalization
import Boundary.CompositionCategory
import Mathlib.CategoryTheory.Preadditive.Basic

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
  simp [FiniteCorrespondenceCompositionData.compQ]

@[simp] theorem compQ_zero_right (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : RationalFiniteCorrespondence X Y) :
    data.compQ left (0 : RationalFiniteCorrespondence Y Z) = 0 := by
  simp [FiniteCorrespondenceCompositionData.compQ]

@[simp] theorem compQ_add_left (data : FiniteCorrespondenceCompositionData (k := k))
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

@[simp] theorem compQ_add_right (data : FiniteCorrespondenceCompositionData (k := k))
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

@[simp] theorem compQ_smul_left (data : FiniteCorrespondenceCompositionData (k := k))
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
    simp [FiniteCorrespondenceCompositionData.compQ]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro rightPrime _
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem compQ_smul_right (data : FiniteCorrespondenceCompositionData (k := k))
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
    simp [FiniteCorrespondenceCompositionData.compQ]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro leftPrime _
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem compQ_single_single (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X Y)
    (rightPrime : PrimeFiniteCorrespondenceGeom Y Z)
    (leftCoeff rightCoeff : ℚ) :
    data.compQ (Finsupp.single leftPrime leftCoeff)
      (Finsupp.single rightPrime rightCoeff) =
        (leftCoeff * rightCoeff) • FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime) := by
  classical
  simp [FiniteCorrespondenceCompositionData.compQ]

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
                  simp [FiniteCorrespondence.toRational_smul]
        _ = ((leftCoeff : ℚ) * (rightCoeff : ℚ)) •
              data.compQ (Finsupp.single leftPrime (1 : ℚ))
                (Finsupp.single rightPrime (1 : ℚ)) := by
                  rw [FiniteCorrespondenceCompositionData.compQ_smul_left,
                    FiniteCorrespondenceCompositionData.compQ_smul_right]
                  simp [smul_smul, mul_assoc]
        _ = ((leftCoeff : ℚ) * (rightCoeff : ℚ)) •
              FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime) := by
                rw [FiniteCorrespondenceCompositionData.compQ_single_single]
                simp [smul_smul, mul_assoc]
        _ = (((leftCoeff * rightCoeff : ℤ) : ℚ)) •
              FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime) := by
                simpa using congrArg
                  (fun coeff : ℚ => coeff • FiniteCorrespondence.toRational (data.compPrime leftPrime rightPrime))
                  (Int.cast_mul leftCoeff rightCoeff).symm
        _ = FiniteCorrespondence.toRational
              ((leftCoeff * rightCoeff) • data.compPrime leftPrime rightPrime) := by
                ext prime
                simp [FiniteCorrespondence.toRational_smul]
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
  simpa [homTensorWithRatLinearEquiv] using
    rightTensorWithRatLinearEquiv_tmul (X := X) (Y := Y) corr q

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

@[simp] theorem id_eq_homTensorWithRatLinearEquiv_id_tmul_one
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k) :
    homTensorWithRatLinearEquiv category
        ((category.integral.id X) ⊗ₜ[ℤ] (1 : ℚ)) = category.id X := by
  rw [homTensorWithRatLinearEquiv_tmul, id_eq_toRational_id]
  simpa using (one_smul ℚ (category.id X))

@[simp] theorem comp_homTensorWithRatLinearEquiv_tmul_tmul
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
          simpa [SmCor.comp] using category.comp_eq_toRational_comp f (category.integral.id Y)
    _ = Finsupp.single prime (1 : ℚ) := by
          simp [f, category.integral.comp_id]

theorem id_comp (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp (category.id X) f = f := by
  apply Finsupp.induction_linear f
  · simp [SmCorQ.comp]
  · intro f₁ f₂ hf₁ hf₂
    rw [category.comp_add, hf₁, hf₂]
  · intro prime coeff
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

theorem comp_id (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y) :
    category.comp f (category.id Y) = f := by
  apply Finsupp.induction_linear f
  · simp [SmCorQ.comp]
  · intro f₁ f₂ hf₁ hf₂
    rw [category.add_comp, hf₁, hf₂]
  · intro prime coeff
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
              simpa [hfg, hZ]
    _ = FiniteCorrespondence.toRational
          (category.integral.comp (category.integral.comp fZ gZ) hZ) := by
            simpa [SmCorQ.comp, SmCor.comp] using
              (category.comp_eq_toRational_comp (category.integral.comp fZ gZ) hZ)
    _ = FiniteCorrespondence.toRational
          (category.integral.comp fZ (category.integral.comp gZ hZ)) := by
            rw [category.integral.assoc]
    _ = category.comp (FiniteCorrespondence.toRational fZ)
          (FiniteCorrespondence.toRational (category.integral.comp gZ hZ)) := by
            symm
            simpa [SmCorQ.comp, SmCor.comp] using
              (category.comp_eq_toRational_comp fZ (category.integral.comp gZ hZ))
    _ = category.comp (Finsupp.single f (1 : ℚ))
          (category.comp (Finsupp.single g (1 : ℚ)) (Finsupp.single h (1 : ℚ))) := by
            simpa [hgh, fZ]

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

theorem assoc (category : SmCorQ (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W X)
    (g : SmCorQ.Hom category X Y)
    (h : SmCorQ.Hom category Y Z) :
    category.comp (category.comp f g) h =
      category.comp f (category.comp g h) := by
  apply Finsupp.induction_linear f
  · simp [SmCorQ.comp]
  · intro f₁ f₂ hf₁ hf₂
    rw [category.add_comp,
      category.add_comp,
      category.add_comp,
      hf₁, hf₂]
  · intro fPrime fCoeff
    apply Finsupp.induction_linear g
    · simp [SmCorQ.comp]
    · intro g₁ g₂ hg₁ hg₂
      rw [category.comp_add,
        category.add_comp,
        category.add_comp,
        category.comp_add,
        hg₁, hg₂]
    · intro gPrime gCoeff
      apply Finsupp.induction_linear h
      · simp [SmCorQ.comp]
      · intro h₁ h₂ hh₁ hh₂
        rw [category.comp_add,
          category.comp_add,
          category.comp_add,
          hh₁, hh₂]
      · intro hPrime hCoeff
        exact assoc_single category fPrime fCoeff gPrime gCoeff hPrime hCoeff

def categoryStruct (category : SmCorQ (k := k)) : CategoryStruct (Geometry.SmSchemeOver k) where
  Hom X Y := SmCorQ.Hom category X Y
  id := SmCorQ.id category
  comp := fun f g => SmCorQ.comp category f g

def toCategory (category : SmCorQ (k := k)) : Category (Geometry.SmSchemeOver k) where
  Hom X Y := SmCorQ.Hom category X Y
  id := SmCorQ.id category
  comp := fun f g => SmCorQ.comp category f g
  id_comp := SmCorQ.id_comp category
  comp_id := SmCorQ.comp_id category
  assoc := SmCorQ.assoc category

end SmCorQ

/-- The category structure on smooth `k`-schemes induced by a chosen `SmCorQ`
package. -/
abbrev SmCorQCat (category : SmCorQ (k := k)) : Category (Geometry.SmSchemeOver k) :=
  SmCorQ.toCategory category

end

end Boundary
