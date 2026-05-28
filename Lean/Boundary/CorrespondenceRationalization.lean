import Boundary.CorrespondenceSums

/-!
# Correspondence Rationalization Comparison

This file isolates the tensor-rationalization comparison for finite
correspondences, leaving `Boundary.CorrespondenceSums` as the stable
coefficient owner.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

namespace FiniteCorrespondence

/-- Left-ordered rationalization comparison for finite correspondences.

This is the concrete normal form of tensoring `FiniteCorrespondence X Y` over
`ℤ` with `ℚ` when the rational coefficient ring is placed on the left. -/
noncomputable def leftTensorWithRatLinearEquiv
    {X Y : Geometry.SmSchemeOver k} :
    TensorProduct ℤ ℚ (FiniteCorrespondence X Y) ≃ₗ[ℚ]
      RationalFiniteCorrespondence X Y := by
  classical
  let e : TensorProduct ℤ ℚ (FiniteCorrespondence X Y) ≃ₗ[ℤ]
      RationalFiniteCorrespondence X Y := by
    simpa [FiniteCorrespondence, RationalFiniteCorrespondence] using
      (TensorProduct.finsuppScalarRight ℤ ℚ (PrimeFiniteCorrespondenceGeom X Y))
  refine
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun q tensor =>
        tensor.induction_on
          (by simp)
          (fun q' corr => by
            ext prime
            change
              ((TensorProduct.finsuppScalarRight ℤ ℚ (PrimeFiniteCorrespondenceGeom X Y))
                ((q • q') ⊗ₜ[ℤ] corr)) prime =
                (q •
                  (TensorProduct.finsuppScalarRight ℤ ℚ (PrimeFiniteCorrespondenceGeom X Y)
                    (q' ⊗ₜ[ℤ] corr))) prime
            simp [TensorProduct.finsuppScalarRight_apply_tmul_apply, smul_eq_mul,
              mul_assoc, mul_left_comm, mul_comm])
          (fun left right ihLeft ihRight => by
            simpa [smul_add, map_add] using
              congrArg₂ (fun a b => a + b) ihLeft ihRight) }

@[simp] theorem leftTensorWithRatLinearEquiv_tmul
    {X Y : Geometry.SmSchemeOver k}
    (q : ℚ) (corr : FiniteCorrespondence X Y) :
    leftTensorWithRatLinearEquiv (X := X) (Y := Y) (q ⊗ₜ[ℤ] corr) =
      q • toRational corr := by
  classical
  ext prime
  simp [leftTensorWithRatLinearEquiv, toRational, toRationalLinearMap,
    smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

/-- Tensor commutation identifies the right-ordered tensor with the left-ordered
tensor before applying the rationalization comparison. -/
noncomputable def tensorRatComm
    {X Y : Geometry.SmSchemeOver k} :
    TensorProduct ℤ (FiniteCorrespondence X Y) ℚ ≃ₗ[ℤ]
      TensorProduct ℤ ℚ (FiniteCorrespondence X Y) :=
  TensorProduct.comm ℤ (FiniteCorrespondence X Y) ℚ

/-- The visible right-ordered tensor product inherits its `ℚ`-module structure
by transporting the standard left-ordered structure across `TensorProduct.comm`.
-/
private noncomputable def ratRightMulLinear (q : ℚ) : ℚ →ₗ[ℤ] ℚ :=
  (q • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)).restrictScalars ℤ

@[simp] private theorem ratRightMulLinear_apply (q q' : ℚ) :
    ratRightMulLinear q q' = q * q' := by
  simp [ratRightMulLinear, mul_comm, mul_left_comm, mul_assoc]

private noncomputable def rightTensorSmulLinear
    {X Y : Geometry.SmSchemeOver k} (q : ℚ) :
    TensorProduct ℤ (FiniteCorrespondence X Y) ℚ →ₗ[ℤ]
      TensorProduct ℤ (FiniteCorrespondence X Y) ℚ :=
  TensorProduct.map (LinearMap.id) (ratRightMulLinear q)

@[simp] private theorem rightTensorSmulLinear_tmul
    {X Y : Geometry.SmSchemeOver k}
    (q q' : ℚ) (corr : FiniteCorrespondence X Y) :
    rightTensorSmulLinear (X := X) (Y := Y) q (corr ⊗ₜ[ℤ] q') =
      corr ⊗ₜ[ℤ] (q * q') := by
  simp [rightTensorSmulLinear]

noncomputable instance instSMulRightTensorWithRat
    {X Y : Geometry.SmSchemeOver k} :
    SMul ℚ (TensorProduct ℤ (FiniteCorrespondence X Y) ℚ) :=
  ⟨fun q tensor => rightTensorSmulLinear (X := X) (Y := Y) q tensor⟩

@[simp] theorem tensorRatComm_tmul
    {X Y : Geometry.SmSchemeOver k}
    (corr : FiniteCorrespondence X Y) (q : ℚ) :
    tensorRatComm (X := X) (Y := Y) (corr ⊗ₜ[ℤ] q) = q ⊗ₜ[ℤ] corr := by
  rfl

@[simp] theorem tensorRatComm_smul
    {X Y : Geometry.SmSchemeOver k}
    (q : ℚ)
    (tensor : TensorProduct ℤ (FiniteCorrespondence X Y) ℚ) :
    tensorRatComm (X := X) (Y := Y) (q • tensor) =
      q • tensorRatComm (X := X) (Y := Y) tensor := by
  refine TensorProduct.induction_on tensor ?_ ?_ ?_
  · change tensorRatComm (X := X) (Y := Y)
        (rightTensorSmulLinear (X := X) (Y := Y) q 0) =
      q • tensorRatComm (X := X) (Y := Y) 0
    simp [rightTensorSmulLinear]
  · intro corr q'
    calc
      tensorRatComm (X := X) (Y := Y) (q • (corr ⊗ₜ[ℤ] q'))
          = tensorRatComm (X := X) (Y := Y) (corr ⊗ₜ[ℤ] (q * q')) := by
              change tensorRatComm (X := X) (Y := Y)
                  (rightTensorSmulLinear (X := X) (Y := Y) q (corr ⊗ₜ[ℤ] q')) = _
              simp [rightTensorSmulLinear_tmul]
      _ = (q * q') ⊗ₜ[ℤ] corr := by
            simp [tensorRatComm_tmul]
      _ = q • tensorRatComm (X := X) (Y := Y) (corr ⊗ₜ[ℤ] q') := by
            simp [tensorRatComm_tmul, TensorProduct.smul_tmul', smul_eq_mul,
              mul_assoc, mul_left_comm, mul_comm]
  · intro left right ihLeft ihRight
    calc
      tensorRatComm (X := X) (Y := Y) (q • (left + right))
          = tensorRatComm (X := X) (Y := Y) (q • left) +
              tensorRatComm (X := X) (Y := Y) (q • right) := by
                change tensorRatComm (X := X) (Y := Y)
                    (rightTensorSmulLinear (X := X) (Y := Y) q (left + right)) =
                  tensorRatComm (X := X) (Y := Y) (q • left) +
                    tensorRatComm (X := X) (Y := Y) (q • right)
                calc
                  tensorRatComm (X := X) (Y := Y)
                      (rightTensorSmulLinear (X := X) (Y := Y) q (left + right))
                      = tensorRatComm (X := X) (Y := Y)
                          (rightTensorSmulLinear (X := X) (Y := Y) q left) +
                        tensorRatComm (X := X) (Y := Y)
                          (rightTensorSmulLinear (X := X) (Y := Y) q right) := by
                            simp [rightTensorSmulLinear]
                  _ = tensorRatComm (X := X) (Y := Y) (q • left) +
                        tensorRatComm (X := X) (Y := Y) (q • right) := by
                          rfl
      _ = q • tensorRatComm (X := X) (Y := Y) left +
            q • tensorRatComm (X := X) (Y := Y) right := by
          simpa using congrArg₂ (fun a b => a + b) ihLeft ihRight
      _ = q • tensorRatComm (X := X) (Y := Y) (left + right) := by
            simp [smul_add]

noncomputable instance instModuleRightTensorWithRat
    {X Y : Geometry.SmSchemeOver k} :
    Module ℚ (TensorProduct ℤ (FiniteCorrespondence X Y) ℚ) := by
  letI : SMul ℚ (TensorProduct ℤ (FiniteCorrespondence X Y) ℚ) :=
    instSMulRightTensorWithRat (X := X) (Y := Y)
  exact Function.Injective.module ℚ
    ((tensorRatComm (X := X) (Y := Y)).toLinearMap.toAddMonoidHom)
    (tensorRatComm (X := X) (Y := Y)).injective
    (fun q tensor => tensorRatComm_smul (X := X) (Y := Y) q tensor)

@[simp] theorem smul_tmul_rightTensorWithRat
    {X Y : Geometry.SmSchemeOver k}
    (q q' : ℚ) (corr : FiniteCorrespondence X Y) :
    q • (corr ⊗ₜ[ℤ] q') = corr ⊗ₜ[ℤ] (q * q') := by
  apply (tensorRatComm (X := X) (Y := Y)).injective
  rw [tensorRatComm_smul]
  simp [TensorProduct.smul_tmul', smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Right-ordered rationalization comparison for finite correspondences.

This is the user-facing comparison between the visible tensor product
`FiniteCorrespondence X Y ⊗[ℤ] ℚ` and rational finite correspondences. -/
noncomputable def rightTensorWithRatLinearEquiv
    {X Y : Geometry.SmSchemeOver k} :
    TensorProduct ℤ (FiniteCorrespondence X Y) ℚ ≃ₗ[ℚ]
      RationalFiniteCorrespondence X Y := by
  classical
  refine
    { toFun := fun tensor =>
        leftTensorWithRatLinearEquiv (X := X) (Y := Y)
          (tensorRatComm (X := X) (Y := Y) tensor)
      invFun := fun corr =>
        (tensorRatComm (X := X) (Y := Y)).symm
          ((leftTensorWithRatLinearEquiv (X := X) (Y := Y)).symm corr)
      left_inv := by
        intro tensor
        simp
      right_inv := by
        intro corr
        simp
      map_add' := by
        intro left right
        simp
      map_smul' := by
        intro q tensor
        change leftTensorWithRatLinearEquiv (X := X) (Y := Y)
            (tensorRatComm (X := X) (Y := Y) (q • tensor)) =
          q • leftTensorWithRatLinearEquiv (X := X) (Y := Y)
            (tensorRatComm (X := X) (Y := Y) tensor)
        rw [tensorRatComm_smul]
        simp }

@[simp] theorem rightTensorWithRatLinearEquiv_tmul
    {X Y : Geometry.SmSchemeOver k}
    (corr : FiniteCorrespondence X Y) (q : ℚ) :
    rightTensorWithRatLinearEquiv (X := X) (Y := Y) (corr ⊗ₜ[ℤ] q) =
      q • toRational corr := by
  simp [rightTensorWithRatLinearEquiv]

@[simp] theorem rightTensorWithRatLinearEquiv_symm_toRational
    {X Y : Geometry.SmSchemeOver k}
    (corr : FiniteCorrespondence X Y) :
    (rightTensorWithRatLinearEquiv (X := X) (Y := Y)).symm (toRational corr) =
      corr ⊗ₜ[ℤ] (1 : ℚ) := by
  apply (rightTensorWithRatLinearEquiv (X := X) (Y := Y)).injective
  simp

end FiniteCorrespondence

end

end Boundary
