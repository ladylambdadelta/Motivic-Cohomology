import Boundary.LFunctions.CohomologicalEulerFactor
import Boundary.LFunctions.EulerFactorLog

/-!
# Log-packaged formal Euler and zeta factors

This file introduces a minimal multiplicative packaging for formal factors.
The package records the logarithm as a power series.  Multiplication and inverse
are represented by addition and negation of logarithms, so the basic product
laws are immediate from the K₀ logarithm characters.

No exponential API is assumed here.
-/

open scoped PowerSeries

universe u v

namespace Boundary
namespace FormalEulerFactor

noncomputable section

variable (K : Type u) [Field K]

/-- A formal factor represented by its logarithm. -/
structure Factor where
  log : K⟦X⟧

namespace Factor

instance : One (Factor K) where
  one := ⟨0⟩

instance : Mul (Factor K) where
  mul A B := ⟨A.log + B.log⟩

instance : Inv (Factor K) where
  inv A := ⟨-A.log⟩

instance : Div (Factor K) where
  div A B := ⟨A.log - B.log⟩

@[simp]
theorem log_one : (1 : Factor K).log = 0 :=
  rfl

@[simp]
theorem log_mul (A B : Factor K) : (A * B).log = A.log + B.log :=
  rfl

@[simp]
theorem log_inv (A : Factor K) : A⁻¹.log = -A.log :=
  rfl

@[simp]
theorem log_div (A B : Factor K) : (A / B).log = A.log - B.log :=
  rfl

@[ext]
theorem ext {A B : Factor K} (h : A.log = B.log) : A = B := by
  cases A
  cases B
  simp at h
  simp [h]

@[simp]
theorem mul_one (A : Factor K) : A * 1 = A := by
  ext
  simp

@[simp]
theorem one_mul (A : Factor K) : 1 * A = A := by
  ext
  simp

@[simp]
theorem mul_inv (A : Factor K) : A * A⁻¹ = 1 := by
  ext
  simp

@[simp]
theorem inv_mul (A : Factor K) : A⁻¹ * A = 1 := by
  ext
  simp

theorem mul_assoc (A B C : Factor K) : (A * B) * C = A * (B * C) := by
  ext
  simp [add_assoc]

theorem mul_comm (A B : Factor K) : A * B = B * A := by
  ext
  simp [add_comm]

theorem div_eq_mul_inv (A B : Factor K) : A / B = A * B⁻¹ := by
  ext
  simp [sub_eq_add_neg]

end Factor

/-- The log-packaged determinant Euler factor attached to a K₀ class. -/
def eulerFactorLogClass (x : Boundary.EndomorphismK0.K0.{u, v} K) : Factor K :=
  ⟨Boundary.EulerFactorLog.eulerLog K x⟩

/-- The log-packaged reciprocal local zeta factor attached to a K₀ class. -/
def zetaFactorLogClass (x : Boundary.EndomorphismK0.K0.{u, v} K) : Factor K :=
  ⟨Boundary.EulerFactorLog.zetaLog K x⟩

@[simp]
theorem eulerFactorLogClass_log (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    (eulerFactorLogClass K x).log = Boundary.EulerFactorLog.eulerLog K x :=
  rfl

@[simp]
theorem zetaFactorLogClass_log (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    (zetaFactorLogClass K x).log = Boundary.EulerFactorLog.zetaLog K x :=
  rfl

@[simp]
theorem eulerFactorLogClass_zero :
    eulerFactorLogClass K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 1 := by
  ext
  simp [eulerFactorLogClass]

theorem eulerFactorLogClass_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (x + y) =
      eulerFactorLogClass K x * eulerFactorLogClass K y := by
  ext
  simp [eulerFactorLogClass, Boundary.EulerFactorLog.eulerLog_add]

@[simp]
theorem eulerFactorLogClass_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (-x) = (eulerFactorLogClass K x)⁻¹ := by
  ext
  simp [eulerFactorLogClass]

theorem eulerFactorLogClass_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (x - y) =
      eulerFactorLogClass K x / eulerFactorLogClass K y := by
  ext
  simp [eulerFactorLogClass, Boundary.EulerFactorLog.eulerLog_sub]

@[simp]
theorem zetaFactorLogClass_zero :
    zetaFactorLogClass K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 1 := by
  ext
  simp [zetaFactorLogClass]

theorem zetaFactorLogClass_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (x + y) =
      zetaFactorLogClass K x * zetaFactorLogClass K y := by
  ext
  simp [zetaFactorLogClass, Boundary.EulerFactorLog.zetaLog_add]

@[simp]
theorem zetaFactorLogClass_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (-x) = (zetaFactorLogClass K x)⁻¹ := by
  ext
  simp [zetaFactorLogClass]

theorem zetaFactorLogClass_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (x - y) =
      zetaFactorLogClass K x / zetaFactorLogClass K y := by
  ext
  simp [zetaFactorLogClass, Boundary.EulerFactorLog.zetaLog_sub]

namespace Cohomological

variable {K}
variable {V : ℤ → Type v}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, FiniteDimensional K (V i)]

/-- The log-packaged determinant Euler factor of a cohomological family. -/
def cohomologicalEulerFactor
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) : Factor K :=
  eulerFactorLogClass K
    (Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
      (V := V) degrees F)

/-- The log-packaged reciprocal local zeta factor of a cohomological family. -/
def cohomologicalZetaFactor
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) : Factor K :=
  zetaFactorLogClass K
    (Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
      (V := V) degrees F)

theorem cohomologicalEulerFactor_log_eq_localZetaFormalLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (cohomologicalEulerFactor (K := K) (V := V) degrees F).log =
      Boundary.CohomologicalEulerFactor.localZetaFormalLog (V := V) degrees F := by
  rw [cohomologicalEulerFactor, eulerFactorLogClass_log]
  rw [Boundary.CohomologicalEulerFactor.localZetaFormalLog_eq_eulerLog]

theorem cohomologicalZetaFactor_log_eq_reciprocalLocalZetaFormalLog
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (cohomologicalZetaFactor (K := K) (V := V) degrees F).log =
      Boundary.CohomologicalEulerFactor.reciprocalLocalZetaFormalLog
        (V := V) degrees F := by
  rfl

theorem cohomologicalEulerFactor_class_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (x + y) =
      eulerFactorLogClass K x * eulerFactorLogClass K y :=
  eulerFactorLogClass_add K x y

theorem cohomologicalZetaFactor_class_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (x + y) =
      zetaFactorLogClass K x * zetaFactorLogClass K y :=
  zetaFactorLogClass_add K x y

end Cohomological

end

end FormalEulerFactor
end Boundary
