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

omit [Field K] in
@[ext]
theorem ext {A B : Factor K} (h : A.log = B.log) : A = B :=
  match A, B with
  | ⟨_⟩, ⟨_⟩ => congrArg Factor.mk h

@[simp]
theorem mul_one (A : Factor K) : A * 1 = A :=
  Factor.ext (K := K) (add_zero A.log)

@[simp]
theorem one_mul (A : Factor K) : 1 * A = A :=
  Factor.ext (K := K) (zero_add A.log)

@[simp]
theorem mul_inv (A : Factor K) : A * A⁻¹ = 1 :=
  Factor.ext (K := K) (add_neg_cancel A.log)

@[simp]
theorem inv_mul (A : Factor K) : A⁻¹ * A = 1 :=
  Factor.ext (K := K) (neg_add_cancel A.log)

theorem mul_assoc (A B C : Factor K) : (A * B) * C = A * (B * C) :=
  Factor.ext (K := K) (add_assoc A.log B.log C.log)

theorem mul_comm (A B : Factor K) : A * B = B * A :=
  Factor.ext (K := K) (add_comm A.log B.log)

theorem div_eq_mul_inv (A B : Factor K) : A / B = A * B⁻¹ :=
  Factor.ext (K := K) (sub_eq_add_neg A.log B.log)

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
    eulerFactorLogClass K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 1 :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.eulerLog_zero K)

theorem eulerFactorLogClass_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (x + y) =
      eulerFactorLogClass K x * eulerFactorLogClass K y :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.eulerLog_add K x y)

@[simp]
theorem eulerFactorLogClass_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (-x) = (eulerFactorLogClass K x)⁻¹ :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.eulerLog_neg K x)

theorem eulerFactorLogClass_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    eulerFactorLogClass K (x - y) =
      eulerFactorLogClass K x / eulerFactorLogClass K y :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.eulerLog_sub K x y)

@[simp]
theorem zetaFactorLogClass_zero :
    zetaFactorLogClass K (0 : Boundary.EndomorphismK0.K0.{u, v} K) = 1 :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.zetaLog_zero K)

theorem zetaFactorLogClass_add
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (x + y) =
      zetaFactorLogClass K x * zetaFactorLogClass K y :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.zetaLog_add K x y)

@[simp]
theorem zetaFactorLogClass_neg
    (x : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (-x) = (zetaFactorLogClass K x)⁻¹ :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.zetaLog_neg K x)

theorem zetaFactorLogClass_sub
    (x y : Boundary.EndomorphismK0.K0.{u, v} K) :
    zetaFactorLogClass K (x - y) =
      zetaFactorLogClass K x / zetaFactorLogClass K y :=
  Factor.ext (K := K) (Boundary.EulerFactorLog.zetaLog_sub K x y)

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

theorem cohomologicalEulerFactor_log_eq_eulerLog
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (cohomologicalEulerFactor (K := K) (V := V) degrees F).log =
      Boundary.EulerFactorLog.eulerLog K
        (Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
          (V := V) degrees F) :=
  Eq.refl
    (Boundary.EulerFactorLog.eulerLog K
      (Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
        (V := V) degrees F))

theorem cohomologicalZetaFactor_log_eq_zetaLog
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (cohomologicalZetaFactor (K := K) (V := V) degrees F).log =
      Boundary.EulerFactorLog.zetaLog K
        (Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
          (V := V) degrees F) :=
  Eq.refl
    (Boundary.EulerFactorLog.zetaLog K
      (Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
        (V := V) degrees F))

theorem cohomologicalEulerFactor_log_eq_localZetaFormalLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (cohomologicalEulerFactor (K := K) (V := V) degrees F).log =
      Boundary.CohomologicalEulerFactor.localZetaFormalLog (V := V) degrees F :=
  (Boundary.CohomologicalEulerFactor.localZetaFormalLog_eq_eulerLog
    (V := V) degrees F).symm

theorem cohomologicalZetaFactor_log_eq_reciprocalLocalZetaFormalLog
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (cohomologicalZetaFactor (K := K) (V := V) degrees F).log =
      Boundary.CohomologicalEulerFactor.reciprocalLocalZetaFormalLog
        (V := V) degrees F :=
  Eq.refl
    (Boundary.CohomologicalEulerFactor.reciprocalLocalZetaFormalLog
      (V := V) degrees F)

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
