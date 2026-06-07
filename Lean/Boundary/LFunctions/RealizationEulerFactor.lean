import Boundary.LFunctions.FormalEulerFactor

/-!
# Realization-facing Euler factors

This file is the first boundary from realized cohomology into the L-function
core.  It does not construct a global realization functor.  It proves that a
bounded finite-dimensional cohomology family equipped with degreewise
endomorphisms has a canonical virtual endomorphism class, hence determinant
Euler and reciprocal zeta factors.
-/

open scoped PowerSeries

universe u v w

namespace Boundary
namespace RealizationEulerFactor

noncomputable section

variable (K : Type u) [Field K]

/-- A finite cohomological package with a degreewise endomorphism.

This is the exact input the L-function core needs from a realization: a finite
set of cohomological degrees, finite-dimensional vector spaces in those
degrees, and a linear endomorphism in each degree. -/
structure FrobeniusCohomologyPackage where
  degrees : Finset ℤ
  object : ℤ → Boundary.EndomorphismK0.EndomorphismObject.{u, v} K

namespace FrobeniusCohomologyPackage

variable {K}

/-- The cohomology vector space in degree `i`. -/
def cohomology (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) : Type v :=
  (P.object i).carrier

instance cohomology.addCommGroup (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) :
    AddCommGroup (P.cohomology i) :=
  (P.object i).addCommGroup

instance cohomology.module (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) :
    Module K (P.cohomology i) :=
  (P.object i).module

instance cohomology.finiteDimensional (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) :
    FiniteDimensional K (P.cohomology i) :=
  (P.object i).finiteDimensional

/-- The degreewise endomorphism supplied by the package. -/
def frobenius (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) :
    Module.End K (P.cohomology i) :=
  (P.object i).endomorphism

/-- The virtual endomorphism class attached to a finite Frobenius cohomology
package. -/
def k0Class (P : FrobeniusCohomologyPackage.{u, v} K) :
    Boundary.EndomorphismK0.K0.{u, v} K :=
  ∑ i in P.degrees.filter (fun i => Odd i),
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) -
    ∑ i in P.degrees.filter (fun i => Even i),
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i))

/-- Extend a package to a larger finite support by putting zero cohomology
outside the original support. -/
def extendSupport (P : FrobeniusCohomologyPackage.{u, v} K)
    (S : Finset ℤ) (_hP : P.degrees ⊆ S) :
    FrobeniusCohomologyPackage.{u, v} K where
  degrees := S
  object := fun i => if i ∈ P.degrees then P.object i else Boundary.EndomorphismK0.zeroObject K

/-- Extending support by zero objects does not change the K₀ class. -/
theorem k0Class_extendSupport
    (P : FrobeniusCohomologyPackage.{u, v} K)
    (S : Finset ℤ) (hP : P.degrees ⊆ S) :
    (P.extendSupport S hP).k0Class = P.k0Class := by
  classical
  have hOdd : P.degrees.filter (fun i => Odd i) ⊆ S.filter (fun i => Odd i) := by
    intro i hi
    exact Finset.mem_filter.2
      ⟨hP (Finset.mem_of_mem_filter i hi), (Finset.mem_filter.1 hi).2⟩
  have hEven : P.degrees.filter (fun i => Even i) ⊆ S.filter (fun i => Even i) := by
    intro i hi
    exact Finset.mem_filter.2
      ⟨hP (Finset.mem_of_mem_filter i hi), (Finset.mem_filter.1 hi).2⟩
  rw [k0Class, k0Class]
  congr 1
  · calc
      (∑ i in S.filter (fun i => Odd i),
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (if i ∈ P.degrees then P.object i else Boundary.EndomorphismK0.zeroObject K))) =
          ∑ i in P.degrees.filter (fun i => Odd i),
            Boundary.EndomorphismK0.mk K
              (Boundary.EndomorphismK0.of K
                (if i ∈ P.degrees then P.object i else Boundary.EndomorphismK0.zeroObject K)) := by
            symm
            rw [Finset.sum_subset hOdd]
            intro i hiS hiP
            have hi_not : i ∉ P.degrees := by
              intro h
              exact hiP (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hiS).2⟩)
            simp [hi_not]
        _ = ∑ i in P.degrees.filter (fun i => Odd i),
            Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [(Finset.mem_filter.1 hi).1]
  · calc
      (∑ i in S.filter (fun i => Even i),
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (if i ∈ P.degrees then P.object i else Boundary.EndomorphismK0.zeroObject K))) =
          ∑ i in P.degrees.filter (fun i => Even i),
            Boundary.EndomorphismK0.mk K
              (Boundary.EndomorphismK0.of K
                (if i ∈ P.degrees then P.object i else Boundary.EndomorphismK0.zeroObject K)) := by
            symm
            rw [Finset.sum_subset hEven]
            intro i hiS hiP
            have hi_not : i ∉ P.degrees := by
              intro h
              exact hiP (Finset.mem_filter.2 ⟨h, (Finset.mem_filter.1 hiS).2⟩)
            simp [hi_not]
        _ = ∑ i in P.degrees.filter (fun i => Even i),
            Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [(Finset.mem_filter.1 hi).1]

/-- Canonical direct sum of two packages, formed on the union of their finite
supports after zero-extension. -/
def directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    FrobeniusCohomologyPackage.{u, v} K where
  degrees := P.degrees ∪ Q.degrees
  object := fun i =>
    Boundary.EndomorphismK0.EndomorphismObject.product
      ((P.extendSupport (P.degrees ∪ Q.degrees)
        (by intro j hj; exact Finset.mem_union_left Q.degrees hj)).object i)
      ((Q.extendSupport (P.degrees ∪ Q.degrees)
        (by intro j hj; exact Finset.mem_union_right P.degrees hj)).object i)

/-- Translate a finite subset of integers by `n`. -/
def shiftInt (S : Finset ℤ) (n : ℤ) : Finset ℤ :=
  S.image (fun i => i + n)

/-- Membership in a translated finite set. -/
theorem mem_shiftInt_iff (S : Finset ℤ) (n d : ℤ) :
    d ∈ shiftInt S n ↔ d - n ∈ S := by
  classical
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨i, hi, rfl⟩
    have hcancel : i + n - n = i := by
      rw [add_sub_cancel_right]
    simpa [hcancel] using hi
  · intro hd
    refine Finset.mem_image.mpr ?_
    refine ⟨d - n, hd, ?_⟩
    rw [sub_add_cancel]

/-- Membership in a unit shift. -/
theorem mem_shiftInt_one_iff (S : Finset ℤ) (d : ℤ) :
    d ∈ shiftInt S 1 ↔ d - 1 ∈ S := by
  exact mem_shiftInt_iff S 1 d

/-- Reindex a sum over a translated finite set by shifting the function. -/
theorem sum_shiftInt_one {M : Type*} [AddCommMonoid M]
    (S : Finset ℤ) (f : ℤ → M) :
    ∑ d in shiftInt S 1, f d = ∑ d in S, f (d + 1) := by
  classical
  rw [shiftInt]
  rw [Finset.sum_image]
  · intro a ha b hb h
    exact add_right_cancel h

/-- The K₀ class of the canonical package direct sum is the sum of the K₀
classes. -/
theorem k0Class_directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).k0Class = P.k0Class + Q.k0Class := by
  classical
  let S : Finset ℤ := P.degrees ∪ Q.degrees
  let P' := P.extendSupport S (by intro j hj; exact Finset.mem_union_left Q.degrees hj)
  let Q' := Q.extendSupport S (by intro j hj; exact Finset.mem_union_right P.degrees hj)
  have hterm :
      ∀ i,
        Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (Boundary.EndomorphismK0.EndomorphismObject.product (P'.object i) (Q'.object i))) =
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P'.object i)) +
            Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (Q'.object i)) := by
    intro i
    exact Boundary.EndomorphismK0.mk_directSum_eq_add K (P'.object i) (Q'.object i)
  have hP' : P'.k0Class = P.k0Class := k0Class_extendSupport P S
    (by intro j hj; exact Finset.mem_union_left Q.degrees hj)
  have hQ' : Q'.k0Class = Q.k0Class := k0Class_extendSupport Q S
    (by intro j hj; exact Finset.mem_union_right P.degrees hj)
  calc
    (P.directSum Q).k0Class =
        P'.k0Class + Q'.k0Class := by
          simp [directSum, extendSupport, P', Q', k0Class,
            Boundary.EndomorphismK0.mk_directSum_eq_add, Finset.sum_add_distrib]
          abel_nf
    _ = P.k0Class + Q.k0Class := by
          rw [hP', hQ']

/-- A package whose degreewise endomorphism objects come from a cohomological
family has the same virtual class as the cohomological package built from that
family. -/
theorem k0Class_eq_cohomologicalEndomorphismClass
    (P : FrobeniusCohomologyPackage.{u, v} K)
    {V : ℤ → Type w}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, Module.End K (V i))
    (hobj : ∀ i, P.object i =
      Boundary.CohomologicalEulerFactor.endomorphismObject (V := V) F i) :
    P.k0Class =
      Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
        (V := V) P.degrees F := by
  classical
  rw [k0Class, Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hobj i]
  simp [Boundary.CohomologicalEulerFactor.endomorphismObject]

/-- The package Euler factor agrees with the cohomological Euler factor when
the package is built from a cohomological family. -/
theorem eulerFactor_eq_cohomologicalEulerFactor
    (P : FrobeniusCohomologyPackage.{u, v} K)
    {V : ℤ → Type w}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, Module.End K (V i))
    (hobj : ∀ i, P.object i =
      Boundary.CohomologicalEulerFactor.endomorphismObject (V := V) F i) :
    P.eulerFactor = Boundary.FormalEulerFactor.Cohomological.cohomologicalEulerFactor
      (K := K) (V := V) P.degrees F := by
  apply Boundary.FormalEulerFactor.Factor.ext
  rw [eulerFactor_log, Boundary.FormalEulerFactor.Cohomological.cohomologicalEulerFactor_log_eq_localZetaFormalLog]
  rw [k0Class_eq_cohomologicalEndomorphismClass P F hobj]

/-- The package reciprocal zeta factor agrees with the cohomological reciprocal
zeta factor when the package is built from a cohomological family. -/
theorem zetaFactor_eq_cohomologicalZetaFactor
    (P : FrobeniusCohomologyPackage.{u, v} K)
    {V : ℤ → Type w}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, Module.End K (V i))
    (hobj : ∀ i, P.object i =
      Boundary.CohomologicalEulerFactor.endomorphismObject (V := V) F i) :
    P.zetaFactor = Boundary.FormalEulerFactor.Cohomological.cohomologicalZetaFactor
      (K := K) (V := V) P.degrees F := by
  apply Boundary.FormalEulerFactor.Factor.ext
  rw [zetaFactor_log, Boundary.FormalEulerFactor.Cohomological.cohomologicalZetaFactor_log_eq_reciprocalLocalZetaFormalLog]
  rw [k0Class_eq_cohomologicalEndomorphismClass P F hobj]

/-- The sign attached to a cohomological degree for the alternating
K₀-class. -/
def degreeSign (i : ℤ) : ℤ :=
  if Even i then 1 else -1

/-- A one-step shift flips the degree sign. -/
theorem degreeSign_add_one (i : ℤ) :
    degreeSign (i + 1) = - degreeSign i := by
  unfold degreeSign
  by_cases h : Even i <;> simp [h, Int.even_add_one]

/-- The package K₀ class as a single signed finite sum. -/
theorem k0Class_eq_signed_sum (P : FrobeniusCohomologyPackage.{u, v} K) :
    P.k0Class =
      -∑ i in P.degrees, degreeSign i •
        Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) := by
  classical
  let x : ℤ → Boundary.EndomorphismK0.K0.{u, v} K := fun i =>
    Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i))
  have hsum :
      ∑ i in P.degrees, degreeSign i • x i =
        ∑ i in P.degrees.filter (fun i => Even i), x i -
          ∑ i in P.degrees.filter (fun i => Odd i), x i := by
    have hsplit :
        ∑ i in P.degrees, degreeSign i • x i =
          ∑ i in P.degrees.filter (fun i => Even i), degreeSign i • x i +
            ∑ i in P.degrees.filter (fun i => Odd i), degreeSign i • x i := by
      simpa [Finset.sum_filter, add_comm, add_left_comm, add_assoc] using
        (Finset.sum_filter_add_sum_filter_not (s := P.degrees) (p := fun i => Even i)
          (f := fun i => degreeSign i • x i)).symm
    have hEven :
        ∑ i in P.degrees.filter (fun i => Even i), degreeSign i • x i =
          ∑ i in P.degrees.filter (fun i => Even i), x i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : Even i := (Finset.mem_filter.1 hi).2
      simp [degreeSign, hi']
    have hOdd :
        ∑ i in P.degrees.filter (fun i => Odd i), degreeSign i • x i =
          -∑ i in P.degrees.filter (fun i => Odd i), x i := by
      calc
        ∑ i in P.degrees.filter (fun i => Odd i), degreeSign i • x i =
            ∑ i in P.degrees.filter (fun i => Odd i), (-1 : ℤ) • x i := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi' : Odd i := (Finset.mem_filter.1 hi).2
              have hne : ¬ Even i := by
                simpa [Int.not_even_iff_odd] using hi'
              simp [degreeSign, hne]
        _ = -∑ i in P.degrees.filter (fun i => Odd i), x i := by
              simp
    rw [hsplit, hEven, hOdd]
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  rw [k0Class, hsum]
  rw [neg_sub]

/-- Shift a package by one cohomological degree, extending by zero outside the
shifted support. -/
def shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    FrobeniusCohomologyPackage.{u, v} K where
  degrees := shiftInt P.degrees 1
  object := fun i =>
    if h : i - 1 ∈ P.degrees then P.object (i - 1)
    else Boundary.EndomorphismK0.zeroObject K

/-- Shifting a package by one negates its K₀ class. -/
theorem k0Class_shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    (P.shiftOne).k0Class = - P.k0Class := by
  classical
  have hsum :=
    sum_shiftInt_one (S := P.degrees)
      (f := fun i =>
        degreeSign i •
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (if h : i - 1 ∈ P.degrees then P.object (i - 1)
              else Boundary.EndomorphismK0.zeroObject K)))
  have hRHS :
      ∑ i in P.degrees,
          degreeSign i •
            Boundary.EndomorphismK0.mk K
              (Boundary.EndomorphismK0.of K
                (if h : i ∈ P.degrees then P.object i
                else Boundary.EndomorphismK0.zeroObject K)) =
        ∑ i in P.degrees, degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  have hmid :
      -∑ i in shiftInt P.degrees 1,
        degreeSign i •
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (if h : i - 1 ∈ P.degrees then P.object (i - 1)
              else Boundary.EndomorphismK0.zeroObject K)) =
      ∑ i in P.degrees,
        degreeSign i •
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (if h : i ∈ P.degrees then P.object i
              else Boundary.EndomorphismK0.zeroObject K)) := by
    simpa [degreeSign_add_one, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      Int.even_add_one] using congrArg Neg.neg hsum
  calc
    (P.shiftOne).k0Class =
        -∑ i in shiftInt P.degrees 1,
          degreeSign i •
            Boundary.EndomorphismK0.mk K
              (Boundary.EndomorphismK0.of K
              (if h : i - 1 ∈ P.degrees then P.object (i - 1)
                else Boundary.EndomorphismK0.zeroObject K)) := by
          simp [k0Class_eq_signed_sum, shiftOne]
    _ =
        ∑ i in P.degrees, degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) := by
          exact hmid.trans hRHS
    _ = - P.k0Class := by
          rw [k0Class_eq_signed_sum]
          simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]


/-- The determinant Euler factor of a finite Frobenius cohomology package,
represented by its logarithm. -/
def eulerFactor (P : FrobeniusCohomologyPackage.{u, v} K) :
    Boundary.FormalEulerFactor.Factor K :=
  Boundary.FormalEulerFactor.eulerFactorLogClass K P.k0Class

/-- The reciprocal zeta factor of a finite Frobenius cohomology package,
represented by its logarithm. -/
def zetaFactor (P : FrobeniusCohomologyPackage.{u, v} K) :
    Boundary.FormalEulerFactor.Factor K :=
  Boundary.FormalEulerFactor.zetaFactorLogClass K P.k0Class

/-- The determinant Euler factor logarithm is the K₀ Euler logarithm of the
package class. -/
@[simp]
theorem eulerFactor_log (P : FrobeniusCohomologyPackage.{u, v} K) :
    P.eulerFactor.log = Boundary.EulerFactorLog.eulerLog K P.k0Class :=
  rfl

/-- The reciprocal zeta factor logarithm is the K₀ zeta logarithm of the
package class. -/
@[simp]
theorem zetaFactor_log (P : FrobeniusCohomologyPackage.{u, v} K) :
    P.zetaFactor.log = Boundary.EulerFactorLog.zetaLog K P.k0Class :=
  rfl

/-- Shifting a package by one inverts its Euler factor. -/
theorem eulerFactor_shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    eulerFactor (K := K) (P.shiftOne) = (eulerFactor (K := K) P)⁻¹ := by
  apply Boundary.FormalEulerFactor.Factor.ext
  simp [eulerFactor, k0Class_shiftOne, Boundary.EulerFactorLog.eulerLog_neg]

/-- Shifting a package by one inverts its reciprocal zeta factor. -/
theorem zetaFactor_shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    zetaFactor (K := K) (P.shiftOne) = (zetaFactor (K := K) P)⁻¹ := by
  apply Boundary.FormalEulerFactor.Factor.ext
  simp [zetaFactor, k0Class_shiftOne, Boundary.EulerFactorLog.zetaLog_neg]

/-- Euler factors multiply under canonical package direct sum. -/
theorem eulerFactor_directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).eulerFactor = P.eulerFactor * Q.eulerFactor := by
  apply Boundary.FormalEulerFactor.Factor.ext
  simp [eulerFactor, k0Class_directSum, Boundary.EulerFactorLog.eulerLog_add]

/-- Reciprocal zeta factors multiply under canonical package direct sum. -/
theorem zetaFactor_directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).zetaFactor = P.zetaFactor * Q.zetaFactor := by
  apply Boundary.FormalEulerFactor.Factor.ext
  simp [zetaFactor, k0Class_directSum, Boundary.EulerFactorLog.zetaLog_add]

/-- Positive coefficients of the package Euler logarithm are the normalized
negative trace-power character of its K₀ class. -/
theorem coeff_eulerFactor_log [CharZero K]
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.eulerFactor.log =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n P.k0Class) / (n : K) := by
  rw [eulerFactor_log]
  exact Boundary.EulerFactorLog.coeff_eulerLog K P.k0Class n hn

/-- Positive coefficients of the package reciprocal zeta logarithm are the
normalized positive trace-power character of its K₀ class. -/
theorem coeff_zetaFactor_log
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.zetaFactor.log =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n P.k0Class) / (n : K) := by
  rw [zetaFactor_log]
  exact Boundary.EulerFactorLog.coeff_zetaLog K P.k0Class n hn

/-- The concrete alternating trace-power formula for coefficients of the
package Euler logarithm. -/
theorem coeff_eulerFactor_log_eq_alternating_trace [CharZero K]
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.eulerFactor.log =
      -(((∑ i in P.degrees.filter (fun i => Odd i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) / (n : K)) := by
  rw [coeff_eulerFactor_log P n hn]
  rw [Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0]
  simp [k0Class, cohomology, frobenius, Boundary.EndomorphismK0.EndomorphismObject.tracePower]
  rw [neg_sub, neg_div]

/-- The concrete alternating trace-power formula for coefficients of the
package reciprocal zeta logarithm. -/
theorem coeff_zetaFactor_log_eq_alternating_trace
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.zetaFactor.log =
      ((∑ i in P.degrees.filter (fun i => Odd i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) / (n : K) := by
  rw [coeff_zetaFactor_log P n hn]
  rw [Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0]
  simp [k0Class, cohomology, frobenius, Boundary.EndomorphismK0.EndomorphismObject.tracePower]

end FrobeniusCohomologyPackage

end

end RealizationEulerFactor
end Boundary
