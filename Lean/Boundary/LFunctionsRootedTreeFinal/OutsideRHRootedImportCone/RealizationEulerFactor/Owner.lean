import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.FormalEulerFactor.Owner

/-!
# Realization-facing Euler factors

This file is the first boundary from realized cohomology into the L-function
core.  It does not construct a global realization functor.  It proves that a
bounded finite-dimensional cohomology family equipped with degreewise
endomorphisms has a canonical virtual endomorphism class, hence determinant
Euler and reciprocal zeta factors.
-/

open scoped PowerSeries

universe u v

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

theorem mk_extendSupport_object_of_mem
    (P : FrobeniusCohomologyPackage.{u, v} K)
    (S : Finset ℤ) (hP : P.degrees ⊆ S) (i : ℤ) (hi : i ∈ P.degrees) :
    Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K ((P.extendSupport S hP).object i)) =
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) :=
  congrArg
    (fun A : Boundary.EndomorphismK0.EndomorphismObject K =>
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A))
    (if_pos hi)

theorem mk_extendSupport_object_of_not_mem
    (P : FrobeniusCohomologyPackage.{u, v} K)
    (S : Finset ℤ) (hP : P.degrees ⊆ S) (i : ℤ) (hi : i ∉ P.degrees) :
    Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K ((P.extendSupport S hP).object i)) =
      0 :=
  Eq.trans
    (congrArg
      (fun A : Boundary.EndomorphismK0.EndomorphismObject K =>
        Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A))
      (if_neg hi))
    (Boundary.EndomorphismK0.mk_zeroObject K)

theorem filter_subset_filter_of_subset {p : ℤ → Prop} [DecidablePred p]
    {A B : Finset ℤ} (hAB : A ⊆ B) :
    A.filter p ⊆ B.filter p :=
  fun i hi =>
    Finset.mem_filter.2
      ⟨hAB (Finset.mem_of_mem_filter i hi), (Finset.mem_filter.1 hi).2⟩

theorem extendSupport_filtered_sum_eq
    (P : FrobeniusCohomologyPackage.{u, v} K)
    (S : Finset ℤ) (hP : P.degrees ⊆ S)
    (p : ℤ → Prop) [DecidablePred p] :
    (∑ i in S.filter p,
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K ((P.extendSupport S hP).object i))) =
      ∑ i in P.degrees.filter p,
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K (P.object i)) :=
  Eq.trans
    (Finset.sum_subset (filter_subset_filter_of_subset hP)
      (fun i hiS hiP =>
        mk_extendSupport_object_of_not_mem P S hP i
          (fun hi => hiP (Finset.mem_filter.2 ⟨hi, (Finset.mem_filter.1 hiS).2⟩)))).symm
    (Finset.sum_congr (Eq.refl (P.degrees.filter p))
      (fun i hi =>
        mk_extendSupport_object_of_mem P S hP i (Finset.mem_of_mem_filter i hi)))

/-- Extending support by zero objects does not change the K₀ class. -/
theorem k0Class_extendSupport
    (P : FrobeniusCohomologyPackage.{u, v} K)
    (S : Finset ℤ) (hP : P.degrees ⊆ S) :
    (P.extendSupport S hP).k0Class = P.k0Class :=
  congrArg₂ Sub.sub
    (extendSupport_filtered_sum_eq P S hP (fun i => Odd i))
    (extendSupport_filtered_sum_eq P S hP (fun i => Even i))

theorem left_degrees_subset_union (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    P.degrees ⊆ P.degrees ∪ Q.degrees :=
  fun _ hj => Finset.mem_union_left Q.degrees hj

theorem right_degrees_subset_union (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    Q.degrees ⊆ P.degrees ∪ Q.degrees :=
  fun _ hj => Finset.mem_union_right P.degrees hj

/-- Canonical direct sum of two packages, formed on the union of their finite
supports after zero-extension. -/
def directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    FrobeniusCohomologyPackage.{u, v} K where
  degrees := P.degrees ∪ Q.degrees
  object := fun i =>
    Boundary.EndomorphismK0.EndomorphismObject.product
      ((P.extendSupport (P.degrees ∪ Q.degrees)
        (left_degrees_subset_union P Q)).object i)
      ((Q.extendSupport (P.degrees ∪ Q.degrees)
        (right_degrees_subset_union P Q)).object i)

/-- Translate a finite subset of integers by `n`. -/
def shiftInt (S : Finset ℤ) (n : ℤ) : Finset ℤ :=
  S.image (fun i => i + n)

/-- Membership in a translated finite set. -/
theorem mem_shiftInt_iff (S : Finset ℤ) (n d : ℤ) :
    d ∈ shiftInt S n ↔ d - n ∈ S :=
  Iff.intro
    (fun hd =>
      match Finset.mem_image.mp hd with
      | ⟨i, hi, hdi⟩ =>
          let hdn : d - n = i :=
            Eq.trans (congrArg (fun x : ℤ => x - n) hdi).symm
              (add_sub_cancel_right i n)
          Eq.subst hdn.symm hi)
    (fun hd =>
      Finset.mem_image.mpr
        ⟨d - n, hd, sub_add_cancel d n⟩)

/-- Membership in a unit shift. -/
theorem mem_shiftInt_one_iff (S : Finset ℤ) (d : ℤ) :
    d ∈ shiftInt S 1 ↔ d - 1 ∈ S :=
  mem_shiftInt_iff S 1 d

/-- Reindex a sum over a translated finite set by shifting the function. -/
theorem sum_shiftInt_one {M : Type*} [AddCommMonoid M]
    (S : Finset ℤ) (f : ℤ → M) :
    ∑ d in shiftInt S 1, f d = ∑ d in S, f (d + 1) :=
  Finset.sum_image
    (fun _ _ _ _ h => add_right_cancel h)

theorem add_sub_add_eq_sub_add_sub {G : Type*} [AddCommGroup G]
    (a b c d : G) :
    (a + b) - (c + d) = (a - c) + (b - d) :=
  add_sub_add_comm a b c d

theorem directSum_product_filtered_sum_eq_add
    (P Q : FrobeniusCohomologyPackage.{u, v} K)
    (p : ℤ → Prop) [DecidablePred p] :
    (∑ i in (P.degrees ∪ Q.degrees).filter p,
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K
          (Boundary.EndomorphismK0.EndomorphismObject.product
            ((P.extendSupport (P.degrees ∪ Q.degrees)
              (left_degrees_subset_union P Q)).object i)
            ((Q.extendSupport (P.degrees ∪ Q.degrees)
              (right_degrees_subset_union P Q)).object i)))) =
      (∑ i in (P.degrees ∪ Q.degrees).filter p,
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K
            ((P.extendSupport (P.degrees ∪ Q.degrees)
              (left_degrees_subset_union P Q)).object i))) +
        ∑ i in (P.degrees ∪ Q.degrees).filter p,
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              ((Q.extendSupport (P.degrees ∪ Q.degrees)
                (right_degrees_subset_union P Q)).object i)) :=
  Eq.trans
    (Finset.sum_congr (Eq.refl ((P.degrees ∪ Q.degrees).filter p))
      (fun i _ =>
        Boundary.EndomorphismK0.mk_directSum_eq_add K
          ((P.extendSupport (P.degrees ∪ Q.degrees)
            (left_degrees_subset_union P Q)).object i)
          ((Q.extendSupport (P.degrees ∪ Q.degrees)
            (right_degrees_subset_union P Q)).object i)))
    (Finset.sum_add_distrib)

theorem k0Class_directSum_extended
    (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).k0Class =
      (P.extendSupport (P.degrees ∪ Q.degrees)
        (left_degrees_subset_union P Q)).k0Class +
        (Q.extendSupport (P.degrees ∪ Q.degrees)
          (right_degrees_subset_union P Q)).k0Class :=
  Eq.trans
    (congrArg₂ Sub.sub
      (directSum_product_filtered_sum_eq_add P Q (fun i => Odd i))
      (directSum_product_filtered_sum_eq_add P Q (fun i => Even i)))
    (add_sub_add_eq_sub_add_sub
      (∑ i in (P.degrees ∪ Q.degrees).filter (fun i => Odd i),
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K
            ((P.extendSupport (P.degrees ∪ Q.degrees)
              (left_degrees_subset_union P Q)).object i)))
      (∑ i in (P.degrees ∪ Q.degrees).filter (fun i => Odd i),
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K
            ((Q.extendSupport (P.degrees ∪ Q.degrees)
              (right_degrees_subset_union P Q)).object i)))
      (∑ i in (P.degrees ∪ Q.degrees).filter (fun i => Even i),
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K
            ((P.extendSupport (P.degrees ∪ Q.degrees)
              (left_degrees_subset_union P Q)).object i)))
      (∑ i in (P.degrees ∪ Q.degrees).filter (fun i => Even i),
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K
            ((Q.extendSupport (P.degrees ∪ Q.degrees)
              (right_degrees_subset_union P Q)).object i))))

/-- The K₀ class of the canonical package direct sum is the sum of the K₀
classes. -/
theorem k0Class_directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).k0Class = P.k0Class + Q.k0Class :=
  Eq.trans
    (k0Class_directSum_extended P Q)
    (congrArg₂ HAdd.hAdd
      (k0Class_extendSupport P (P.degrees ∪ Q.degrees)
        (left_degrees_subset_union P Q))
      (k0Class_extendSupport Q (P.degrees ∪ Q.degrees)
        (right_degrees_subset_union P Q)))

/-- A package whose degreewise endomorphism objects come from a cohomological
family has the same virtual class as the cohomological package built from that
family. -/
theorem k0Class_eq_cohomologicalEndomorphismClass
    (P : FrobeniusCohomologyPackage.{u, v} K)
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, Module.End K (V i))
    (hobj : ∀ i, P.object i =
      Boundary.CohomologicalEulerFactor.endomorphismObject (V := V) F i) :
    P.k0Class =
      Boundary.CohomologicalEulerFactor.cohomologicalEndomorphismClass
        (V := V) P.degrees F :=
  congrArg₂ Sub.sub
    (Finset.sum_congr (Eq.refl (P.degrees.filter (fun i => Odd i)))
      (fun i _ =>
        congrArg
          (fun A : Boundary.EndomorphismK0.EndomorphismObject K =>
            Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A))
          (hobj i)))
    (Finset.sum_congr (Eq.refl (P.degrees.filter (fun i => Even i)))
      (fun i _ =>
        congrArg
          (fun A : Boundary.EndomorphismK0.EndomorphismObject K =>
            Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A))
          (hobj i)))

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

/-- The package Euler factor agrees with the cohomological Euler factor when
the package is built from a cohomological family. -/
theorem eulerFactor_eq_cohomologicalEulerFactor
    (P : FrobeniusCohomologyPackage.{u, v} K)
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, Module.End K (V i))
    (hobj : ∀ i, P.object i =
      Boundary.CohomologicalEulerFactor.endomorphismObject (V := V) F i) :
    P.eulerFactor = Boundary.FormalEulerFactor.Cohomological.cohomologicalEulerFactor
      (K := K) (V := V) P.degrees F :=
  Boundary.FormalEulerFactor.Factor.ext (K := K)
    (Eq.trans
      (eulerFactor_log P)
      (Eq.trans
        (congrArg (Boundary.EulerFactorLog.eulerLog K)
          (k0Class_eq_cohomologicalEndomorphismClass P F hobj))
        (Boundary.FormalEulerFactor.Cohomological.cohomologicalEulerFactor_log_eq_eulerLog
          (K := K) (V := V) P.degrees F).symm))

/-- The package reciprocal zeta factor agrees with the cohomological reciprocal
zeta factor when the package is built from a cohomological family. -/
theorem zetaFactor_eq_cohomologicalZetaFactor
    (P : FrobeniusCohomologyPackage.{u, v} K)
    {V : ℤ → Type v}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, FiniteDimensional K (V i)]
    (F : ∀ i, Module.End K (V i))
    (hobj : ∀ i, P.object i =
      Boundary.CohomologicalEulerFactor.endomorphismObject (V := V) F i) :
    P.zetaFactor = Boundary.FormalEulerFactor.Cohomological.cohomologicalZetaFactor
      (K := K) (V := V) P.degrees F :=
  Boundary.FormalEulerFactor.Factor.ext (K := K)
    (Eq.trans
      (zetaFactor_log P)
      (Eq.trans
        (congrArg (Boundary.EulerFactorLog.zetaLog K)
          (k0Class_eq_cohomologicalEndomorphismClass P F hobj))
        (Boundary.FormalEulerFactor.Cohomological.cohomologicalZetaFactor_log_eq_zetaLog
          (K := K) (V := V) P.degrees F).symm))

/-- The sign attached to a cohomological degree for the alternating
K₀-class. -/
def degreeSign (i : ℤ) : ℤ :=
  if Even i then 1 else -1

/-- Even degrees have positive sign. -/
theorem degreeSign_of_even (i : ℤ) (hi : Even i) :
    degreeSign i = 1 :=
  if_pos hi

/-- Odd degrees have negative sign. -/
theorem degreeSign_of_odd (i : ℤ) (hi : Odd i) :
    degreeSign i = -1 :=
  if_neg ((Int.not_even_iff_odd).2 hi)

/-- The successor of an even degree has negative sign. -/
theorem degreeSign_add_one_of_even (i : ℤ) (hi : Even i) :
    degreeSign (i + 1) = - degreeSign i :=
  Eq.trans
    (degreeSign_of_odd (i + 1)
      ((Int.not_even_iff_odd).1
        (fun hsucc => (Int.even_add_one.1 hsucc) hi)))
    (congrArg Neg.neg (degreeSign_of_even i hi).symm)

/-- The successor of an odd degree has positive sign. -/
theorem degreeSign_add_one_of_odd (i : ℤ) (hi : Odd i) :
    degreeSign (i + 1) = - degreeSign i :=
  Eq.trans
    (degreeSign_of_even (i + 1)
      (Int.even_add_one.2 ((Int.not_even_iff_odd).2 hi)))
    (congrArg Neg.neg (degreeSign_of_odd i hi).symm)

/-- A one-step shift flips the degree sign. -/
theorem degreeSign_add_one (i : ℤ) :
    degreeSign (i + 1) = - degreeSign i :=
  match Int.even_or_odd i with
  | Or.inl hi => degreeSign_add_one_of_even i hi
  | Or.inr hi => degreeSign_add_one_of_odd i hi

theorem one_zsmul_eq_self {G : Type*} [AddCommGroup G] (x : G) :
    (1 : ℤ) • x = x :=
  one_zsmul x

theorem neg_one_zsmul_eq_neg {G : Type*} [AddCommGroup G] (x : G) :
    (-1 : ℤ) • x = -x :=
  neg_one_zsmul x

theorem degreeSign_smul_of_even {G : Type*} [AddCommGroup G]
    (i : ℤ) (x : G) (hi : Even i) :
    degreeSign i • x = x :=
  Eq.trans
    (congrArg (fun c : ℤ => c • x) (degreeSign_of_even i hi))
    (one_zsmul_eq_self x)

theorem degreeSign_smul_of_odd {G : Type*} [AddCommGroup G]
    (i : ℤ) (x : G) (hi : Odd i) :
    degreeSign i • x = -x :=
  Eq.trans
    (congrArg (fun c : ℤ => c • x) (degreeSign_of_odd i hi))
    (neg_one_zsmul_eq_neg x)

theorem sum_degreeSign_smul_even_filter {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => Even i), degreeSign i • x i) =
      ∑ i in S.filter (fun i => Even i), x i :=
  Finset.sum_congr (Eq.refl (S.filter (fun i => Even i)))
    (fun i hi =>
      degreeSign_smul_of_even i (x i) (Finset.mem_filter.1 hi).2)

theorem sum_degreeSign_smul_odd_filter {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => Odd i), degreeSign i • x i) =
      ∑ i in S.filter (fun i => Odd i), -x i :=
  Finset.sum_congr (Eq.refl (S.filter (fun i => Odd i)))
    (fun i hi =>
      degreeSign_smul_of_odd i (x i) (Finset.mem_filter.1 hi).2)

theorem sum_neg_eq_neg_sum {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S, -x i) = -∑ i in S, x i :=
  Finset.sum_neg_distrib

theorem sum_degreeSign_smul_odd_filter_eq_neg {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => Odd i), degreeSign i • x i) =
      -∑ i in S.filter (fun i => Odd i), x i :=
  Eq.trans
    (sum_degreeSign_smul_odd_filter S x)
    (sum_neg_eq_neg_sum (S.filter (fun i => Odd i)) x)

theorem sum_filter_not_even_eq_sum_filter_odd {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => ¬ Even i), x i) =
      ∑ i in S.filter (fun i => Odd i), x i :=
  Finset.sum_congr
    (Finset.filter_congr (fun _ _ => Int.not_even_iff_odd))
    (fun i _ => Eq.refl (x i))

theorem sum_degreeSign_smul_filter_not_even_eq_odd {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => ¬ Even i), degreeSign i • x i) =
      ∑ i in S.filter (fun i => Odd i), degreeSign i • x i :=
  sum_filter_not_even_eq_sum_filter_odd S (fun i => degreeSign i • x i)

theorem sum_degreeSign_smul_even_odd_split {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S, degreeSign i • x i) =
      (∑ i in S.filter (fun i => Even i), degreeSign i • x i) +
        ∑ i in S.filter (fun i => Odd i), degreeSign i • x i :=
  Eq.trans
    (Finset.sum_filter_add_sum_filter_not (s := S) (p := fun i => Even i)
      (f := fun i => degreeSign i • x i)).symm
    (congrArg₂ HAdd.hAdd
      (Eq.refl (∑ i in S.filter (fun i => Even i), degreeSign i • x i))
      (sum_degreeSign_smul_filter_not_even_eq_odd S x))

theorem even_sum_add_neg_odd_sum_eq_even_sub_odd {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => Even i), x i) +
        (-∑ i in S.filter (fun i => Odd i), x i) =
      (∑ i in S.filter (fun i => Even i), x i) -
        ∑ i in S.filter (fun i => Odd i), x i :=
  (sub_eq_add_neg
    (∑ i in S.filter (fun i => Even i), x i)
    (∑ i in S.filter (fun i => Odd i), x i)).symm

theorem sum_degreeSign_smul_eq_even_sub_odd {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S, degreeSign i • x i) =
      (∑ i in S.filter (fun i => Even i), x i) -
        ∑ i in S.filter (fun i => Odd i), x i :=
  Eq.trans
    (sum_degreeSign_smul_even_odd_split S x)
    (Eq.trans
      (congrArg₂ HAdd.hAdd
        (sum_degreeSign_smul_even_filter S x)
        (sum_degreeSign_smul_odd_filter_eq_neg S x))
      (even_sum_add_neg_odd_sum_eq_even_sub_odd S x))

theorem neg_even_sub_odd_eq_odd_sub_even {G : Type*} [AddCommGroup G]
    (a b : G) :
    -(a - b) = b - a :=
  neg_sub a b

theorem odd_sub_even_eq_neg_even_sub_odd {G : Type*} [AddCommGroup G]
    (a b : G) :
    b - a = -(a - b) :=
  (neg_even_sub_odd_eq_odd_sub_even a b).symm

theorem odd_sub_even_eq_neg_signed_sum {G : Type*} [AddCommGroup G]
    (S : Finset ℤ) (x : ℤ → G) :
    (∑ i in S.filter (fun i => Odd i), x i) -
        ∑ i in S.filter (fun i => Even i), x i =
      -∑ i in S, degreeSign i • x i :=
  Eq.trans
    (odd_sub_even_eq_neg_even_sub_odd
      (∑ i in S.filter (fun i => Even i), x i)
      (∑ i in S.filter (fun i => Odd i), x i))
    (congrArg Neg.neg (sum_degreeSign_smul_eq_even_sub_odd S x).symm)

/-- The package K₀ class as a single signed finite sum. -/
theorem k0Class_eq_signed_sum (P : FrobeniusCohomologyPackage.{u, v} K) :
    P.k0Class =
      -∑ i in P.degrees, degreeSign i •
        Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) :=
  odd_sub_even_eq_neg_signed_sum P.degrees
    (fun i =>
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)))

/-- Shift a package by one cohomological degree, extending by zero outside the
shifted support. -/
def shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    FrobeniusCohomologyPackage.{u, v} K where
  degrees := shiftInt P.degrees 1
  object := fun i =>
    if _h : i - 1 ∈ P.degrees then P.object (i - 1)
    else Boundary.EndomorphismK0.zeroObject K

theorem shiftOne_object_succ_of_mem
    (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) (hi : i ∈ P.degrees) :
    (P.shiftOne).object (i + 1) = P.object i :=
  Eq.trans
    (if_pos (Eq.subst (add_sub_cancel_right i 1).symm hi))
    (congrArg P.object (add_sub_cancel_right i 1))

theorem mk_shiftOne_object_succ_of_mem
    (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) (hi : i ∈ P.degrees) :
    Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K ((P.shiftOne).object (i + 1))) =
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) :=
  congrArg
    (fun A : Boundary.EndomorphismK0.EndomorphismObject K =>
      Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K A))
    (shiftOne_object_succ_of_mem P i hi)

theorem degreeSign_succ_smul_mk_shiftOne_object
    (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) (hi : i ∈ P.degrees) :
    degreeSign (i + 1) •
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K ((P.shiftOne).object (i + 1))) =
      -(degreeSign i •
        Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i))) :=
  Eq.trans
    (congrArg₂
      (fun c x => c • x)
      (degreeSign_add_one i)
      (mk_shiftOne_object_succ_of_mem P i hi))
    (neg_zsmul
      (Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)))
      (degreeSign i))

theorem shiftOne_signed_sum_reindex
    (P : FrobeniusCohomologyPackage.{u, v} K) :
    (∑ d in shiftInt P.degrees 1,
      degreeSign d •
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K ((P.shiftOne).object d))) =
      ∑ i in P.degrees,
        degreeSign (i + 1) •
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K ((P.shiftOne).object (i + 1))) :=
  sum_shiftInt_one (S := P.degrees)
    (f := fun d =>
      degreeSign d •
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K ((P.shiftOne).object d)))

theorem shiftOne_signed_sum_eq_neg_original_signed_sum
    (P : FrobeniusCohomologyPackage.{u, v} K) :
    (∑ d in shiftInt P.degrees 1,
      degreeSign d •
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K ((P.shiftOne).object d))) =
      -∑ i in P.degrees,
        degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) :=
  Eq.trans
    (shiftOne_signed_sum_reindex P)
    (Eq.trans
      (Finset.sum_congr (Eq.refl P.degrees)
        (fun i hi => degreeSign_succ_smul_mk_shiftOne_object P i hi))
      (sum_neg_eq_neg_sum P.degrees
        (fun i =>
          degreeSign i •
            Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)))))

theorem neg_k0Class_eq_original_signed_sum
    (P : FrobeniusCohomologyPackage.{u, v} K) :
    -P.k0Class =
      ∑ i in P.degrees,
        degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) :=
  Eq.trans
    (congrArg Neg.neg (k0Class_eq_signed_sum P))
    (neg_neg
      (∑ i in P.degrees,
        degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i))))

theorem neg_shiftOne_signed_sum_eq_original_signed_sum
    (P : FrobeniusCohomologyPackage.{u, v} K) :
    -(∑ d in shiftInt P.degrees 1,
      degreeSign d •
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K ((P.shiftOne).object d))) =
      ∑ i in P.degrees,
        degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)) :=
  Eq.trans
    (congrArg Neg.neg (shiftOne_signed_sum_eq_neg_original_signed_sum P))
    (neg_neg
      (∑ i in P.degrees,
        degreeSign i •
          Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i))))

/-- Shifting a package by one negates its K₀ class. -/
theorem k0Class_shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    (P.shiftOne).k0Class = - P.k0Class :=
  Eq.trans
    (k0Class_eq_signed_sum P.shiftOne)
    (Eq.trans
      (neg_shiftOne_signed_sum_eq_original_signed_sum P)
      (neg_k0Class_eq_original_signed_sum P).symm)


/-- Shifting a package by one inverts its Euler factor. -/
theorem eulerFactor_shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    eulerFactor (K := K) (P.shiftOne) = (eulerFactor (K := K) P)⁻¹ :=
  Boundary.FormalEulerFactor.Factor.ext (K := K)
    (Eq.trans
      (eulerFactor_log P.shiftOne)
      (Eq.trans
        (congrArg (Boundary.EulerFactorLog.eulerLog K) (k0Class_shiftOne P))
        (Boundary.EulerFactorLog.eulerLog_neg K P.k0Class)))

/-- Shifting a package by one inverts its reciprocal zeta factor. -/
theorem zetaFactor_shiftOne (P : FrobeniusCohomologyPackage.{u, v} K) :
    zetaFactor (K := K) (P.shiftOne) = (zetaFactor (K := K) P)⁻¹ :=
  Boundary.FormalEulerFactor.Factor.ext (K := K)
    (Eq.trans
      (zetaFactor_log P.shiftOne)
      (Eq.trans
        (congrArg (Boundary.EulerFactorLog.zetaLog K) (k0Class_shiftOne P))
        (Boundary.EulerFactorLog.zetaLog_neg K P.k0Class)))

/-- Euler factors multiply under canonical package direct sum. -/
theorem eulerFactor_directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).eulerFactor = P.eulerFactor * Q.eulerFactor :=
  Boundary.FormalEulerFactor.Factor.ext (K := K)
    (Eq.trans
      (eulerFactor_log (P.directSum Q))
      (Eq.trans
        (congrArg (Boundary.EulerFactorLog.eulerLog K) (k0Class_directSum P Q))
        (Boundary.EulerFactorLog.eulerLog_add K P.k0Class Q.k0Class)))

/-- Reciprocal zeta factors multiply under canonical package direct sum. -/
theorem zetaFactor_directSum (P Q : FrobeniusCohomologyPackage.{u, v} K) :
    (P.directSum Q).zetaFactor = P.zetaFactor * Q.zetaFactor :=
  Boundary.FormalEulerFactor.Factor.ext (K := K)
    (Eq.trans
      (zetaFactor_log (P.directSum Q))
      (Eq.trans
        (congrArg (Boundary.EulerFactorLog.zetaLog K) (k0Class_directSum P Q))
        (Boundary.EulerFactorLog.zetaLog_add K P.k0Class Q.k0Class)))

/-- Positive coefficients of the package Euler logarithm are the normalized
negative trace-power character of its K₀ class. -/
theorem coeff_eulerFactor_log [CharZero K]
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.eulerFactor.log =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n P.k0Class) / (n : K) :=
  Eq.trans
    (congrArg (PowerSeries.coeff K n) (eulerFactor_log P))
    (Boundary.EulerFactorLog.coeff_eulerLog K P.k0Class n hn)

/-- Positive coefficients of the package reciprocal zeta logarithm are the
normalized positive trace-power character of its K₀ class. -/
theorem coeff_zetaFactor_log
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.zetaFactor.log =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n P.k0Class) / (n : K) :=
  Eq.trans
    (congrArg (PowerSeries.coeff K n) (zetaFactor_log P))
    (Boundary.EulerFactorLog.coeff_zetaLog K P.k0Class n hn)

theorem traceCharacterK0_sum_object
    (P : FrobeniusCohomologyPackage.{u, v} K) (s : Finset ℤ) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K n
        (∑ i in s,
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K (P.object i))) =
      ∑ i in s,
        Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i) :=
  Eq.trans
    (map_sum (Boundary.EndomorphismK0.traceCharacterK0 K n)
      (fun i =>
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K (P.object i))) s)
    (Finset.sum_congr (Eq.refl s)
      (fun i _ =>
        Boundary.EndomorphismK0.traceCharacterK0_of (K := K) n (P.object i)))

theorem traceCharacterK0_k0Class_pow
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K n P.k0Class =
      (∑ i in P.degrees.filter (fun i => Odd i),
        Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i) :=
  Eq.trans
    (map_sub (Boundary.EndomorphismK0.traceCharacterK0 K n)
      (∑ i in P.degrees.filter (fun i => Odd i),
        Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i)))
      (∑ i in P.degrees.filter (fun i => Even i),
        Boundary.EndomorphismK0.mk K (Boundary.EndomorphismK0.of K (P.object i))))
    (congrArg₂ Sub.sub
      (traceCharacterK0_sum_object P (P.degrees.filter (fun i => Odd i)) n)
      (traceCharacterK0_sum_object P (P.degrees.filter (fun i => Even i)) n))

theorem traceCharacterK0_one_powerMapK0_k0Class
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
        (Boundary.EndomorphismK0.powerMapK0 K n P.k0Class) =
      (∑ i in P.degrees.filter (fun i => Odd i),
        Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i) :=
  Eq.trans
    (Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0 K n P.k0Class)
    (traceCharacterK0_k0Class_pow P n)

theorem tracePower_object_eq_trace_frobenius
    (P : FrobeniusCohomologyPackage.{u, v} K) (i : ℤ) (n : ℕ) :
    Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i) =
      LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n) :=
  Eq.refl
    (Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i))

theorem sum_tracePower_object_eq_sum_trace_frobenius
    (P : FrobeniusCohomologyPackage.{u, v} K) (s : Finset ℤ) (n : ℕ) :
    (∑ i in s,
      Boundary.EndomorphismK0.EndomorphismObject.tracePower n (P.object i)) =
      ∑ i in s, LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n) :=
  Finset.sum_congr (Eq.refl s)
    (fun i _ => tracePower_object_eq_trace_frobenius P i n)

theorem traceCharacterK0_one_powerMapK0_k0Class_eq_alternating_trace
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
        (Boundary.EndomorphismK0.powerMapK0 K n P.k0Class) =
      (∑ i in P.degrees.filter (fun i => Odd i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n) :=
  Eq.trans
    (traceCharacterK0_one_powerMapK0_k0Class P n)
    (congrArg₂ Sub.sub
      (sum_tracePower_object_eq_sum_trace_frobenius
        P (P.degrees.filter (fun i => Odd i)) n)
      (sum_tracePower_object_eq_sum_trace_frobenius
        P (P.degrees.filter (fun i => Even i)) n))

/-- The concrete alternating trace-power formula for coefficients of the
package Euler logarithm. -/
theorem coeff_eulerFactor_log_eq_alternating_trace [CharZero K]
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.eulerFactor.log =
      -(((∑ i in P.degrees.filter (fun i => Odd i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) / (n : K)) :=
  Eq.trans
    (coeff_eulerFactor_log P n hn)
    (Eq.trans
      (congrArg (fun t : K => -t / (n : K))
        (traceCharacterK0_one_powerMapK0_k0Class_eq_alternating_trace P n))
      (neg_div (n : K)
        ((∑ i in P.degrees.filter (fun i => Odd i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n))))

/-- The concrete alternating trace-power formula for coefficients of the
package reciprocal zeta logarithm. -/
theorem coeff_zetaFactor_log_eq_alternating_trace
    (P : FrobeniusCohomologyPackage.{u, v} K) (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n P.zetaFactor.log =
      ((∑ i in P.degrees.filter (fun i => Odd i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) -
        ∑ i in P.degrees.filter (fun i => Even i),
          LinearMap.trace K (P.cohomology i) ((P.frobenius i) ^ n)) / (n : K) :=
  Eq.trans
    (coeff_zetaFactor_log P n hn)
    (congrArg (fun t : K => t / (n : K))
      (traceCharacterK0_one_powerMapK0_k0Class_eq_alternating_trace P n))

end FrobeniusCohomologyPackage

end

end RealizationEulerFactor
end Boundary
