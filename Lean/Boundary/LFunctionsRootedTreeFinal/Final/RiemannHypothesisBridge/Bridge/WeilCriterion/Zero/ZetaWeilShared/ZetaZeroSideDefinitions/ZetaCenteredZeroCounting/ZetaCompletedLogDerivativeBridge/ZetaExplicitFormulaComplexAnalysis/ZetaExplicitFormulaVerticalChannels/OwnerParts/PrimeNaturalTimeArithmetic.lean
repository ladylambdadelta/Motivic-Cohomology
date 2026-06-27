import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.Admissible.ZetaAdmissiblePaleyWiener.ExplicitFormula.ZetaExplicitFormulaAnalyticCore.Owner
import Mathlib.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.Order.Interval.Finset.Defs

/-!
# Natural-number prime-time arithmetic

This file owns the arithmetic side of the prime contribution: the
natural-number von Mangoldt distribution and its reindexing by raw
prime-power coordinates.  It contains no contour or vertical-channel
analysis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- The natural number represented by a raw prime-power coordinate. -/
def zetaPrimePowerIndexToNat (ι : ZetaPrimePowerIndex) : ℕ :=
  ι.p ^ ι.n

/-- Genuine raw prime-power coordinates are equivalent to a prime and a
zero-based exponent.  The represented natural number is `p^(m+1)`. -/
def zetaPrimePowerGenuineEquivPrimesNat :
    {ι : ZetaPrimePowerIndex // ZetaPrimePowerIndex.IsGenuine ι} ≃
      Nat.Primes × ℕ where
  toFun ι :=
    (⟨ι.1.p, ι.2.1⟩, ι.1.n - 1)
  invFun q :=
    ⟨⟨q.1, q.2 + 1⟩, ⟨q.1.prop, Nat.succ_pos q.2⟩⟩
  left_inv := by
    intro ι
    cases ι with
    | mk raw hraw =>
        cases raw with
        | mk p n =>
            have hn_ne : n ≠ 0 :=
              Nat.ne_zero_of_lt hraw.2
            have hn : n - 1 + 1 = n :=
              Nat.sub_one_add_one hn_ne
            apply Subtype.ext
            exact congrArg (fun m : ℕ => ZetaPrimePowerIndex.mk p m) hn
  right_inv := by
    intro q
    cases q with
    | mk p m =>
        apply Prod.ext
        · exact Subtype.ext rfl
        · exact Nat.add_sub_cancel m 1

/-- The genuine-coordinate equivalence represents the same natural number as
mathlib's canonical prime-power equivalence. -/
theorem zetaPrimePowerGenuineEquivPrimesNat_toNat
    (ι : {ι : ZetaPrimePowerIndex // ZetaPrimePowerIndex.IsGenuine ι}) :
    zetaPrimePowerIndexToNat ι.1 =
      (Nat.Primes.prodNatEquiv (zetaPrimePowerGenuineEquivPrimesNat ι) : ℕ) := by
  cases ι with
  | mk raw hraw =>
      cases raw with
      | mk p n =>
          unfold zetaPrimePowerIndexToNat
          unfold zetaPrimePowerGenuineEquivPrimesNat
          have hn_ne : n ≠ 0 :=
            Nat.ne_zero_of_lt hraw.2
          have hn : n - 1 + 1 = n :=
            Nat.sub_one_add_one hn_ne
          exact congrArg (fun m : ℕ => p ^ m) hn.symm

/-- The natural-number center used by the von Mangoldt Mellin inversion. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalCenter
    (n : ℕ) : ℝ :=
  Real.log n

/-- The natural-number center unfolds to `log n`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log
    (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalCenter n =
      Real.log n := by
  rfl

/-- Time-boundary values commute with reflection by negating the time
coordinate. -/
theorem zetaCompletedTimeBoundaryValue_reflect
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedTimeBoundaryValue (ZetaAdmissibleFunction.reflect f) a =
      zetaCompletedTimeBoundaryValue f (-a) := by
  calc
    zetaCompletedTimeBoundaryValue (ZetaAdmissibleFunction.reflect f) a =
        ZetaAdmissibleFunction.reflect f a := by
      exact zetaCompletedTimeBoundaryValue_eq_apply
        (ZetaAdmissibleFunction.reflect f) a
    _ = f (-a) := by
      exact ZetaAdmissibleFunction.reflect_apply f a
    _ = zetaCompletedTimeBoundaryValue f (-a) := by
      exact (zetaCompletedTimeBoundaryValue_eq_apply f (-a)).symm

/-- At a natural prime center, reflection evaluates the time boundary at the
opposite logarithmic center. -/
theorem zetaCompletedTimeBoundaryValue_reflect_primeNaturalCenter
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedTimeBoundaryValue
        (ZetaAdmissibleFunction.reflect f)
        (zetaCompletedExplicitFormulaPrimeNaturalCenter n) =
      zetaCompletedTimeBoundaryValue f
        (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  exact
    zetaCompletedTimeBoundaryValue_reflect
      f (zetaCompletedExplicitFormulaPrimeNaturalCenter n)

/-- A nonzero natural index is a positive real Mellin argument. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalCast_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < (n : ℝ) := by
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)

/-- A nonzero natural index is a nonzero complex Mellin base. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalCast_complex_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr hn

/-- The complex half-power of a natural index is the real square root. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_cpow_half_eq_sqrt
    (n : ℕ) :
    (n : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt n : ℂ) := by
  have hcpow :
      (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ)) : ℂ) :=
    (Complex.ofReal_cpow (Nat.cast_nonneg n) (1 / 2 : ℝ)).symm
  have hsqrt :
      (((n : ℝ) ^ (1 / 2 : ℝ)) : ℂ) =
        (Real.sqrt n : ℂ) :=
    congrArg (fun x : ℝ => (x : ℂ))
      (Real.sqrt_eq_rpow (n : ℝ)).symm
  exact Eq.trans hcpow hsqrt

/-- The complex negative half-power of a natural index is the inverse real
square root. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_cpow_neg_half_eq_inv_sqrt
    (n : ℕ) :
    (n : ℂ) ^ (-(1 / 2 : ℂ)) =
      ((Real.sqrt n : ℂ))⁻¹ := by
  exact Eq.trans
    (Complex.cpow_neg (n : ℂ) (1 / 2 : ℂ))
    (congrArg Inv.inv
      (zetaCompletedExplicitFormulaPrimeNatural_cpow_half_eq_sqrt n))

/-- The real completed von Mangoldt weight coerces to the product of the
complex von Mangoldt value and the inverse square-root character. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalWeight_complex_eq
    (n : ℕ) :
    ((Λ n / Real.sqrt n : ℝ) : ℂ) =
      ((↗Λ) n : ℂ) * ((Real.sqrt n : ℂ))⁻¹ := by
  calc
    ((Λ n / Real.sqrt n : ℝ) : ℂ) =
        ((Λ n * (Real.sqrt n)⁻¹ : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => (x : ℂ))
        (div_eq_mul_inv (Λ n) (Real.sqrt n))
    _ =
        ((Λ n : ℝ) : ℂ) * (((Real.sqrt n)⁻¹ : ℝ) : ℂ) := by
      exact Complex.ofReal_mul (Λ n) ((Real.sqrt n)⁻¹)
    _ =
        ((Λ n : ℂ)) * ((Real.sqrt n : ℂ))⁻¹ := by
      exact congrArg (fun z : ℂ => ((Λ n : ℂ)) * z)
        (Complex.ofReal_inv (Real.sqrt n))
    _ =
        ((↗Λ) n : ℂ) * ((Real.sqrt n : ℂ))⁻¹ := by
      rfl

/-- The completed natural-number von Mangoldt weight, with the zero term
removed before the square-root normalization is formed. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalWeight
    (n : ℕ) : ℝ :=
  if n = 0 then
    0
  else
    Λ n / Real.sqrt n

/-- The natural von Mangoldt weight vanishes at zero. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalWeight_zero :
    zetaCompletedExplicitFormulaPrimeNaturalWeight 0 = 0 := by
  rfl

/-- Away from zero, the natural von Mangoldt weight is the completed
normalization `Λ n / sqrt n`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalWeight_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalWeight n =
      Λ n / Real.sqrt n := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalWeight
  exact if_neg hn

/-- The natural von Mangoldt weight vanishes away from prime powers. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalWeight_eq_zero_of_not_isPrimePow
    {n : ℕ} (hn : ¬ IsPrimePow n) :
    zetaCompletedExplicitFormulaPrimeNaturalWeight n = 0 := by
  by_cases hzero : n = 0
  · exact Eq.trans (congrArg zetaCompletedExplicitFormulaPrimeNaturalWeight hzero)
      zetaCompletedExplicitFormulaPrimeNaturalWeight_zero
  · have hΛ : Λ n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    calc
      zetaCompletedExplicitFormulaPrimeNaturalWeight n =
          Λ n / Real.sqrt n :=
        zetaCompletedExplicitFormulaPrimeNaturalWeight_of_ne_zero hzero
      _ = 0 / Real.sqrt n := by
        exact congrArg (fun x : ℝ => x / Real.sqrt n) hΛ
      _ = 0 := by
        exact zero_div (Real.sqrt n)

/-- The one-sided natural-number time sample produced by the right
von-Mangoldt vertical Mellin inversion before the left/conjugate prime side is
combined with it. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
    ((2 * π : ℝ) •
      zetaCompletedTimeBoundaryValue f
        (zetaCompletedExplicitFormulaPrimeNaturalCenter n))

/-- Away from zero, the one-sided natural time sample unfolds to the completed
von-Mangoldt weight `Λ n / sqrt n` at the logarithmic center. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
  exact congrArg
    (fun w : ℝ =>
      ((w : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))
    (zetaCompletedExplicitFormulaPrimeNaturalWeight_of_ne_zero hn)

/-- Away from zero, the one-sided sample of the reflected admissible probe is
the completed von-Mangoldt weight at the opposite logarithmic center. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_reflect_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
        (ZetaAdmissibleFunction.reflect f) n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
  have hsample :
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
          (ZetaAdmissibleFunction.reflect f) n =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue
              (ZetaAdmissibleFunction.reflect f)
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_of_ne_zero
      (ZetaAdmissibleFunction.reflect f) hn
  have htime :
      zetaCompletedTimeBoundaryValue
          (ZetaAdmissibleFunction.reflect f)
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) =
        zetaCompletedTimeBoundaryValue f
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
    zetaCompletedTimeBoundaryValue_reflect_primeNaturalCenter f n
  exact
    Eq.trans hsample
      (congrArg
        (fun z : ℂ =>
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) • z))
        htime)

/-- The reflected negative-time natural boundary sample with completed
von-Mangoldt normalization.

This is the exact time-side value produced by reflected right-line
Paley-Wiener sampling.  It is intentionally separate from
`zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample`: identifying
the two is the remaining functional-equation/Hermitian normalization, not a
definition of reflection. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
    ((2 * π : ℝ) •
      zetaCompletedTimeBoundaryValue f
        (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)))

/-- The reflected negative-time natural boundary sample unfolds away from the
zero index to the completed von-Mangoldt weight `Λ n / sqrt n`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
  exact congrArg
    (fun w : ℝ =>
      ((w : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))))
    (zetaCompletedExplicitFormulaPrimeNaturalWeight_of_ne_zero hn)

/-- The one-sided natural sample of the reflected probe is the named
negative-time reflected boundary sample. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_reflect_eq_reflectedTimeBoundarySample
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
        (ZetaAdmissibleFunction.reflect f) n =
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
  unfold zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
  have htime :
      zetaCompletedTimeBoundaryValue
          (ZetaAdmissibleFunction.reflect f)
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) =
        zetaCompletedTimeBoundaryValue f
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
    zetaCompletedTimeBoundaryValue_reflect_primeNaturalCenter f n
  exact
    congrArg
      (fun z : ℂ =>
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
          ((2 * π : ℝ) • z))
      htime

/-- The zero reflected negative-time natural boundary sample vanishes. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f 0 = 0 := by
  calc
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f 0 =
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight 0 : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (-(zetaCompletedExplicitFormulaPrimeNaturalCenter 0))) := by
      rfl
    _ =
        ((0 : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (-(zetaCompletedExplicitFormulaPrimeNaturalCenter 0))) := by
      exact congrArg
        (fun w : ℝ =>
          ((w : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter 0))))
        zetaCompletedExplicitFormulaPrimeNaturalWeight_zero
    _ = 0 := by
      exact zero_mul
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))

/-- The two analytic one-sided natural boundary faces produced by the right
and reflected-left Mellin inversions. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n

/-- The two-face natural boundary sample unfolds as right one-sided plus
reflected one-sided. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_eq
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n := by
  rfl

/-- Away from zero, the two-face boundary sample unfolds to the two completed
von-Mangoldt boundary values at opposite logarithmic centers.

This is the exact scalar expression that must match the symmetric natural
summand in the remaining Hermitian/time-side normalization. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
  calc
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n := by
      rfl
    _ =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n := by
      exact congrArg
        (fun z : ℂ =>
          z + zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n)
        (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_of_ne_zero
          f hn)
    _ =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
      exact congrArg
        (fun z : ℂ =>
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
            z)
        (zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_of_ne_zero
          f hn)

/-- Under the reflection-dagger identity at a nonzero natural prime center, the
two-face boundary sample is exactly the scalar multiple of the Hermitian
time-boundary sum.

This is only the two-face algebra. It does not identify the result with the
real symmetric `TimeSummand`; that comparison carries the separate explicit
formula normalization constants. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero_of_reflectionDagger
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0)
    (hreflect :
      zetaCompletedTimeBoundaryValue f
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
        star
          (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n))) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) := by
  let W : ℂ := ((Λ n / Real.sqrt n : ℝ) : ℂ)
  let R : ℝ := (2 * π : ℝ)
  let V : ℂ :=
    zetaCompletedTimeBoundaryValue f
      (zetaCompletedExplicitFormulaPrimeNaturalCenter n)
  let Vneg : ℂ :=
    zetaCompletedTimeBoundaryValue f
      (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))
  have htwo :
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
        W * (R • V) + W * (R • Vneg) :=
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero
      f hn
  have hneg : Vneg = star V :=
    hreflect
  have hmul :
      W * (R • V) + W * (R • star V) =
        W * ((R • V) + (R • star V)) := by
    exact (mul_add W (R • V) (R • star V)).symm
  have hsmul :
      (R • V) + (R • star V) = R • (V + star V) := by
    exact (smul_add R V (star V)).symm
  calc
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
        W * (R • V) + W * (R • Vneg) := htwo
    _ = W * (R • V) + W * (R • star V) := by
      exact congrArg (fun z : ℂ => W * (R • V) + W * (R • z)) hneg
    _ = W * ((R • V) + (R • star V)) := hmul
    _ = W * (R • (V + star V)) := by
      exact congrArg (fun z : ℂ => W * z) hsmul

/-- The two-face boundary sample vanishes at the zero natural index. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f 0 = 0 := by
  have hone :
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0 = 0 := by
    unfold zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
    calc
      ((zetaCompletedExplicitFormulaPrimeNaturalWeight 0 : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)) =
          ((0 : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)) := by
        exact congrArg
          (fun w : ℝ =>
            ((w : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))
          zetaCompletedExplicitFormulaPrimeNaturalWeight_zero
      _ = 0 := by
        exact zero_mul
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter 0))
  calc
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f 0 =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0 +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f 0 := by
      rfl
    _ = 0 +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f 0 := by
      exact congrArg
        (fun z : ℂ =>
          z + zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f 0)
        hone
    _ = 0 + 0 := by
      exact congrArg
        (fun z : ℂ => 0 + z)
        (zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_zero
          f)
    _ = 0 := by
      exact zero_add 0

/-- The zeroth one-sided natural time sample vanishes. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0 = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
  calc
    ((zetaCompletedExplicitFormulaPrimeNaturalWeight 0 : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)) =
        ((0 : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)) := by
      exact congrArg
        (fun w : ℝ =>
          ((w : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))
        zetaCompletedExplicitFormulaPrimeNaturalWeight_zero
    _ = 0 := by
      exact zero_mul
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter 0))

/-- The completed boundary-value support is the same as the original
compactly supported admissible source support. -/
theorem zetaCompletedExplicitFormula_timeBoundarySupport_eq
    (f : ZetaAdmissibleFunction) :
    tsupport f.toZetaTestFunction' = tsupport f.toZetaTestFunction := by
  exact congrArg tsupport
    (funext
      (fun u : ℝ =>
        ZetaAdmissibleFunction.toZetaTestFunction'_apply f u))

/-- Compact support gives an upper bound for the completed boundary-value
support used by the natural-number prime samples. -/
theorem exists_zetaCompletedExplicitFormula_timeBoundarySupportUpperBound
    (f : ZetaAdmissibleFunction) :
    ∃ B : ℝ, ∀ x ∈ tsupport f.toZetaTestFunction', x ≤ B := by
  obtain ⟨B, hB⟩ :=
    IsCompact.bddAbove
      f.toZetaTestFunction.hasCompactSupport.isCompact
  refine ⟨B, ?_⟩
  intro x hx
  have hx_source : x ∈ tsupport f.toZetaTestFunction := by
    exact
      Eq.subst
        (motive := fun S : Set ℝ => x ∈ S)
        (zetaCompletedExplicitFormula_timeBoundarySupport_eq f)
        hx
  exact hB x hx_source

/-- Compact support gives a lower bound for the completed boundary-value
support used by reflected natural-number prime samples. -/
theorem exists_zetaCompletedExplicitFormula_timeBoundarySupportLowerBound
    (f : ZetaAdmissibleFunction) :
    ∃ A : ℝ, ∀ x ∈ tsupport f.toZetaTestFunction', A ≤ x := by
  obtain ⟨A, hA⟩ :=
    IsCompact.bddBelow
      f.toZetaTestFunction.hasCompactSupport.isCompact
  refine ⟨A, ?_⟩
  intro x hx
  have hx_source : x ∈ tsupport f.toZetaTestFunction := by
    exact
      Eq.subst
        (motive := fun S : Set ℝ => x ∈ S)
        (zetaCompletedExplicitFormula_timeBoundarySupport_eq f)
        hx
  exact hA x hx_source

/-- The completed boundary value vanishes above any upper bound for its
time-domain support. -/
theorem zetaCompletedTimeBoundaryValue_eq_zero_of_supportUpperBound_lt
    (f : ZetaAdmissibleFunction) {B a : ℝ}
    (hB : ∀ x ∈ tsupport f.toZetaTestFunction', x ≤ B)
    (ha : B < a) :
    zetaCompletedTimeBoundaryValue f a = 0 := by
  have hnot_mem : a ∉ tsupport f.toZetaTestFunction' := by
    intro ha_mem
    have hle : a ≤ B := hB a ha_mem
    exact (not_lt_of_ge hle) ha
  calc
    zetaCompletedTimeBoundaryValue f a =
        f.toZetaTestFunction' a := by
      rfl
    _ = 0 := by
      exact image_eq_zero_of_nmem_tsupport hnot_mem

/-- The completed boundary value vanishes below any lower bound for its
time-domain support. -/
theorem zetaCompletedTimeBoundaryValue_eq_zero_of_lt_supportLowerBound
    (f : ZetaAdmissibleFunction) {A a : ℝ}
    (hA : ∀ x ∈ tsupport f.toZetaTestFunction', A ≤ x)
    (ha : a < A) :
    zetaCompletedTimeBoundaryValue f a = 0 := by
  have hnot_mem : a ∉ tsupport f.toZetaTestFunction' := by
    intro ha_mem
    have hle : A ≤ a := hA a ha_mem
    exact (not_lt_of_ge hle) ha
  calc
    zetaCompletedTimeBoundaryValue f a =
        f.toZetaTestFunction' a := by
      rfl
    _ = 0 := by
      exact image_eq_zero_of_nmem_tsupport hnot_mem

/-- Once a natural index is larger than the exponential ceiling of a support
bound, its logarithmic center lies strictly beyond that support bound. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalSupportUpper_lt_log_of_ceil_lt
    {B : ℝ} {n : ℕ}
    (hn : Nat.ceil (Real.exp B) < n) :
    B < Real.log n := by
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_le_of_lt (Nat.zero_le (Nat.ceil (Real.exp B))) hn
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hceil_lt : ((Nat.ceil (Real.exp B) : ℕ) : ℝ) < (n : ℝ) :=
    Nat.cast_lt.mpr hn
  have hexp_le : Real.exp B ≤ ((Nat.ceil (Real.exp B) : ℕ) : ℝ) :=
    Nat.le_ceil (Real.exp B)
  have hexp_lt : Real.exp B < (n : ℝ) :=
    lt_of_le_of_lt hexp_le hceil_lt
  exact (Real.lt_log_iff_exp_lt hn_pos).mpr hexp_lt

/-- A one-sided prime natural-time sample vanishes once its logarithmic center
lies above a support upper bound for the completed boundary source. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_eq_zero_of_supportUpperBound_lt_log
    (f : ZetaAdmissibleFunction) {B : ℝ} {n : ℕ}
    (hB : ∀ x ∈ tsupport f.toZetaTestFunction', x ≤ B)
    (hn : B < Real.log n) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n = 0 := by
  have hcenter_log :
      zetaCompletedExplicitFormulaPrimeNaturalCenter n =
        Real.log n :=
    zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log n
  have hcenter_zero :
      zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) = 0 := by
    exact
      zetaCompletedTimeBoundaryValue_eq_zero_of_supportUpperBound_lt
        f hB
        (Eq.subst
          (motive := fun a : ℝ => B < a)
          hcenter_log.symm
          hn)
  unfold zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
  calc
    ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
          ((2 * π : ℝ) • (0 : ℂ)) := by
      exact congrArg
        (fun z : ℂ =>
          ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
            ((2 * π : ℝ) • z))
        hcenter_zero
    _ =
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
          0 := by
      exact congrArg
        (fun z : ℂ =>
          ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) * z)
        (smul_zero (2 * π : ℝ) : (2 * π : ℝ) • (0 : ℂ) = 0)
    _ = 0 := by
      exact mul_zero
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ)

/-- A one-sided prime natural-time sample vanishes for all sufficiently large
natural indices, explicitly bounded by the exponential ceiling of a compact
support bound. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_eq_zero_of_supportCeil_lt
    (f : ZetaAdmissibleFunction) {B : ℝ} {n : ℕ}
    (hB : ∀ x ∈ tsupport f.toZetaTestFunction', x ≤ B)
    (hn : Nat.ceil (Real.exp B) < n) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n = 0 := by
  exact
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_eq_zero_of_supportUpperBound_lt_log
      f hB
      (zetaCompletedExplicitFormulaPrimeNaturalSupportUpper_lt_log_of_ceil_lt
        hn)

/-- The one-sided prime natural-time samples have finite support, because the
admissible source is compactly supported and the centers are `log n`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_support_finite
    (f : ZetaAdmissibleFunction) :
    (Function.support
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n)).Finite := by
  obtain ⟨B, hB⟩ :=
    exists_zetaCompletedExplicitFormula_timeBoundarySupportUpperBound f
  let M : ℕ := Nat.ceil (Real.exp B)
  have hsubset :
      Function.support
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) ⊆
        Set.Iic M := by
    intro n hn
    by_contra hnot_le
    have hlt : M < n :=
      Nat.lt_of_not_ge hnot_le
    have hzero :
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n = 0 :=
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_eq_zero_of_supportCeil_lt
        f hB hlt
    exact hn hzero
  exact
    Set.Finite.subset
      (by
        simpa only [Finset.coe_Iic] using
          (Finset.Iic M).finite_toSet)
      hsubset

/-- The one-sided natural-time sample series is summable; in fact it has
finite support. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) := by
  exact
    summable_of_finite_support
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_support_finite
        f)

/-- A reflected prime natural boundary sample vanishes once the opposite
logarithmic center lies below a support lower bound for the completed boundary
source. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_zero_of_neg_log_lt_supportLowerBound
    (f : ZetaAdmissibleFunction) {A : ℝ} {n : ℕ}
    (hA : ∀ x ∈ tsupport f.toZetaTestFunction', A ≤ x)
    (hn : -Real.log n < A) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n = 0 := by
  have hcenter_log :
      zetaCompletedExplicitFormulaPrimeNaturalCenter n =
        Real.log n :=
    zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log n
  have hcenter_neg :
      -(zetaCompletedExplicitFormulaPrimeNaturalCenter n) =
        -Real.log n :=
    congrArg Neg.neg hcenter_log
  have hcenter_zero :
      zetaCompletedTimeBoundaryValue f
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) = 0 := by
    exact
      zetaCompletedTimeBoundaryValue_eq_zero_of_lt_supportLowerBound
        f hA
        (Eq.subst
          (motive := fun a : ℝ => a < A)
          hcenter_neg.symm
          hn)
  unfold zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
  calc
    ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) =
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
          ((2 * π : ℝ) • (0 : ℂ)) := by
      exact congrArg
        (fun z : ℂ =>
          ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
            ((2 * π : ℝ) • z))
        hcenter_zero
    _ =
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) *
          0 := by
      exact congrArg
        (fun z : ℂ =>
          ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ) * z)
        (smul_zero (2 * π : ℝ) : (2 * π : ℝ) • (0 : ℂ) = 0)
    _ = 0 := by
      exact mul_zero
        ((zetaCompletedExplicitFormulaPrimeNaturalWeight n : ℝ) : ℂ)

/-- A reflected prime natural boundary sample vanishes for all sufficiently
large natural indices, explicitly bounded by the exponential ceiling of the
opposite lower support bound. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_zero_of_supportCeil_lt
    (f : ZetaAdmissibleFunction) {A : ℝ} {n : ℕ}
    (hA : ∀ x ∈ tsupport f.toZetaTestFunction', A ≤ x)
    (hn : Nat.ceil (Real.exp (-A)) < n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n = 0 := by
  have hnegA_log : -A < Real.log n :=
    zetaCompletedExplicitFormulaPrimeNaturalSupportUpper_lt_log_of_ceil_lt
      hn
  have hneg_log_A : -Real.log n < A := by
    have hneg : -Real.log n < -(-A) :=
      neg_lt_neg hnegA_log
    exact
      Eq.subst
        (motive := fun a : ℝ => -Real.log n < a)
        (neg_neg A)
        hneg
  exact
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_zero_of_neg_log_lt_supportLowerBound
      f hA hneg_log_A

/-- The reflected natural boundary samples have finite support, because the
admissible source is compactly supported and the reflected centers are
`-log n`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_support_finite
    (f : ZetaAdmissibleFunction) :
    (Function.support
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n)).Finite := by
  obtain ⟨A, hA⟩ :=
    exists_zetaCompletedExplicitFormula_timeBoundarySupportLowerBound f
  let M : ℕ := Nat.ceil (Real.exp (-A))
  have hsubset :
      Function.support
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) ⊆
        Set.Iic M := by
    intro n hn
    by_contra hnot_le
    have hlt : M < n :=
      Nat.lt_of_not_ge hnot_le
    have hzero :
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n = 0 :=
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_zero_of_supportCeil_lt
        f hA hlt
    exact hn hzero
  exact
    Set.Finite.subset
      (by
        simpa only [Finset.coe_Iic] using
          (Finset.Iic M).finite_toSet)
      hsubset

/-- The reflected natural boundary sample series is summable; in fact it has
finite support. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n) := by
  exact
    summable_of_finite_support
      (zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_support_finite
        f)

/-- The two-face natural boundary sample series is summable; both one-sided
faces have finite support. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) := by
  have hone :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f
  have hreflected :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) :=
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_summable
      f
  have hsum :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
            zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f n) :=
    Summable.add hone hreflected
  exact
    Eq.subst
      (motive := fun u : ℕ → ℂ => Summable u)
      (funext
        (fun n : ℕ =>
          (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_eq
            f n).symm))
      hsum

/-- The right one-sided natural-number prime contribution before the
left/conjugate recombination into the symmetric explicit-formula prime
contribution. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' n : ℕ,
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n

/-- The one-sided natural contribution unfolds to the natural-number sum of
one-sided samples. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution_eq_tsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  rfl

/-- The reflected natural-number boundary contribution produced by the
negative-time reflected Mellin samples. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' n : ℕ,
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n

/-- The reflected natural boundary contribution unfolds to the natural-number
sum of reflected samples. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_tsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n := by
  rfl

/-- The two-face boundary contribution is the sum of the right one-sided and
reflected negative-time boundary samples. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' n : ℕ,
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n

/-- The two-face boundary contribution unfolds to the natural-number sum of
two-face boundary samples. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_eq_tsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
  rfl

/-- The two-face boundary contribution is the sum of its one-sided and
reflected faces. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_eq_oneSided_add_reflectedBoundaryContribution
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
        zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f := by
  have hone :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f
  have hreflected :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) :=
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_summable
      f
  have htwoFace :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
            zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f n :=
    tsum_congr
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_eq
          f n)
  have hadd :
      (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
            zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f n) =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) +
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f n :=
    tsum_add hone hreflected
  calc
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution f =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
            f n := by
      rfl
    _ =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
            zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f n := by
      exact htwoFace
    _ =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) +
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f n := by
      exact hadd
    _ =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
            f := by
      exact congrArg₂ HAdd.hAdd
        (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution_eq_tsum
          f).symm
        (zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_tsum
          f).symm

/-- The natural center at a genuine prime-power coordinate agrees with the
prime-power window center. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalCenter_pow_eq_primePowerCenter
    {p k : ℕ} (hp : Nat.Prime p) :
    zetaCompletedExplicitFormulaPrimeNaturalCenter (p ^ k) =
      zetaPrimePacketCenter p k := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalCenter
  unfold zetaPrimePacketCenter
  have hcast : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k :=
    Nat.cast_pow p k
  calc
    Real.log (p ^ k) = Real.log ((p : ℝ) ^ k) := by
      exact congrArg Real.log hcast
    _ = (k : ℝ) * Real.log p := by
      exact Real.log_pow (p : ℝ) k
    _ = ↑k * Real.log p := by
      rfl

/-- The natural von Mangoldt weight at a genuine prime-power coordinate agrees
with the raw prime-power index weight. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalWeight_pow_eq_primePowerWeight
    {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    zetaCompletedExplicitFormulaPrimeNaturalWeight (p ^ k) =
      ZetaPrimePowerIndex.weight ⟨p, k⟩ := by
  have hk_ne : k ≠ 0 := by
    exact Nat.ne_zero_of_lt hk
  have hp_ne : p ≠ 0 :=
    hp.ne_zero
  have hpow_ne : p ^ k ≠ 0 :=
    pow_ne_zero k hp_ne
  unfold ZetaPrimePowerIndex.weight
  calc
    zetaCompletedExplicitFormulaPrimeNaturalWeight (p ^ k) =
        Λ (p ^ k) / Real.sqrt (p ^ k) :=
      zetaCompletedExplicitFormulaPrimeNaturalWeight_of_ne_zero hpow_ne
    _ = Λ p / Real.sqrt (p ^ k) := by
      exact congrArg (fun x : ℝ => x / Real.sqrt (p ^ k))
        (ArithmeticFunction.vonMangoldt_apply_pow hk_ne)
    _ = Real.log p / Real.sqrt (p ^ k) := by
      exact congrArg (fun x : ℝ => x / Real.sqrt (p ^ k))
        (ArithmeticFunction.vonMangoldt_apply_prime hp)
    _ = (if _hp : Nat.Prime p then
          if _hk : 1 ≤ k then
            Real.log p / Real.sqrt (p ^ k)
          else
            0
        else
          0) := by
      let a : ℝ := Real.log p / Real.sqrt (p ^ k)
      have hinner :
          (if _hk : 1 ≤ k then a else 0) = a :=
        if_pos hk
      have houter :
          (if _hp : Nat.Prime p then
            if _hk : 1 ≤ k then a else 0
          else
            0) =
          (if _hk : 1 ≤ k then a else 0) :=
        if_pos hp
      exact (Eq.trans houter hinner).symm

/-- The natural-number time-side summand produced by Mellin inversion of the
right von Mangoldt line. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  -(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
    Complex.re
      (zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
        star
          (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n))))

/-- Away from zero, the natural-time summand unfolds to the completed
von-Mangoldt weight `Λ n / sqrt n` at the logarithmic center. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
      -((Λ n / Real.sqrt n) *
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
  exact congrArg
    (fun w : ℝ =>
      -(w *
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))))
    (zetaCompletedExplicitFormulaPrimeNaturalWeight_of_ne_zero hn)

/-- The symmetric natural-number von Mangoldt contribution.  This is the
time-side prime distribution after right/left recombination, before reindexing
to raw prime-power coordinates. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' n : ℕ,
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n

/-- The symmetric natural contribution unfolds to the natural-number sum of
the symmetric time-side summands. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_tsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n := by
  rfl

/-- The complementary natural-number prime sample needed to turn the right
one-sided Mellin sample into the symmetric time-side sample.

This is an arithmetic normalization, not a contour theorem: the left/reflected
prime analysis must later identify its own sample with this exact complement. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n -
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n

/-- The complementary prime sample unfolds as symmetric minus right one-sided. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_eq
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n =
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n -
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  rfl

/-- A two-face decomposition of the symmetric natural summand identifies the
reflected natural boundary sample with the complementary natural sample.

This is the arithmetic endpoint needed by the reflected left prime channel:
the analytic reflected Mellin inversion supplies the reflected sample, while
the Hermitian/time-side owner theorem should supply the two-face decomposition
of the symmetric summand. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_oneSided_add_reflected
    (f : ZetaAdmissibleFunction) (n : ℕ)
    (hsplit :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  let L : ℂ := zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n
  have hS : S = R + L :=
    hsplit
  calc
    L = (R + L) - R := by
      calc
        L = 0 + L := by
          exact (zero_add L).symm
        _ = (R + -R) + L := by
          exact congrArg (fun z : ℂ => z + L) (add_right_neg R).symm
        _ = R + (-R + L) := by
          exact add_assoc R (-R) L
        _ = R + (L + -R) := by
          exact congrArg (fun z : ℂ => R + z) (add_comm (-R) L)
        _ = (R + L) + -R := by
          exact (add_assoc R L (-R)).symm
        _ = (R + L) - R := by
          exact (sub_eq_add_neg (R + L) R).symm
    _ = S - R := by
      exact congrArg (fun z : ℂ => z - R) hS.symm
    _ =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
      exact
        (zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_eq
          f n).symm

/-- A named two-face decomposition of the symmetric natural summand identifies
the reflected natural boundary sample with the complementary natural sample. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction) (n : ℕ)
    (hsplit :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
  exact
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_oneSided_add_reflected
      f n
      (Eq.trans hsplit
        (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_eq
          f n))

/-- The negative complementary sample is the right one-sided sample minus the
symmetric natural prime summand. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_neg_complementTimeSample_eq_oneSided_sub_symmetric
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n -
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n
  change -(S - R) = R - S
  calc
    -(S - R) = -(S + -R) := by
      exact congrArg Neg.neg (sub_eq_add_neg S R)
    _ = -S + -(-R) := by
      exact neg_add S (-R)
    _ = -S + R := by
      exact congrArg (fun z : ℂ => -S + z) (neg_neg R)
    _ = R + -S := by
      exact add_comm (-S) R
    _ = R - S := by
      exact (sub_eq_add_neg R S).symm

/-- Pointwise arithmetic recombination of the right one-sided sample with its
complementary sample. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementTimeSample
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n =
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n
  change R + (S - R) = S
  calc
    R + (S - R) = R + (S + -R) := by
      exact congrArg (fun z : ℂ => R + z) (sub_eq_add_neg S R)
    _ = R + (-R + S) := by
      exact congrArg (fun z : ℂ => R + z) (add_comm S (-R))
    _ = (R + -R) + S := by
      exact (add_assoc R (-R) S).symm
    _ = 0 + S := by
      exact congrArg (fun z : ℂ => z + S) (add_right_neg R)
    _ = S := by
      exact zero_add S

/-- If the reflected boundary sample has been identified with the arithmetic
complement, then the right one-sided and reflected boundary samples recombine
to the symmetric natural summand. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_reflectedTimeBoundarySample_eq_timeSummand_of_reflected_eq_complement
    (f : ZetaAdmissibleFunction) (n : ℕ)
    (hreflected :
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  let L : ℂ := zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n
  let C : ℂ := zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n
  have hL : L = C :=
    hreflected
  have hRC : R + C = S :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementTimeSample
      f n
  calc
    R + L = R + C := by
      exact congrArg (fun z : ℂ => R + z) hL
    _ = S := hRC

/-- If the reflected boundary sample has been identified with the arithmetic
complement, then the symmetric natural summand is exactly the named two-face
boundary sample. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_reflected_eq_complement
    (f : ZetaAdmissibleFunction) (n : ℕ)
    (hreflected :
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  let L : ℂ := zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n
  let T : ℂ := zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n
  have hsum : R + L = S :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_reflectedTimeBoundarySample_eq_timeSummand_of_reflected_eq_complement
      f n hreflected
  have hT : T = R + L :=
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_eq f n
  calc
    S = R + L := hsum.symm
    _ = T := hT.symm

/-- The reflected boundary sample is the arithmetic complement exactly when
the symmetric natural summand is the named two-face boundary sample. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_iff_timeSummand_eq_twoFaceBoundarySample
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n ↔
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
  constructor
  · intro hreflected
    exact
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_reflected_eq_complement
        f n hreflected
  · intro hsplit
    exact
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_twoFace
        f n hsplit

/-- The complementary natural-number prime contribution required for the
two-face prime recombination.

It is defined as the exact arithmetic difference between the symmetric
time-side prime contribution and the right one-sided contribution.  A later
left/reflected contour theorem should identify its analytic line value with
this contribution. -/
noncomputable def zetaCompletedExplicitFormulaPrimeNaturalComplementContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f -
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f

/-- The complementary natural contribution unfolds as symmetric minus right
one-sided. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementContribution_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
      zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f -
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f := by
  rfl

/-- Complementary natural contribution from a supplied `tsum_sub`
normalization of the pointwise complementary samples.

This theorem does not assert summability.  It isolates the purely arithmetic
transport from the analytic/summability fact that the `tsum` of pointwise
differences is the difference of the two natural prime `tsum`s. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementContribution_eq_tsum_of_tsum_sub
    (f : ZetaAdmissibleFunction)
    (htsum_sub :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) -
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
  calc
    zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
        zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f := by
      rfl
    _ =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f := by
      exact congrArg
        (fun z : ℂ =>
          z - zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f)
        (zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_tsum f)
    _ =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) -
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
      exact congrArg
        (fun z : ℂ =>
          (∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) - z)
        (zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution_eq_tsum f)
    _ =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n -
            zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
      exact htsum_sub.symm
    _ =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
      exact tsum_congr
        (fun n : ℕ =>
          (zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_eq
            f n).symm)

/-- `tsum` normalization in the orientation consumed by reflected prime
Mellin inversion. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_tsum_eq_contribution_of_tsum_sub
    (f : ZetaAdmissibleFunction)
    (htsum_sub :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) =
        (∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) -
          ∑' n : ℕ,
            zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n) :
    (∑' n : ℕ,
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
      zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f := by
  exact
    (zetaCompletedExplicitFormulaPrimeNaturalComplementContribution_eq_tsum_of_tsum_sub
      f htsum_sub).symm

/-- Complementary natural contribution from summability of the symmetric and
right one-sided natural prime series.

This is the standard `tsum_sub` specialization for the arithmetic complement
definition.  The analytic content is exactly the two summability hypotheses;
the rest is bookkeeping owned by this file. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementContribution_eq_tsum_of_summable
    (f : ZetaAdmissibleFunction)
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n)) :
    zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
      ∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
  exact
    zetaCompletedExplicitFormulaPrimeNaturalComplementContribution_eq_tsum_of_tsum_sub
      f
      (tsum_sub hsymmetric honeSided)

/-- `tsum` normalization in the orientation consumed by reflected prime
Mellin inversion, from summability of the symmetric and right one-sided
natural prime series. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_tsum_eq_contribution_of_summable
    (f : ZetaAdmissibleFunction)
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n)) :
    (∑' n : ℕ,
      zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
      zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f := by
  exact
    (zetaCompletedExplicitFormulaPrimeNaturalComplementContribution_eq_tsum_of_summable
      f hsymmetric honeSided).symm

/-- A pointwise reflected/complement normalization identifies the reflected
boundary contribution with the arithmetic complementary contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_complementContribution_of_reflected_eq_complement
    (f : ZetaAdmissibleFunction)
    (hreflected :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f =
      zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f := by
  have htsum :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n) =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n :=
    tsum_congr hreflected
  have hcomplement :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f :=
    zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_tsum_eq_contribution_of_summable
      f
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable f)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f)
  calc
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n := by
      rfl
    _ =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n := by
      exact htsum
    _ = zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f := by
      exact hcomplement

/-- A pointwise two-face decomposition identifies the reflected boundary
contribution with the arithmetic complementary contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_complementContribution_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction)
    (hsplit :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f =
      zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f := by
  exact
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_complementContribution_of_reflected_eq_complement
      f
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_twoFace
          f n (hsplit n))

/-- The negative complementary contribution is the right one-sided natural
contribution minus the symmetric natural prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_neg_complementContribution_eq_oneSided_sub_symmetric
    (f : ZetaAdmissibleFunction) :
    -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f -
        zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f
  change -(S - R) = R - S
  calc
    -(S - R) = -(S + -R) := by
      exact congrArg Neg.neg (sub_eq_add_neg S R)
    _ = -S + -(-R) := by
      exact neg_add S (-R)
    _ = -S + R := by
      exact congrArg (fun z : ℂ => -S + z) (neg_neg R)
    _ = R + -S := by
      exact add_comm (-S) R
    _ = R - S := by
      exact (sub_eq_add_neg R S).symm

/-- Arithmetic recombination of the right one-sided natural contribution with
its complementary contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
      zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f := by
  let R : ℂ := zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f
  let S : ℂ := zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f
  change R + (S - R) = S
  calc
    R + (S - R) = R + (S + -R) := by
      exact congrArg (fun z : ℂ => R + z) (sub_eq_add_neg S R)
    _ = R + (-R + S) := by
      exact congrArg (fun z : ℂ => R + z) (add_comm S (-R))
    _ = (R + -R) + S := by
      exact (add_assoc R (-R) S).symm
    _ = 0 + S := by
      exact congrArg (fun z : ℂ => z + S) (add_right_neg R)
    _ = S := by
      exact zero_add S

/-- The raw prime-power time-side summand. -/
noncomputable def zetaCompletedExplicitFormulaPrimePowerTimeSummand
    (f : ZetaAdmissibleFunction) (ι : ZetaPrimePowerIndex) : ℂ :=
  -(ZetaPrimePowerIndex.weight ι *
    Complex.re
      (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
        star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))

/-- The raw prime-power weight vanishes for non-genuine coordinates. -/
theorem zetaCompletedExplicitFormulaPrimePowerWeight_eq_zero_of_not_isGenuine
    {ι : ZetaPrimePowerIndex} (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    ZetaPrimePowerIndex.weight ι = 0 := by
  unfold ZetaPrimePowerIndex.weight
  unfold ZetaPrimePowerIndex.IsGenuine at hι
  by_cases hp : Nat.Prime ι.p
  · have hn : ¬ 1 ≤ ι.n := by
      intro hn
      exact hι ⟨hp, hn⟩
    have hinner :
        (if _hn : 1 ≤ ι.n then
          Real.log ι.p / Real.sqrt (ι.p ^ ι.n)
        else
          0) = 0 :=
      if_neg hn
    have houter :
        (if _hp : Nat.Prime ι.p then
          if _hn : 1 ≤ ι.n then
            Real.log ι.p / Real.sqrt (ι.p ^ ι.n)
          else
            0
        else
          0) =
        (if _hn : 1 ≤ ι.n then
          Real.log ι.p / Real.sqrt (ι.p ^ ι.n)
        else
          0) :=
      if_pos hp
    exact Eq.trans houter hinner
  · exact if_neg hp

/-- The raw prime-power time-side summand vanishes for non-genuine
coordinates. -/
theorem zetaCompletedExplicitFormulaPrimePowerTimeSummand_eq_zero_of_not_isGenuine
    (f : ZetaAdmissibleFunction) {ι : ZetaPrimePowerIndex}
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedExplicitFormulaPrimePowerTimeSummand f ι = 0 := by
  unfold zetaCompletedExplicitFormulaPrimePowerTimeSummand
  have hweight :
      ZetaPrimePowerIndex.weight ι = 0 :=
    zetaCompletedExplicitFormulaPrimePowerWeight_eq_zero_of_not_isGenuine
      hι
  calc
    (-(ZetaPrimePowerIndex.weight ι *
      Complex.re
        (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
          star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι)))) : ℂ) =
        (-(0 *
          Complex.re
            (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
              star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι)))) : ℂ) := by
      exact congrArg
        (fun w : ℝ =>
          (-(w *
            Complex.re
              (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
                star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι)))) : ℂ))
        hweight
    _ = 0 := by
      let R : ℝ :=
        Complex.re
          (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
            star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι)))
      have hmul : 0 * R = 0 :=
        zero_mul R
      have hneg : -(0 * R) = 0 :=
        Eq.trans (congrArg Neg.neg hmul) (neg_zero : -(0 : ℝ) = 0)
      exact congrArg (fun x : ℝ => (x : ℂ)) hneg

/-- The natural time-side summand vanishes away from prime powers. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_zero_of_not_isPrimePow
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : ¬ IsPrimePow n) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
  have hweight :
      zetaCompletedExplicitFormulaPrimeNaturalWeight n = 0 :=
    zetaCompletedExplicitFormulaPrimeNaturalWeight_eq_zero_of_not_isPrimePow hn
  calc
    (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
      Complex.re
        (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
          star
            (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
        (-(0 *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) := by
      exact congrArg
        (fun w : ℝ =>
          (-(w *
            Complex.re
              (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
                star
                  (zetaCompletedTimeBoundaryValue f
                    (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ))
        hweight
    _ = 0 := by
      let R : ℝ :=
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))
      have hmul : 0 * R = 0 :=
        zero_mul R
      have hneg : -(0 * R) = 0 :=
        Eq.trans (congrArg Neg.neg hmul) (neg_zero : -(0 : ℝ) = 0)
      exact congrArg (fun x : ℝ => (x : ℂ)) hneg

/-- The natural von Mangoldt time-side summand vanishes at zero. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f 0 = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
  calc
    (-(zetaCompletedExplicitFormulaPrimeNaturalWeight 0 *
      Complex.re
        (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter 0) +
          star
            (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))) : ℂ) =
        (-(0 *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter 0) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))) : ℂ) := by
      exact congrArg
        (fun w : ℝ =>
          (-(w *
            Complex.re
              (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter 0) +
                star
                  (zetaCompletedTimeBoundaryValue f
                    (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))) : ℂ))
        zetaCompletedExplicitFormulaPrimeNaturalWeight_zero
    _ = 0 := by
      let R : ℝ :=
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter 0) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter 0)))
      have hmul : 0 * R = 0 :=
        zero_mul R
      have hneg : -(0 * R) = 0 :=
        Eq.trans (congrArg Neg.neg hmul) (neg_zero : -(0 : ℝ) = 0)
      exact congrArg (fun x : ℝ => (x : ℂ)) hneg

/-- Nonzero two-face normalization from the exact scalar Hermitian boundary
identity at the natural logarithmic center.

This lemma is deliberately only scalar assembly: the input is the exact
Paley-Wiener/Hermitian time-boundary normalization needed to identify the
Mellin one-sided samples with the symmetric natural-time summand. -/
def zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian
    (f : ZetaAdmissibleFunction) : Prop :=
  ∀ n : ℕ, n ≠ 0 →
    (-( (Λ n / Real.sqrt n) *
      Complex.re
        (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
          star
            (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((2 * π : ℝ) •
            zetaCompletedTimeBoundaryValue f
              (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)))

theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_ne_zero_of_scalarHermitian
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0)
    (hscalar :
      (-( (Λ n / Real.sqrt n) *
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
  have htime :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_of_ne_zero f hn
  have htwo :
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) :=
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero
      f hn
  calc
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) := by
      exact htime
    _ =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
      exact hscalar
    _ = zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
      exact htwo.symm

/-- The scalar boundary normalization follows back from the nonzero
two-face normalization.

Together with
`zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_ne_zero_of_scalarHermitian`,
this records that the scalar condition is exactly the nonzero pointwise
content of the two-face natural-time normalization. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_scalarHermitian_of_ne_zero_of_timeSummand_eq_twoFaceBoundarySample
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0)
    (htwoFace :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
      (-( (Λ n / Real.sqrt n) *
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
  have htime :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_of_ne_zero f hn
  have htwo :
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) :=
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_of_ne_zero
      f hn
  calc
    (-( (Λ n / Real.sqrt n) *
      Complex.re
        (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
          star
            (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n := by
      exact htime.symm
    _ = zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
      exact htwoFace
    _ =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
      exact htwo

/-- At a nonzero natural index, the scalar boundary normalization is
equivalent to the two-face natural-time normalization. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_scalarHermitian_iff_timeSummand_eq_twoFaceBoundarySample_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
      (-( (Λ n / Real.sqrt n) *
        Complex.re
          (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
            star
              (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((2 * π : ℝ) •
              zetaCompletedTimeBoundaryValue f
                (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) ↔
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
  constructor
  · intro hscalar
    exact
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_ne_zero_of_scalarHermitian
        f hn hscalar
  · intro htwoFace
    exact
      zetaCompletedExplicitFormulaPrimeNatural_scalarHermitian_of_ne_zero_of_timeSummand_eq_twoFaceBoundarySample
        f hn htwoFace

/-- All-index two-face normalization from the nonzero scalar
boundary identity.

The zero index is discharged by the vanishing of the natural von Mangoldt
weight; every nonzero index is delegated to the scalar boundary
normalization. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_scalarHermitian
    (f : ZetaAdmissibleFunction)
    (hscalar :
      ∀ n : ℕ, n ≠ 0 →
        (-( (Λ n / Real.sqrt n) *
          Complex.re
            (zetaCompletedTimeBoundaryValue f
                (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
              star
                (zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) +
            ((Λ n / Real.sqrt n : ℝ) : ℂ) *
              ((2 * π : ℝ) •
                zetaCompletedTimeBoundaryValue f
                  (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) :
    ∀ n : ℕ,
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n := by
  intro n
  by_cases hn : n = 0
  · exact
      Eq.subst
        (motive := fun m : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f m =
            zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f m)
        hn.symm
        (Eq.trans
          (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_zero f)
          (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_zero
            f).symm)
  · exact
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_twoFaceBoundarySample_of_ne_zero_of_scalarHermitian
        f hn (hscalar n hn)

/-- All-index scalar boundary normalization from the two-face natural-time
normalization.

The scalar condition is only a nonzero-index statement, so the all-index
two-face hypothesis is consumed at each nonzero natural index. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian_of_timeSummand_eq_twoFaceBoundarySample
    (f : ZetaAdmissibleFunction)
    (htwoFace :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    zetaCompletedExplicitFormulaPrimeNaturalScalarHermitian f := by
  intro n hn
  exact
    zetaCompletedExplicitFormulaPrimeNatural_scalarHermitian_of_ne_zero_of_timeSummand_eq_twoFaceBoundarySample
      f hn (htwoFace n)

/-- A symmetric prime natural-time summand vanishes once its logarithmic center
lies above a support upper bound for the completed boundary source. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_zero_of_supportUpperBound_lt_log
    (f : ZetaAdmissibleFunction) {B : ℝ} {n : ℕ}
    (hB : ∀ x ∈ tsupport f.toZetaTestFunction', x ≤ B)
    (hn : B < Real.log n) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n = 0 := by
  have hcenter_log :
      zetaCompletedExplicitFormulaPrimeNaturalCenter n =
        Real.log n :=
    zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log n
  have hcenter_zero :
      zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) = 0 := by
    exact
      zetaCompletedTimeBoundaryValue_eq_zero_of_supportUpperBound_lt
        f hB
        (Eq.subst
          (motive := fun a : ℝ => B < a)
          hcenter_log.symm
          hn)
  unfold zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
  calc
    (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
      Complex.re
        (zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n) +
          star
            (zetaCompletedTimeBoundaryValue f
              (zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) : ℂ) =
        (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
          Complex.re ((0 : ℂ) + star (0 : ℂ))) : ℂ) := by
      exact congrArg
        (fun z : ℂ =>
          (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
            Complex.re (z + star z)) : ℂ))
        hcenter_zero
    _ =
        (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
          Complex.re ((0 : ℂ) + (0 : ℂ))) : ℂ) := by
      exact congrArg
        (fun z : ℂ =>
          (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
            Complex.re ((0 : ℂ) + z)) : ℂ))
        (star_zero : star (0 : ℂ) = 0)
    _ =
        (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
          Complex.re (0 : ℂ)) : ℂ) := by
      exact congrArg
        (fun z : ℂ =>
          (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n *
            Complex.re z) : ℂ))
        (zero_add (0 : ℂ))
    _ =
        (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n * 0) : ℂ) := by
      exact congrArg
        (fun r : ℝ =>
          (-(zetaCompletedExplicitFormulaPrimeNaturalWeight n * r) : ℂ))
        (Complex.zero_re)
    _ = 0 := by
      have hmul :
          zetaCompletedExplicitFormulaPrimeNaturalWeight n * 0 = 0 :=
        mul_zero (zetaCompletedExplicitFormulaPrimeNaturalWeight n)
      have hneg :
          -(zetaCompletedExplicitFormulaPrimeNaturalWeight n * 0) = 0 :=
        Eq.trans (congrArg Neg.neg hmul) (neg_zero : -(0 : ℝ) = 0)
      exact congrArg (fun r : ℝ => (r : ℂ)) hneg

/-- The symmetric prime natural-time summand vanishes for all sufficiently
large natural indices, explicitly bounded by the exponential ceiling of a
compact support bound. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_zero_of_supportCeil_lt
    (f : ZetaAdmissibleFunction) {B : ℝ} {n : ℕ}
    (hB : ∀ x ∈ tsupport f.toZetaTestFunction', x ≤ B)
    (hn : Nat.ceil (Real.exp B) < n) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n = 0 := by
  exact
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_zero_of_supportUpperBound_lt_log
      f hB
      (zetaCompletedExplicitFormulaPrimeNaturalSupportUpper_lt_log_of_ceil_lt
        hn)

/-- The symmetric natural-time summands have finite support, because the
admissible source is compactly supported and the centers are `log n`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_support_finite
    (f : ZetaAdmissibleFunction) :
    (Function.support
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n)).Finite := by
  obtain ⟨B, hB⟩ :=
    exists_zetaCompletedExplicitFormula_timeBoundarySupportUpperBound f
  let M : ℕ := Nat.ceil (Real.exp B)
  have hsubset :
      Function.support
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) ⊆
        Set.Iic M := by
    intro n hn
    by_contra hnot_le
    have hlt : M < n :=
      Nat.lt_of_not_ge hnot_le
    have hzero :
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n = 0 :=
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_zero_of_supportCeil_lt
        f hB hlt
    exact hn hzero
  exact
    Set.Finite.subset
      (by
        simpa only [Finset.coe_Iic] using
          (Finset.Iic M).finite_toSet)
      hsubset

/-- The symmetric natural-time summand series is summable; in fact it has
finite support. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) := by
  exact
    summable_of_finite_support
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_support_finite f)

/-- The zeroth complementary natural prime sample vanishes. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f 0 = 0 := by
  calc
    zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f 0 =
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f 0 -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0 := by
      rfl
    _ = 0 -
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0 := by
      exact congrArg
        (fun z : ℂ =>
          z - zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f 0)
        (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_zero f)
    _ = 0 - 0 := by
      exact congrArg
        (fun z : ℂ => 0 - z)
        (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_zero f)
    _ = 0 := by
      exact sub_self (0 : ℂ)

/-- The negative zeroth complementary natural prime sample also vanishes. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_neg_complementTimeSample_zero
    (f : ZetaAdmissibleFunction) :
    -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f 0) = 0 := by
  calc
    -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f 0) =
        -0 := by
      exact congrArg Neg.neg
        (zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_zero f)
    _ = 0 := by
      exact neg_zero

/-- At a genuine prime-power coordinate, the natural summand indexed by `p^k`
is exactly the raw prime-power summand. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_pow_eq_primePowerTimeSummand
    (f : ZetaAdmissibleFunction) {p k : ℕ}
    (hp : Nat.Prime p) (hk : 1 ≤ k) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f (p ^ k) =
      zetaCompletedExplicitFormulaPrimePowerTimeSummand f ⟨p, k⟩ := by
  unfold zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
  unfold zetaCompletedExplicitFormulaPrimePowerTimeSummand
  have hweight :
      zetaCompletedExplicitFormulaPrimeNaturalWeight (p ^ k) =
        ZetaPrimePowerIndex.weight ⟨p, k⟩ :=
    zetaCompletedExplicitFormulaPrimeNaturalWeight_pow_eq_primePowerWeight
      hp hk
  have hcenter :
      zetaCompletedExplicitFormulaPrimeNaturalCenter (p ^ k) =
        ZetaPrimePowerIndex.center ⟨p, k⟩ := by
    unfold ZetaPrimePowerIndex.center
    exact zetaCompletedExplicitFormulaPrimeNaturalCenter_pow_eq_primePowerCenter
      hp
  let naturalSample : ℂ :=
    zetaCompletedTimeBoundaryValue f
      (zetaCompletedExplicitFormulaPrimeNaturalCenter (p ^ k))
  let primePowerSample : ℂ :=
    zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ⟨p, k⟩)
  have hsample : naturalSample = primePowerSample :=
    congrArg (fun x : ℝ => zetaCompletedTimeBoundaryValue f x) hcenter
  have hsampleConj : star naturalSample = star primePowerSample :=
    congrArg star hsample
  have hreal :
      Complex.re (naturalSample + star naturalSample) =
        Complex.re (primePowerSample + star primePowerSample) :=
    congrArg Complex.re
      (congrArg₂ (fun a b : ℂ => a + b) hsample hsampleConj)
  exact
    congrArg (fun x : ℝ => (x : ℂ))
      (congrArg Neg.neg
        (congrArg₂ (fun a b : ℝ => a * b) hweight hreal))

/-- For a genuine raw prime-power coordinate, the natural summand at the
represented natural number agrees with the raw coordinate summand. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_toNat_eq_primePowerTimeSummand
    (f : ZetaAdmissibleFunction) {ι : ZetaPrimePowerIndex}
    (hι : ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f
        (zetaPrimePowerIndexToNat ι) =
      zetaCompletedExplicitFormulaPrimePowerTimeSummand f ι := by
  cases ι with
  | mk p k =>
      exact
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_pow_eq_primePowerTimeSummand
          f hι.1 hι.2

/-- Summand compatibility between the genuine raw-coordinate model and
mathlib's canonical prime-power subtype model. -/
theorem zetaCompletedExplicitFormulaPrimePowerTimeSummand_eq_naturalSubtypeSummand
    (f : ZetaAdmissibleFunction)
    (ι : {ι : ZetaPrimePowerIndex // ZetaPrimePowerIndex.IsGenuine ι}) :
    zetaCompletedExplicitFormulaPrimePowerTimeSummand f ι.1 =
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f
        (Nat.Primes.prodNatEquiv
          (zetaPrimePowerGenuineEquivPrimesNat ι)).1 := by
  have htoNat :
      zetaPrimePowerIndexToNat ι.1 =
        (Nat.Primes.prodNatEquiv
          (zetaPrimePowerGenuineEquivPrimesNat ι) : ℕ) :=
    zetaPrimePowerGenuineEquivPrimesNat_toNat ι
  have hnatural :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f
          (zetaPrimePowerIndexToNat ι.1) =
        zetaCompletedExplicitFormulaPrimePowerTimeSummand f ι.1 :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_toNat_eq_primePowerTimeSummand
      f ι.2
  exact
    Eq.trans
      hnatural.symm
      (congrArg
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n)
        htoNat)

/-- Owner arithmetic leaf: the natural-number von Mangoldt time-side
distribution reindexes exactly as the raw prime-power distribution.

This is the support theorem for `Λ`: the natural summand is zero away from
genuine prime powers, and for `n = p^k` its center is
`k * log p` and its weight is `log p / sqrt (p^k)`. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTimeTsum_eq_primePowerTsum_ownerArithmetic
    (f : ZetaAdmissibleFunction) :
    (∑' n : ℕ,
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) =
      ((∑' ι : ZetaPrimePowerIndex,
        -(ZetaPrimePowerIndex.weight ι *
          Complex.re
            (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
              star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))) : ℂ) := by
  let naturalSummand : ℕ → ℂ :=
    fun n => zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n
  let rawSummand : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedExplicitFormulaPrimePowerTimeSummand f ι
  have hnatural_support :
      Function.support naturalSummand ⊆
        {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hn_primePower
    have hzero :
        naturalSummand n = 0 :=
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_eq_zero_of_not_isPrimePow
        f hn_primePower
    exact hn hzero
  have hraw_support :
      Function.support rawSummand ⊆
        {ι : ZetaPrimePowerIndex | ZetaPrimePowerIndex.IsGenuine ι} := by
    intro ι hι
    by_contra hι_genuine
    have hzero :
        rawSummand ι = 0 :=
      zetaCompletedExplicitFormulaPrimePowerTimeSummand_eq_zero_of_not_isGenuine
        f hι_genuine
    exact hι hzero
  have hnatural_to_primePowers :
      (∑' n : ℕ, naturalSummand n) =
        ∑' n : {n : ℕ // IsPrimePow n}, naturalSummand n :=
    (tsum_subtype_eq_of_support_subset hnatural_support).symm
  have hprimePowers_to_pairs :
      (∑' n : {n : ℕ // IsPrimePow n}, naturalSummand n) =
        ∑' q : Nat.Primes × ℕ,
          naturalSummand (Nat.Primes.prodNatEquiv q) :=
    ((Nat.Primes.prodNatEquiv).tsum_eq
      (fun n : {n : ℕ // IsPrimePow n} => naturalSummand n)).symm
  have hpairs_to_genuine :
      (∑' q : Nat.Primes × ℕ,
          naturalSummand (Nat.Primes.prodNatEquiv q)) =
        ∑' ι : {ι : ZetaPrimePowerIndex //
            ZetaPrimePowerIndex.IsGenuine ι},
          naturalSummand
            (Nat.Primes.prodNatEquiv
              (zetaPrimePowerGenuineEquivPrimesNat ι)) :=
    (zetaPrimePowerGenuineEquivPrimesNat.tsum_eq
      (fun q : Nat.Primes × ℕ =>
        naturalSummand (Nat.Primes.prodNatEquiv q))).symm
  have hgenuine_to_raw_subtype :
      (∑' ι : {ι : ZetaPrimePowerIndex //
          ZetaPrimePowerIndex.IsGenuine ι},
        naturalSummand
          (Nat.Primes.prodNatEquiv
            (zetaPrimePowerGenuineEquivPrimesNat ι))) =
        ∑' ι : {ι : ZetaPrimePowerIndex //
            ZetaPrimePowerIndex.IsGenuine ι},
          rawSummand ι := by
    have hpointwise :
        (fun ι : {ι : ZetaPrimePowerIndex //
            ZetaPrimePowerIndex.IsGenuine ι} =>
          naturalSummand
            (Nat.Primes.prodNatEquiv
              (zetaPrimePowerGenuineEquivPrimesNat ι))) =
          fun ι : {ι : ZetaPrimePowerIndex //
              ZetaPrimePowerIndex.IsGenuine ι} =>
            rawSummand ι := by
      funext ι
      exact
        (zetaCompletedExplicitFormulaPrimePowerTimeSummand_eq_naturalSubtypeSummand
          f ι).symm
    exact congrArg
      (fun u : {ι : ZetaPrimePowerIndex //
          ZetaPrimePowerIndex.IsGenuine ι} → ℂ =>
        ∑' ι : {ι : ZetaPrimePowerIndex //
            ZetaPrimePowerIndex.IsGenuine ι}, u ι)
      hpointwise
  have hraw_subtype_to_raw :
      (∑' ι : {ι : ZetaPrimePowerIndex //
          ZetaPrimePowerIndex.IsGenuine ι},
        rawSummand ι) =
        ∑' ι : ZetaPrimePowerIndex, rawSummand ι :=
    tsum_subtype_eq_of_support_subset hraw_support
  have hraw_def :
      (∑' ι : ZetaPrimePowerIndex, rawSummand ι) =
        ((∑' ι : ZetaPrimePowerIndex,
          -(ZetaPrimePowerIndex.weight ι *
            Complex.re
              (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
                star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))) : ℂ) :=
    rfl
  calc
    (∑' n : ℕ,
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) =
        ∑' n : ℕ, naturalSummand n := by
      rfl
    _ = ∑' n : {n : ℕ // IsPrimePow n}, naturalSummand n :=
      hnatural_to_primePowers
    _ = ∑' q : Nat.Primes × ℕ,
          naturalSummand (Nat.Primes.prodNatEquiv q) :=
      hprimePowers_to_pairs
    _ = ∑' ι : {ι : ZetaPrimePowerIndex //
          ZetaPrimePowerIndex.IsGenuine ι},
        naturalSummand
          (Nat.Primes.prodNatEquiv
            (zetaPrimePowerGenuineEquivPrimesNat ι)) :=
      hpairs_to_genuine
    _ = ∑' ι : {ι : ZetaPrimePowerIndex //
          ZetaPrimePowerIndex.IsGenuine ι},
        rawSummand ι :=
      hgenuine_to_raw_subtype
    _ = ∑' ι : ZetaPrimePowerIndex, rawSummand ι :=
      hraw_subtype_to_raw
    _ = ((∑' ι : ZetaPrimePowerIndex,
          -(ZetaPrimePowerIndex.weight ι *
            Complex.re
              (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
                star (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι))))) : ℂ) :=
      hraw_def

/-- The symmetric natural-number von Mangoldt distribution is the public
completed prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_primeContribution
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  have hnatural :
      zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution f =
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n :=
    zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_tsum f
  have hreindex :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) =
        ((∑' ι : ZetaPrimePowerIndex,
          -(ZetaPrimePowerIndex.weight ι *
            Complex.re
              (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
                star (zetaCompletedTimeBoundaryValue f
                  (ZetaPrimePowerIndex.center ι))))) : ℂ) :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeTsum_eq_primePowerTsum_ownerArithmetic
      f
  have hprime :
      ((∑' ι : ZetaPrimePowerIndex,
          -(ZetaPrimePowerIndex.weight ι *
            Complex.re
              (zetaCompletedTimeBoundaryValue f (ZetaPrimePowerIndex.center ι) +
                star (zetaCompletedTimeBoundaryValue f
                  (ZetaPrimePowerIndex.center ι))))) : ℂ) =
        zetaCompletedExplicitFormulaPrimeContribution f := by
    exact zetaCompletedExplicitFormulaPrimePowerContribution_eq_primeContribution f
  exact Eq.trans hnatural (Eq.trans hreindex hprime)

/-- Arithmetic recombination of the right one-sided natural contribution with
its complementary contribution, normalized to the public prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution_eq_primeContribution
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedContribution f +
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f =
      zetaCompletedExplicitFormulaPrimeContribution f := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaPrimeNaturalOneSided_add_complementContribution f)
    (zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_primeContribution f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
