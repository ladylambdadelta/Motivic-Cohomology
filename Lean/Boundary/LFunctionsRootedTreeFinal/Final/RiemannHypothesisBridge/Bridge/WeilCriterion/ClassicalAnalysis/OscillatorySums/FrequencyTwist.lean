import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Frequency twists for real oscillatory phases

This file fixes the Fourier normalization used by the finite B-process.  For
the exponential convention `exp (I * φ(x))`, the integer Fourier mode `m`
subtracts `2π m x`, not merely `m x`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The `m`-th Fourier-frequency twist of a real phase. -/
def Complex.realPhaseFrequencyTwist
    (φ : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) : ℝ :=
  φ x - 2 * Real.pi * (m : ℝ) * x

/-- The real angular frequency attached to an integer Fourier mode. -/
def Real.integerAngularFrequency
    (m : ℤ) : ℝ :=
  2 * Real.pi * (m : ℝ)

/-- The frequency twist is phase minus angular frequency times position. -/
theorem Complex.realPhaseFrequencyTwist_eq_phase_sub_angularFrequency_mul
    (φ : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) :
    Complex.realPhaseFrequencyTwist φ m x =
      φ x - Real.integerAngularFrequency m * x :=
  Eq.refl (φ x - 2 * Real.pi * (m : ℝ) * x)

/-- Exact derivative of a Fourier-frequency twist. -/
theorem Complex.hasDerivAt_realPhaseFrequencyTwist
    {φ : ℝ → ℝ}
    {φ' x : ℝ}
    (m : ℤ)
    (hφ : HasDerivAt φ φ' x) :
    HasDerivAt
      (Complex.realPhaseFrequencyTwist φ m)
      (φ' - Real.integerAngularFrequency m)
      x := by
  have hlinear :
      HasDerivAt
        (fun y : ℝ => Real.integerAngularFrequency m * y)
        (Real.integerAngularFrequency m)
        x := by
    have hraw :
        HasDerivAt
          (fun y : ℝ => Real.integerAngularFrequency m * y)
          (Real.integerAngularFrequency m * 1)
          x :=
      (hasDerivAt_id x).const_mul (Real.integerAngularFrequency m)
    exact
      Eq.subst
        (motive := fun derivative : ℝ =>
          HasDerivAt
            (fun y : ℝ => Real.integerAngularFrequency m * y)
            derivative x)
        (mul_one (Real.integerAngularFrequency m))
        hraw
  show
    HasDerivAt
      (fun y : ℝ => φ y - Real.integerAngularFrequency m * y)
      (φ' - Real.integerAngularFrequency m)
      x
  have hdifference :
      HasDerivAt
        (fun y : ℝ => φ y - Real.integerAngularFrequency m * y)
        (φ' - Real.integerAngularFrequency m)
        x :=
    hφ.sub hlinear
  exact hdifference

/-- A point is stationary for mode `m` exactly when the original phase
derivative equals the angular frequency `2πm`. -/
theorem Complex.realPhaseFrequencyTwist_derivative_eq_zero_of_eq_angularFrequency
    {φ : ℝ → ℝ}
    {φ' x : ℝ}
    (m : ℤ)
    (hφ : HasDerivAt φ φ' x)
    (hstationary : φ' = Real.integerAngularFrequency m) :
    HasDerivAt
      (Complex.realPhaseFrequencyTwist φ m)
      0
      x := by
  have htwist :=
    Complex.hasDerivAt_realPhaseFrequencyTwist m hφ
  have hzero : φ' - Real.integerAngularFrequency m = 0 :=
    sub_eq_zero.mpr hstationary
  exact
    Eq.subst
      (motive := fun derivative : ℝ =>
        HasDerivAt
          (Complex.realPhaseFrequencyTwist φ m)
          derivative x)
      hzero
      htwist

/-- Integer sampling is unchanged by an integer Fourier-frequency twist. -/
theorem Complex.exp_I_realPhaseFrequencyTwist_nat_eq
    (φ : ℝ → ℝ)
    (m : ℤ)
    (n : ℕ) :
    Complex.exp
        (Complex.I *
          (Complex.realPhaseFrequencyTwist φ m n : ℂ)) =
      Complex.exp (Complex.I * (φ n : ℂ)) := by
  let mode : ℤ := m * (n : ℤ)
  have hphase_split :
      Complex.I *
          (Complex.realPhaseFrequencyTwist φ m n : ℂ) =
        Complex.I * (φ n : ℂ) +
          (-(mode : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
    have hmode_cast :
        (mode : ℂ) = (m : ℂ) * (n : ℂ) :=
      Int.cast_mul m (n : ℤ)
    have hn_cast : ((n : ℤ) : ℂ) = (n : ℂ) :=
      Int.cast_natCast n
    have hmode_normalized :
        (mode : ℂ) = (m : ℂ) * (n : ℂ) :=
      hmode_cast.trans
        (congrArg (fun value : ℂ => (m : ℂ) * value) hn_cast)
    have hfrequency_cast :
        (((2 : ℝ) * Real.pi * (m : ℝ) * (n : ℝ) : ℝ) : ℂ) =
          (2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ) := by
      have houter :=
        Complex.ofReal_mul
          ((2 : ℝ) * Real.pi * (m : ℝ))
          (n : ℝ)
      have hmiddle :=
        Complex.ofReal_mul
          ((2 : ℝ) * Real.pi)
          (m : ℝ)
      have hinner :=
        Complex.ofReal_mul (2 : ℝ) Real.pi
      have htwo : ((2 : ℝ) : ℂ) = (2 : ℂ) :=
        Complex.ofReal_ofNat 2
      have hm : (((m : ℤ) : ℝ) : ℂ) = (m : ℂ) :=
        Complex.ofReal_intCast m
      have hn : ((n : ℝ) : ℂ) = (n : ℂ) :=
        Complex.ofReal_natCast n
      exact
        houter.trans
          ((congrArg₂ (fun u v : ℂ => u * v)
            (hmiddle.trans
              (congrArg₂ (fun u v : ℂ => u * v)
                (hinner.trans
                  (congrArg₂ (fun u v : ℂ => u * v)
                    htwo (Eq.refl (Real.pi : ℂ))))
                hm))
            hn))
    have htwist_cast :
        (Complex.realPhaseFrequencyTwist φ m n : ℂ) =
          (φ n : ℂ) -
            (2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ) := by
      have hsub :=
        Complex.ofReal_sub
          (φ n)
          ((2 : ℝ) * Real.pi * (m : ℝ) * (n : ℝ))
      exact
        hsub.trans
          (congrArg₂ (fun u v : ℂ => u - v)
            (Eq.refl (φ n : ℂ)) hfrequency_cast)
    calc
      Complex.I *
          (Complex.realPhaseFrequencyTwist φ m n : ℂ) =
        Complex.I *
          ((φ n : ℂ) -
            (2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ)) :=
        congrArg (fun value : ℂ => Complex.I * value) htwist_cast
      _ = Complex.I * (φ n : ℂ) -
          Complex.I *
            ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ)) :=
        mul_sub Complex.I (φ n : ℂ)
          ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ))
      _ = Complex.I * (φ n : ℂ) +
          (-(mode : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
        have hfrequency_reorder :
            Complex.I *
                ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ)) =
              (mode : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
          calc
            Complex.I *
                ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ)) =
              (Complex.I *
                ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ))) * (n : ℂ) :=
              (mul_assoc Complex.I
                ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ))
                (n : ℂ)).symm
            _ = ((Complex.I * ((2 : ℂ) * (Real.pi : ℂ))) * (m : ℂ)) *
                (n : ℂ) :=
              congrArg
                (fun value : ℂ => value * (n : ℂ))
                (mul_assoc Complex.I
                  ((2 : ℂ) * (Real.pi : ℂ))
                  (m : ℂ)).symm
            _ = ((((2 : ℂ) * (Real.pi : ℂ)) * Complex.I) * (m : ℂ)) *
                (n : ℂ) :=
              congrArg
                (fun value : ℂ => (value * (m : ℂ)) * (n : ℂ))
                (mul_comm Complex.I ((2 : ℂ) * (Real.pi : ℂ)))
            _ = (((2 : ℂ) * (Real.pi : ℂ)) * Complex.I) *
                ((m : ℂ) * (n : ℂ)) :=
              mul_assoc
                (((2 : ℂ) * (Real.pi : ℂ)) * Complex.I)
                (m : ℂ) (n : ℂ)
            _ = ((m : ℂ) * (n : ℂ)) *
                ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) :=
              mul_comm
                (((2 : ℂ) * (Real.pi : ℂ)) * Complex.I)
                ((m : ℂ) * (n : ℂ))
            _ = (mode : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) :=
              congrArg
                (fun value : ℂ => value * (2 * (Real.pi : ℂ) * Complex.I))
                hmode_normalized.symm
        calc
          Complex.I * (φ n : ℂ) -
              Complex.I *
                ((2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * (n : ℂ)) =
            Complex.I * (φ n : ℂ) -
              (mode : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) :=
            congrArg
              (fun value : ℂ => Complex.I * (φ n : ℂ) - value)
              hfrequency_reorder
          _ = Complex.I * (φ n : ℂ) +
              (-((mode : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))) :=
            sub_eq_add_neg
              (Complex.I * (φ n : ℂ))
              ((mode : ℂ) * (2 * (Real.pi : ℂ) * Complex.I))
          _ = Complex.I * (φ n : ℂ) +
              (-(mode : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) :=
            congrArg
              (fun value : ℂ => Complex.I * (φ n : ℂ) + value)
              (neg_mul (mode : ℂ)
                (2 * (Real.pi : ℂ) * Complex.I)).symm
  have hexponential_split :
      Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist φ m n : ℂ)) =
        Complex.exp (Complex.I * (φ n : ℂ)) *
          Complex.exp
            ((-(mode : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)) :=
    (congrArg Complex.exp hphase_split).trans
      (Complex.exp_add
        (Complex.I * (φ n : ℂ))
        ((-(mode : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)))
  have hmode_exponential :
      Complex.exp
          ((-(mode : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    have hinteger_mode :
        Complex.exp
            (((-mode : ℤ) : ℂ) *
              (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
      Complex.exp_int_mul_two_pi_mul_I (-mode)
    have hnegative_cast : ((-mode : ℤ) : ℂ) = -(mode : ℂ) :=
      Int.cast_neg mode
    Eq.subst
      (motive := fun coefficient : ℂ =>
        Complex.exp
          (coefficient * (2 * (Real.pi : ℂ) * Complex.I)) = 1)
      hnegative_cast
      hinteger_mode
  exact
    hexponential_split.trans
      ((congrArg
        (fun value : ℂ =>
          Complex.exp (Complex.I * (φ n : ℂ)) * value)
        hmode_exponential).trans
        (mul_one (Complex.exp (Complex.I * (φ n : ℂ)))))

end

end LFunctions
end Boundary
