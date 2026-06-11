import Boundary.LFunctions.TraceExpansionTransport
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic trace expansions: Euler layer

This file owns the Euler-specific derivative identities built on the
transport layer.
-/

open scoped BigOperators PowerSeries

namespace Boundary
namespace TraceExpansion

noncomputable section

variable {K : Type*} [Field K]

theorem mul_assoc_forward (a b c : K⟦X⟧) :
    (a * b) * c = a * (b * c) := by
  exact mul_assoc a b c

theorem mul_assoc_backward (a b c : K⟦X⟧) :
    a * (b * c) = (a * b) * c := by
  exact (mul_assoc a b c).symm

theorem mul_left_comm_assoc (a b c : K⟦X⟧) :
    a * (b * c) = b * (a * c) := by
  exact mul_left_comm a b c

theorem mul_middle_swap (a b c : K⟦X⟧) :
    (a * b) * c = b * (a * c) := by
  exact (mul_assoc_forward a b c).trans (mul_left_comm_assoc a b c)

theorem mul_reassociate_four_right (a b c d : K⟦X⟧) :
    ((a * b) * c) * d = a * (b * (c * d)) := by
  exact
    (mul_assoc_forward (a * b) c d).trans
      ((mul_assoc_forward a b (c * d)))

theorem mul_reassociate_left_factor_tail (a b c d : K⟦X⟧) :
    (a * b) * (c * d) = a * (c * (b * d)) := by
  exact (mul_assoc_forward a b (c * d)).trans
    (congrArg (fun t : K⟦X⟧ => a * t) (mul_left_comm_assoc b c d))

theorem mul_reassociate_left_factor_flat (a b c d : K⟦X⟧) :
    (a * b) * (c * d) = (a * (c * b)) * d := by
  exact
    (mul_reassociate_left_factor_tail a b c d).trans
      ((congrArg (fun t : K⟦X⟧ => a * t)
        (mul_assoc_backward c b d)).trans
        (mul_assoc_backward a (c * b) d))

theorem mul_reassociate_outer_flat (a b c d : K⟦X⟧) :
    (a * (b * c)) * d = a * ((b * c) * d) := by
  exact mul_assoc_forward a (b * c) d

theorem mul_reassociate_outer_to_nested (a b c d : K⟦X⟧) :
    (a * (b * c)) * d = a * (b * (c * d)) := by
  exact (mul_reassociate_outer_flat a b c d).trans
    (congrArg (fun t : K⟦X⟧ => a * t) (mul_assoc_forward b c d))

theorem mul_cancel_one_middle (a b : K⟦X⟧) :
    (a * 1) * b = a * b := by
  exact (mul_assoc_forward a 1 b).trans
    (congrArg (fun t : K⟦X⟧ => a * t) (one_mul b))

theorem mul_flatten_three (a b c : K⟦X⟧) :
    a * (b * c) = a * b * c := by
  exact mul_assoc_backward a b c

theorem natCast_add_one_eq_add_one
    [CharZero K] (r : ℕ) :
    ((r + 1 : ℕ) : K⟦X⟧) = (r : K⟦X⟧) + 1 := by
  exact Nat.cast_add_one r

theorem algebraMap_add_one_natCast
    [CharZero K] (r : ℕ) :
    (algebraMap K K⟦X⟧) (1 + (r : K)) = ((r + 1 : ℕ) : K⟦X⟧) := by
  have hmap :
      (algebraMap K K⟦X⟧) (1 + (r : K)) =
        (algebraMap K K⟦X⟧) 1 + (algebraMap K K⟦X⟧) (r : K) := by
    exact map_add (algebraMap K K⟦X⟧) 1 (r : K)
  have hone :
      (algebraMap K K⟦X⟧) 1 + (algebraMap K K⟦X⟧) (r : K) =
        (1 : K⟦X⟧) + (r : K⟦X⟧) := by
    exact congrArg (fun t : K⟦X⟧ => t + (algebraMap K K⟦X⟧) (r : K))
      (map_one (algebraMap K K⟦X⟧))
  have hcomm :
      (1 : K⟦X⟧) + (r : K⟦X⟧) = (r : K⟦X⟧) + 1 := by
    exact add_comm (1 : K⟦X⟧) (r : K⟦X⟧)
  have hcast : (r : K⟦X⟧) + 1 = ((r + 1 : ℕ) : K⟦X⟧) := by
    exact (Nat.cast_add_one r).symm
  exact hmap.trans (hone.trans (hcomm.trans hcast))

theorem algebraMap_add_one_natCast_inv
    [CharZero K] (r : ℕ) :
    (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹) =
      ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹ := by
  have hbase : ((r + 1 : ℕ) : K) = 1 + (r : K) := by
    have hsucc : ((r + 1 : ℕ) : K) = (r : K) + 1 := by
      exact Nat.cast_add_one r
    have hcomm : (r : K) + 1 = 1 + (r : K) := by
      exact add_comm (r : K) 1
    exact hsucc.trans hcomm
  have hmul :
      (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹) *
          (algebraMap K K⟦X⟧) (1 + (r : K)) = 1 := by
    have hmap :
        (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹) *
            (algebraMap K K⟦X⟧) (1 + (r : K)) =
          (algebraMap K K⟦X⟧)
            ((((r + 1 : ℕ) : K)⁻¹) * (1 + (r : K))) := by
      exact (map_mul (algebraMap K K⟦X⟧)
        (((r + 1 : ℕ) : K)⁻¹) (1 + (r : K))).symm
    have hscalarBase :
        (((r + 1 : ℕ) : K)⁻¹) * (1 + (r : K)) =
          (((r + 1 : ℕ) : K)⁻¹) * ((r + 1 : ℕ) : K) := by
      exact congrArg (fun t : K => (((r + 1 : ℕ) : K)⁻¹) * t) hbase.symm
    have hscalarCancel :
        (((r + 1 : ℕ) : K)⁻¹) * ((r + 1 : ℕ) : K) = 1 := by
      have hneNat : (r + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero r
      have hne : ((r + 1 : ℕ) : K) ≠ 0 := by
        exact_mod_cast hneNat
      exact inv_mul_cancel₀ hne
    have hscalar :
        (((r + 1 : ℕ) : K)⁻¹) * (1 + (r : K)) = 1 := by
      exact hscalarBase.trans hscalarCancel
    have hone :
        (algebraMap K K⟦X⟧)
            ((((r + 1 : ℕ) : K)⁻¹) * (1 + (r : K))) =
          (algebraMap K K⟦X⟧) 1 := by
      exact congrArg (algebraMap K K⟦X⟧) hscalar
    have hmapOne : (algebraMap K K⟦X⟧) 1 = 1 := by
      exact map_one (algebraMap K K⟦X⟧)
    exact hmap.trans (hone.trans hmapOne)
  have hnonzero :
      PowerSeries.constantCoeff K ((algebraMap K K⟦X⟧) (1 + (r : K))) ≠ 0 := by
    have hcc :
        PowerSeries.constantCoeff K ((algebraMap K K⟦X⟧) (1 + (r : K))) = 1 + (r : K) := by
      rfl
    intro hzero
    have hzero' : (r : K) + 1 = 0 := by
      have hcomm : (r : K) + 1 = 1 + (r : K) := by
        exact add_comm (r : K) 1
      have htarget : 1 + (r : K) = 0 := by
        exact hcc.symm.trans hzero
      exact hcomm.trans htarget
    exact (Nat.cast_add_one_ne_zero r) hzero'
  exact (PowerSeries.eq_inv_iff_mul_eq_one hnonzero).2 hmul

theorem shift_reassociate_transport_map
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) := by
  exact congrArg (fun t : K⟦X⟧ =>
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) * t) *
      (((r : K⟦X⟧) + 1) * (g ^ r * PowerSeries.derivative K g)))
    (algebraMap_add_one_natCast_inv (K := K) r)

theorem shift_reassociate_transport_assoc
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g))) =
      (((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) *
          (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹ *
            (g ^ r * PowerSeries.derivative K g)))) := by
  exact mul_reassociate_left_factor_tail
    ((-1 : K⟦X⟧) ^ (r + 1 + 1))
    (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)
    (((r : K⟦X⟧) + 1))
    (g ^ r * PowerSeries.derivative K g)

theorem shift_reassociate_transport_tail
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (g ^ r * PowerSeries.derivative K g) =
      ((r : K⟦X⟧) + 1) *
        (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹ *
          (g ^ r * PowerSeries.derivative K g)) := by
  exact mul_assoc_forward
    (((r : K⟦X⟧) + 1))
    (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)
    (g ^ r * PowerSeries.derivative K g)

theorem shift_reassociate_transport_flat
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)) *
        (g ^ r * PowerSeries.derivative K g)) =
      (((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) *
          (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹ *
            (g ^ r * PowerSeries.derivative K g)))) := by
  exact mul_reassociate_outer_to_nested
    ((-1 : K⟦X⟧) ^ (r + 1 + 1))
    (((r : K⟦X⟧) + 1))
    (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)
    (g ^ r * PowerSeries.derivative K g)

theorem shift_reassociate_transport_flat_left
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g))) =
      (((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)) *
          (g ^ r * PowerSeries.derivative K g) := by
  exact mul_reassociate_left_factor_flat
    ((-1 : K⟦X⟧) ^ (r + 1 + 1))
    (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)
    (((r : K⟦X⟧) + 1))
    (g ^ r * PowerSeries.derivative K g)

theorem natCast_add_one_inv_cancel
    [CharZero K] (r : ℕ) :
    ((r : K⟦X⟧) + 1) * (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) = 1 := by
  have hmap : (algebraMap K K⟦X⟧) (1 + (r : K)) = ((r + 1 : ℕ) : K⟦X⟧) := by
    exact algebraMap_add_one_natCast (K := K) r
  have hunit : ((r + 1 : ℕ) : K⟦X⟧) * (((r + 1 : ℕ) : K⟦X⟧)⁻¹) = 1 := by
    exact PowerSeries.mul_inv_cancel ((r + 1 : ℕ) : K⟦X⟧)
      (by exact_mod_cast Nat.cast_add_one_ne_zero r)
  have hleft :
      ((r : K⟦X⟧) + 1) * (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) =
        ((r + 1 : ℕ) : K⟦X⟧) * (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) := by
    exact congrArg (fun t : K⟦X⟧ => t * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)
      (Nat.cast_add_one r).symm
  have hright :
      ((r + 1 : ℕ) : K⟦X⟧) * (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) =
        ((r + 1 : ℕ) : K⟦X⟧) * (((r + 1 : ℕ) : K⟦X⟧)⁻¹) := by
    exact congrArg (fun t : K⟦X⟧ => ((r + 1 : ℕ) : K⟦X⟧) * t)
      (congrArg (fun t : K⟦X⟧ => t⁻¹) hmap)
  exact hleft.trans (hright.trans hunit)

theorem natCast_add_one_inv_cancel_core'
    [CharZero K] (r : ℕ) :
    ((r : K⟦X⟧) + 1) * (((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) = 1 := by
  exact natCast_add_one_inv_cancel (K := K) r

theorem negOne_sq_eq_one :
    (-1 : K⟦X⟧) ^ 2 = 1 := by
  have hpow :
      (-1 : K⟦X⟧) ^ 2 = (-1 : K⟦X⟧) * (-1 : K⟦X⟧) := by
    exact pow_two (-1 : K⟦X⟧)
  have hneg : (-1 : K⟦X⟧) * (-1 : K⟦X⟧) = 1 * 1 := by
    exact neg_mul_neg 1 1
  have hone : (1 : K⟦X⟧) * 1 = 1 := by
    exact one_mul 1
  exact hpow.trans (hneg.trans hone)

theorem negOne_pow_add_two_eq_self (n : ℕ) :
    (-1 : K⟦X⟧) ^ (n + 2) = (-1 : K⟦X⟧) ^ n := by
  have hsplit :
      (-1 : K⟦X⟧) ^ (n + 2) =
        (-1 : K⟦X⟧) ^ n * (-1 : K⟦X⟧) ^ 2 := by
    exact pow_add (-1 : K⟦X⟧) n 2
  have hsquare :
      (-1 : K⟦X⟧) ^ n * (-1 : K⟦X⟧) ^ 2 =
        (-1 : K⟦X⟧) ^ n * 1 := by
    exact congrArg (fun t : K⟦X⟧ => (-1 : K⟦X⟧) ^ n * t)
      (negOne_sq_eq_one (K := K))
  have hone : (-1 : K⟦X⟧) ^ n * 1 = (-1 : K⟦X⟧) ^ n := by
    exact mul_one ((-1 : K⟦X⟧) ^ n)
  exact hsplit.trans (hsquare.trans hone)

theorem negOne_pow_succ_succ
    [CharZero K] (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1 + 1)) = (-1 : K⟦X⟧) ^ (r + 1) := by
  exact negOne_pow_add_two_eq_self (K := K) (r + 1)

theorem negOne_pow_add_two
    [CharZero K] (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1)) = (-1 : K⟦X⟧) ^ r := by
  exact negOne_pow_add_two_eq_self (K := K) r

theorem scalar_derivative_normalization_map
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (algebraMap K K⟦X⟧
      (((-1 : K) ^ (r + 1 + 1)) * ((r + 1 : ℕ) : K)⁻¹)) *
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        PowerSeries.derivative K (g ^ (r + 1)) := by
  have hpow : (algebraMap K K⟦X⟧) ((-1 : K) ^ (r + 1 + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) := by
    have hmapPow :
        (algebraMap K K⟦X⟧) ((-1 : K) ^ (r + 1 + 1)) =
          ((algebraMap K K⟦X⟧) (-1 : K)) ^ (r + 1 + 1) := by
      exact map_pow (algebraMap K K⟦X⟧) (-1 : K) (r + 1 + 1)
    have hmapNeg :
        (algebraMap K K⟦X⟧) (-1 : K) = -((algebraMap K K⟦X⟧) (1 : K)) := by
      exact map_neg (algebraMap K K⟦X⟧) (1 : K)
    have hnegOne :
        -((algebraMap K K⟦X⟧) (1 : K)) = (-1 : K⟦X⟧) := by
      exact congrArg Neg.neg (map_one (algebraMap K K⟦X⟧))
    have hbase :
        (algebraMap K K⟦X⟧) (-1 : K) = (-1 : K⟦X⟧) := by
      exact hmapNeg.trans hnegOne
    have hpowBase :
        ((algebraMap K K⟦X⟧) (-1 : K)) ^ (r + 1 + 1) =
          ((-1 : K⟦X⟧) ^ (r + 1 + 1)) := by
      exact congrArg (fun t : K⟦X⟧ => t ^ (r + 1 + 1)) hbase
    exact hmapPow.trans hpowBase
  have hmapMul :
      (algebraMap K K⟦X⟧
        (((-1 : K) ^ (r + 1 + 1)) * ((r + 1 : ℕ) : K)⁻¹)) *
          PowerSeries.derivative K (g ^ (r + 1)) =
        ((algebraMap K K⟦X⟧) ((-1 : K) ^ (r + 1 + 1)) *
          (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
            PowerSeries.derivative K (g ^ (r + 1)) := by
    exact congrArg (fun t : K⟦X⟧ => t * PowerSeries.derivative K (g ^ (r + 1)))
      (map_mul (algebraMap K K⟦X⟧)
        (((-1 : K) ^ (r + 1 + 1)) : K) (((r + 1 : ℕ) : K)⁻¹))
  have hpowTransport :
      ((algebraMap K K⟦X⟧) ((-1 : K) ^ (r + 1 + 1)) *
          (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
            PowerSeries.derivative K (g ^ (r + 1)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
          (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
            PowerSeries.derivative K (g ^ (r + 1)) := by
    exact congrArg (fun t : K⟦X⟧ => t * PowerSeries.derivative K (g ^ (r + 1)))
      (congrArg (fun t : K⟦X⟧ => t * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹))
        hpow)
  exact hmapMul.trans hpowTransport

theorem scalar_derivative_normalization
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        PowerSeries.derivative K (g ^ (r + 1)) := by
  have hsmul :
      ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
          PowerSeries.derivative K (g ^ (r + 1)) =
        (algebraMap K K⟦X⟧
          (((-1 : K) ^ (r + 1 + 1)) * ((r + 1 : ℕ) : K)⁻¹)) *
            PowerSeries.derivative K (g ^ (r + 1)) := by
    have hsmulDef :
        ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
            PowerSeries.derivative K (g ^ (r + 1)) =
          (algebraMap K K⟦X⟧
            (((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)))) *
              PowerSeries.derivative K (g ^ (r + 1)) := by
      exact Algebra.smul_def _ _
    have hdiv :
        (algebraMap K K⟦X⟧
            (((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)))) *
              PowerSeries.derivative K (g ^ (r + 1)) =
          (algebraMap K K⟦X⟧
            (((-1 : K) ^ (r + 1 + 1)) * ((r + 1 : ℕ) : K)⁻¹)) *
              PowerSeries.derivative K (g ^ (r + 1)) := by
      exact congrArg (fun t : K⟦X⟧ => t * PowerSeries.derivative K (g ^ (r + 1)))
        (congrArg (algebraMap K K⟦X⟧)
          (div_eq_mul_inv ((-1 : K) ^ (r + 1 + 1)) ((r + 1 : ℕ) : K)))
    exact hsmulDef.trans hdiv
  have hnormalize :
      (algebraMap K K⟦X⟧
        (((-1 : K) ^ (r + 1 + 1)) * ((r + 1 : ℕ) : K)⁻¹)) *
          PowerSeries.derivative K (g ^ (r + 1)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
          (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
          PowerSeries.derivative K (g ^ (r + 1)) := by
    exact scalar_derivative_normalization_map (K := K) g r
  exact hsmul.trans hnormalize

theorem negOne_pow_mul_with_derivative
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g =
      (-g) ^ r * PowerSeries.derivative K g := by
  have hpow : ((-1 : K⟦X⟧) ^ (r + 1 + 1)) = (-1 : K⟦X⟧) ^ r := by
    exact negOne_pow_add_two (K := K) r
  have hpowTransport :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g =
        (((-1 : K⟦X⟧) ^ r * g ^ r) * PowerSeries.derivative K g) := by
    exact congrArg (fun t : K⟦X⟧ => t * g ^ r * PowerSeries.derivative K g) hpow
  have hnegPow :
      (((-1 : K⟦X⟧) ^ r * g ^ r) * PowerSeries.derivative K g) =
        (-g) ^ r * PowerSeries.derivative K g := by
    exact congrArg (fun t : K⟦X⟧ => t * PowerSeries.derivative K g)
      ((neg_pow g r).symm)
  exact hpowTransport.trans hnegPow

theorem derivative_formalLog_term_leibniz_smul
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    PowerSeries.derivative K (g ^ (r + 1)) =
      ((r + 1 : ℕ) : K⟦X⟧) •
        (g ^ r • PowerSeries.derivative K g) := by
  have h := Derivation.leibniz_pow (D := PowerSeries.derivative K) (a := g) (n := r + 1)
  have hpow : g ^ (r + 1 - 1) = g ^ r := by
    exact congrArg (fun n => g ^ n) (Nat.succ_sub_one r)
  have hleibniz :
      PowerSeries.derivative K (g ^ (r + 1)) =
        (r + 1 : ℕ) • (g ^ (r + 1 - 1) • PowerSeries.derivative K g) := by
    exact h
  have hpow' :
      g ^ (r + 1 - 1) • PowerSeries.derivative K g =
        g ^ r • PowerSeries.derivative K g := by
    exact congrArg (fun t : K⟦X⟧ => t • PowerSeries.derivative K g) hpow
  have hcast :
      (r + 1 : ℕ) • (g ^ (r + 1 - 1) • PowerSeries.derivative K g) =
        ((r + 1 : ℕ) : K⟦X⟧) •
          (g ^ (r + 1 - 1) • PowerSeries.derivative K g) := by
    exact (Nat.cast_smul_eq_nsmul (R := K⟦X⟧) (r + 1)
      (g ^ (r + 1 - 1) • PowerSeries.derivative K g)).symm
  have hpowTransport :
      ((r + 1 : ℕ) : K⟦X⟧) •
          (g ^ (r + 1 - 1) • PowerSeries.derivative K g) =
        ((r + 1 : ℕ) : K⟦X⟧) • (g ^ r • PowerSeries.derivative K g) := by
    exact congrArg (fun t : K⟦X⟧ => ((r + 1 : ℕ) : K⟦X⟧) • t) hpow'
  exact hleibniz.trans (hcast.trans hpowTransport)

theorem derivative_formalLog_term_leibniz
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    PowerSeries.derivative K (g ^ (r + 1)) =
      ((r + 1 : ℕ) : K⟦X⟧) *
        (g ^ r * PowerSeries.derivative K g) := by
  exact derivative_formalLog_term_leibniz_smul (K := K) g r

theorem derivative_formalLog_term_shift_reassociate_core'
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
  ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) := by
  have hmap :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) := by
    exact shift_reassociate_transport_map (K := K) g r
  have hflat :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) := by
    exact shift_reassociate_transport_flat_left (K := K) g r
  exact hmap.trans hflat

theorem derivative_formalLog_term_shift_core
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) := by
  exact derivative_formalLog_term_shift_reassociate_core' (K := K) g r

theorem derivative_formalLog_term_shift
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) := by
  exact derivative_formalLog_term_shift_reassociate_core' (K := K) g r

theorem derivative_formalLog_term_shift_reassociate
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) := by
  exact derivative_formalLog_term_shift_reassociate_core' (K := K) g r

theorem derivative_formalLog_term_cancel_unit
    [CharZero K] (r : ℕ) :
    (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) = 1 := by
  exact natCast_add_one_inv_cancel (K := K) r

theorem derivative_formalLog_term_cancel_left_mul
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * 1) *
        (g ^ r * PowerSeries.derivative K g) := by
  exact congrArg (fun t : K⟦X⟧ => ((-1 : K⟦X⟧) ^ (r + 1 + 1) * t) *
    (g ^ r * PowerSeries.derivative K g))
    (derivative_formalLog_term_cancel_unit (K := K) r)

theorem derivative_formalLog_term_cancel_left_mul_one
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) * 1) *
        (g ^ r * PowerSeries.derivative K g) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
  have hassoc :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * 1) *
        (g ^ r * PowerSeries.derivative K g) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
          (1 * (g ^ r * PowerSeries.derivative K g)) := by
    exact mul_assoc_forward
      ((-1 : K⟦X⟧) ^ (r + 1 + 1))
      1
      (g ^ r * PowerSeries.derivative K g)
  have hone :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
          (1 * (g ^ r * PowerSeries.derivative K g)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * (g ^ r * PowerSeries.derivative K g) := by
    exact congrArg
      (fun t : K⟦X⟧ => ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * t)
      (one_mul (g ^ r * PowerSeries.derivative K g))
  have hflat :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * (g ^ r * PowerSeries.derivative K g) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
    exact mul_assoc_backward
      ((-1 : K⟦X⟧) ^ (r + 1 + 1))
      (g ^ r)
      (PowerSeries.derivative K g)
  exact hassoc.trans (hone.trans hflat)

theorem derivative_formalLog_term_cancel
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    (((-1 : K⟦X⟧) ^ (r + 1 + 1) *
      (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)) *
        (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
  have hcancel :
      (((-1 : K⟦X⟧) ^ (r + 1 + 1) *
      (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹)) *
        (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * 1) *
        (g ^ r * PowerSeries.derivative K g) := by
    exact derivative_formalLog_term_cancel_left_mul (K := K) g r
  have hone :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * 1) *
        (g ^ r * PowerSeries.derivative K g) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
    exact derivative_formalLog_term_cancel_left_mul_one (K := K) g r
  exact hcancel.trans hone

theorem derivative_formalLog_term_normalize
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          ((algebraMap K⟦X⟧ K⟦X⟧) g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
  have hcoeff :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
          (((r : K⟦X⟧) + 1) *
            ((algebraMap K⟦X⟧ K⟦X⟧) g ^ r * PowerSeries.derivative K g)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
          (((r : K⟦X⟧) + 1) * (g ^ r * PowerSeries.derivative K g)) := by
    exact congrArg
      (fun t : K⟦X⟧ =>
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
          (((r : K⟦X⟧) + 1) * t))
      (rfl : (algebraMap K⟦X⟧ K⟦X⟧) g ^ r * PowerSeries.derivative K g =
        g ^ r * PowerSeries.derivative K g)
  have hmap :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) (((r + 1 : ℕ) : K)⁻¹)) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) := by
    exact shift_reassociate_transport_map (K := K) g r
  have hflat :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) := by
    exact shift_reassociate_transport_flat_left (K := K) g r
  have hcancel :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
        (((r : K⟦X⟧) + 1) * ((algebraMap K K⟦X⟧) (1 + (r : K)))⁻¹) *
          (g ^ r * PowerSeries.derivative K g) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
    exact derivative_formalLog_term_cancel (K := K) g r
  exact hcoeff.trans (hmap.trans (hflat.trans hcancel))

theorem derivative_formalLog_term_coe_normalize
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        PowerSeries.derivative K (g ^ (r + 1)) := by
  exact scalar_derivative_normalization (K := K) g r

theorem derivative_formalLog_term_mid_step_reassociate_core'
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) := by
  have hleib :
      PowerSeries.derivative K (g ^ (r + 1)) =
        ((r + 1 : ℕ) : K⟦X⟧) *
          (g ^ r * PowerSeries.derivative K g) := by
    exact derivative_formalLog_term_leibniz (K := K) g r
  have hcast :
      ((r + 1 : ℕ) : K⟦X⟧) = ((r : K⟦X⟧) + 1) := by
    exact natCast_add_one_eq_add_one (K := K) r
  have hleib' :
      PowerSeries.derivative K (g ^ (r + 1)) =
        (((r : K⟦X⟧) + 1) * (g ^ r * PowerSeries.derivative K g)) := by
    exact hleib.trans (congrArg (fun t : K⟦X⟧ => t * (g ^ r * PowerSeries.derivative K g)) hcast)
  exact congrArg (fun t : K⟦X⟧ =>
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
      (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) * t) hleib'

theorem derivative_formalLog_term_mid_step
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) := by
  exact derivative_formalLog_term_mid_step_reassociate_core' (K := K) g r

theorem derivative_formalLog_term_mid_step_reassociate
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        (((r : K⟦X⟧) + 1) *
          (g ^ r * PowerSeries.derivative K g)) := by
  exact derivative_formalLog_term_mid_step_reassociate_core' (K := K) g r

theorem derivative_formalLog_term_mid
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
        PowerSeries.derivative K (g ^ (r + 1)) =
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
  have hcoe :
      ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
          PowerSeries.derivative K (g ^ (r + 1)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
          (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
          PowerSeries.derivative K (g ^ (r + 1)) := by
    exact derivative_formalLog_term_coe_normalize (K := K) g r
  have hmid :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
        (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
          PowerSeries.derivative K (g ^ (r + 1)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
          (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
          (((r : K⟦X⟧) + 1) *
            (g ^ r * PowerSeries.derivative K g)) := by
    exact derivative_formalLog_term_mid_step (K := K) g r
  have hnorm :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1) *
          (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
          (((r : K⟦X⟧) + 1) *
            (g ^ r * PowerSeries.derivative K g)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
    exact derivative_formalLog_term_normalize (K := K) g r
  exact hcoe.trans (hmid.trans hnorm)

theorem derivative_formalLog_term
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
        PowerSeries.derivative K (g ^ (r + 1)) =
      (-g) ^ r * PowerSeries.derivative K g := by
  have hmid :
      ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
          PowerSeries.derivative K (g ^ (r + 1)) =
        ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
    exact derivative_formalLog_term_mid (K := K) g r
  have hneg :
      ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g =
        (-g) ^ r * PowerSeries.derivative K g := by
    exact negOne_pow_mul_with_derivative (K := K) g r
  exact hmid.trans hneg

theorem constantCoeff_eq_one_of_coeff_zero_eq_one
    (f : K⟦X⟧) (h0 : PowerSeries.coeff K 0 f = 1) :
    PowerSeries.constantCoeff K f = 1 := by
  exact (PowerSeries.coeff_zero_eq_constantCoeff_apply f).symm.trans h0

theorem constantCoeff_sub_one_of_constantCoeff_eq_one
    (f : K⟦X⟧) (hf0 : PowerSeries.constantCoeff K f = 1) :
    PowerSeries.constantCoeff K (f - 1) = 0 := by
  have hsub :
      PowerSeries.constantCoeff K (f - 1) =
        PowerSeries.constantCoeff K f - PowerSeries.constantCoeff K (1 : K⟦X⟧) := by
    exact map_sub (PowerSeries.constantCoeff K) f 1
  have hleft :
      PowerSeries.constantCoeff K f - PowerSeries.constantCoeff K (1 : K⟦X⟧) =
        1 - PowerSeries.constantCoeff K (1 : K⟦X⟧) := by
    exact congrArg (fun t : K => t - PowerSeries.constantCoeff K (1 : K⟦X⟧)) hf0
  have hone :
      1 - PowerSeries.constantCoeff K (1 : K⟦X⟧) = 1 - 1 := by
    exact congrArg (fun t : K => (1 : K) - t) PowerSeries.constantCoeff_one
  have hzero : (1 : K) - 1 = 0 := by
    exact sub_self (1 : K)
  exact hsub.trans (hleft.trans (hone.trans hzero))

theorem constantCoeff_sub_one_eq_zero_of_coeff_zero_eq_one
    (f : K⟦X⟧) (h0 : PowerSeries.coeff K 0 f = 1) :
    PowerSeries.constantCoeff K (f - 1) = 0 := by
  exact constantCoeff_sub_one_of_constantCoeff_eq_one (K := K) f
    (constantCoeff_eq_one_of_coeff_zero_eq_one (K := K) f h0)

theorem coeff_derivative_mul_finiteGeomInverse_eq_coeff_derivative_mul_inv
    (f : K⟦X⟧) (n : ℕ)
    (hg : PowerSeries.constantCoeff K (f - 1) = 0) :
      PowerSeries.coeff K n
        (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) =
      PowerSeries.coeff K n (PowerSeries.derivative K f * f⁻¹) := by
  have hone_add : 1 + (f - 1) = f := by
    exact (add_comm (1 : K⟦X⟧) (f - 1)).trans (sub_add_cancel f 1)
  have hfinite :
      PowerSeries.coeff K n
          (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) =
        PowerSeries.coeff K n
          (PowerSeries.derivative K f * (1 + (f - 1))⁻¹) := by
    exact coeff_mul_finiteGeomInverse_eq_coeff_mul_inv
      (K := K) (g := f - 1) (q := PowerSeries.derivative K f)
      (N := n) (d := n) hg (Nat.lt_succ_self n)
  have hinv :
      PowerSeries.coeff K n
          (PowerSeries.derivative K f * (1 + (f - 1))⁻¹) =
        PowerSeries.coeff K n (PowerSeries.derivative K f * f⁻¹) := by
    exact congrArg
      (fun t : K⟦X⟧ => PowerSeries.coeff K n (PowerSeries.derivative K f * t⁻¹))
      hone_add
  exact hfinite.trans hinv

theorem coeff_scaled_derivative_pow_term
    (c : K) (p : K⟦X⟧) (n : ℕ) :
    c * PowerSeries.coeff K (n + 1) p * (n + 1 : K) =
      PowerSeries.coeff K n (c • PowerSeries.derivative K p) := by
  have hcoeff :
      PowerSeries.coeff K n (c • PowerSeries.derivative K p) =
        c • PowerSeries.coeff K n (PowerSeries.derivative K p) := by
    exact PowerSeries.coeff_smul n (PowerSeries.derivative K p) c
  have hderivative :
      c • PowerSeries.coeff K n (PowerSeries.derivative K p) =
        c • (PowerSeries.coeff K (n + 1) p * (n + 1 : K)) := by
    exact congrArg (fun t : K => c • t) (PowerSeries.coeff_derivative p n)
  have hmul :
      c • (PowerSeries.coeff K (n + 1) p * (n + 1 : K)) =
        c * PowerSeries.coeff K (n + 1) p * (n + 1 : K) := by
    exact (mul_assoc c (PowerSeries.coeff K (n + 1) p) (n + 1 : K)).symm
  exact (hcoeff.trans (hderivative.trans hmul)).symm

theorem derivative_sub_one_eq_derivative (f : K⟦X⟧) :
    PowerSeries.derivative K (f - 1) = PowerSeries.derivative K f := by
  have hsub :
      PowerSeries.derivative K (f - 1) =
        PowerSeries.derivative K f - PowerSeries.derivative K (1 : K⟦X⟧) := by
    exact (PowerSeries.derivative K).map_sub f 1
  have hone : PowerSeries.derivative K (1 : K⟦X⟧) = 0 := by
    exact (PowerSeries.derivative K).map_one_eq_zero
  have hzero :
      PowerSeries.derivative K f - PowerSeries.derivative K (1 : K⟦X⟧) =
        PowerSeries.derivative K f - 0 := by
    exact congrArg (fun t : K⟦X⟧ => PowerSeries.derivative K f - t) hone
  have hsubZero : PowerSeries.derivative K f - 0 = PowerSeries.derivative K f := by
    exact sub_zero (PowerSeries.derivative K f)
  exact hsub.trans (hzero.trans hsubZero)

theorem coeff_derivative_formalLog_eq_coeff_mul_finiteGeomInverse
    [CharZero K] (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K n
        (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) := by
  let scalarCoeff : ℕ → K := fun k => ((-1 : K) ^ (k + 1) / (k : K))
  have hterm :
      ∀ k ∈ Finset.range (n + 2),
        scalarCoeff k *
            PowerSeries.coeff K (n + 1) ((f - 1) ^ k) * (n + 1 : K) =
          PowerSeries.coeff K n
            (scalarCoeff k •
              PowerSeries.derivative K ((f - 1) ^ k)) := by
    intro k hk
    exact coeff_scaled_derivative_pow_term (K := K)
      (scalarCoeff k) ((f - 1) ^ k) n
  have hcoeffDerivative :
      PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
        PowerSeries.coeff K (n + 1) (formalLog f) * (n + 1 : K) := by
    exact coeff_derivative_formalLog f n
  have hcoeffLog :
      PowerSeries.coeff K (n + 1) (formalLog f) =
        ∑ k in Finset.range (n + 2),
          scalarCoeff k *
            PowerSeries.coeff K (n + 1) ((f - 1) ^ k) := by
    exact coeff_formalLog_of_ne_zero f (Nat.succ_ne_zero n)
  have hlogMul :
      PowerSeries.coeff K (n + 1) (formalLog f) * (n + 1 : K) =
        (∑ k in Finset.range (n + 2),
          scalarCoeff k *
            PowerSeries.coeff K (n + 1) ((f - 1) ^ k)) * (n + 1 : K) := by
    exact congrArg (fun t : K => t * (n + 1 : K)) hcoeffLog
  have hsumMul :
      (∑ k in Finset.range (n + 2),
          scalarCoeff k *
            PowerSeries.coeff K (n + 1) ((f - 1) ^ k)) * (n + 1 : K) =
      (∑ k in Finset.range (n + 2),
        scalarCoeff k *
          PowerSeries.coeff K (n + 1) ((f - 1) ^ k) * (n + 1 : K)) := by
    exact Finset.sum_mul
      (s := Finset.range (n + 2))
      (f := fun k =>
        scalarCoeff k *
          PowerSeries.coeff K (n + 1) ((f - 1) ^ k))
      (a := (n + 1 : K))
  have hsumTerm :
      (∑ k in Finset.range (n + 2),
        scalarCoeff k *
          PowerSeries.coeff K (n + 1) ((f - 1) ^ k) * (n + 1 : K)) =
      ∑ k in Finset.range (n + 2),
        PowerSeries.coeff K n
          (scalarCoeff k •
            PowerSeries.derivative K ((f - 1) ^ k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k hk
  have hmapSum :
      (∑ k in Finset.range (n + 2),
        PowerSeries.coeff K n
          (scalarCoeff k •
            PowerSeries.derivative K ((f - 1) ^ k))) =
      PowerSeries.coeff K n
        (∑ k in Finset.range (n + 2),
          scalarCoeff k •
            PowerSeries.derivative K ((f - 1) ^ k)) := by
    exact (map_sum (PowerSeries.coeff K n)
      (fun k =>
        scalarCoeff k •
          PowerSeries.derivative K ((f - 1) ^ k))
      (Finset.range (n + 2))).symm
  have hderive :
      (∑ k in Finset.range (n + 2),
          scalarCoeff k •
            PowerSeries.derivative K ((f - 1) ^ k)) =
        PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n := by
    let F : ℕ → K⟦X⟧ :=
      fun k => scalarCoeff k •
        PowerSeries.derivative K ((f - 1) ^ k)
    have hrange :
        (∑ k in Finset.range (n + 2),
            ((-1 : K) ^ (k + 1) / (k : K)) •
              PowerSeries.derivative K ((f - 1) ^ k)) =
          (∑ r in Finset.range (n + 1), F (r + 1)) + F 0 := by
      exact Finset.sum_range_succ' F (n + 1)
    have hpowZero : (f - 1) ^ (0 : ℕ) = (1 : K⟦X⟧) := by
      exact pow_zero (f - 1)
    have hderivativeZero :
        PowerSeries.derivative K ((f - 1) ^ (0 : ℕ)) =
          PowerSeries.derivative K (1 : K⟦X⟧) := by
      exact congrArg (PowerSeries.derivative K) hpowZero
    have honeDerivative : PowerSeries.derivative K (1 : K⟦X⟧) = 0 := by
      exact (PowerSeries.derivative K).map_one_eq_zero
    have hzeroDerivative :
        PowerSeries.derivative K ((f - 1) ^ (0 : ℕ)) = 0 := by
      exact hderivativeZero.trans honeDerivative
    have hzeroTerm :
        F 0 = 0 := by
      have hsmul :
          F 0 =
            (((-1 : K) ^ (0 + 1) / ((0 : ℕ) : K)) •
              (0 : K⟦X⟧)) := by
        exact congrArg
          (fun t : K⟦X⟧ =>
            (((-1 : K) ^ (0 + 1) / ((0 : ℕ) : K)) • t))
          hzeroDerivative
      have hsmulZero :
          (((-1 : K) ^ (0 + 1) / ((0 : ℕ) : K)) •
              (0 : K⟦X⟧)) = 0 := by
        exact smul_zero (((-1 : K) ^ (0 + 1) / ((0 : ℕ) : K)) : K)
      exact hsmul.trans hsmulZero
    have hdrop :
        (∑ r in Finset.range (n + 1), F (r + 1)) + F 0 =
          ∑ r in Finset.range (n + 1), F (r + 1) := by
      exact (congrArg (fun t : K⟦X⟧ => (∑ r in Finset.range (n + 1), F (r + 1)) + t)
        hzeroTerm).trans (add_zero (∑ r in Finset.range (n + 1), F (r + 1)))
    have htail :
        (∑ r in Finset.range (n + 1), F (r + 1)) =
          ∑ r in Finset.range (n + 1),
            PowerSeries.derivative K f * (-(f - 1)) ^ r := by
      exact Finset.sum_congr rfl
        (fun r _ =>
          let hterm :
              F (r + 1) =
                (-(f - 1)) ^ r * PowerSeries.derivative K (f - 1) :=
            derivative_formalLog_term (K := K) (g := f - 1) r
          let hderivative :
              (-(f - 1)) ^ r * PowerSeries.derivative K (f - 1) =
                (-(f - 1)) ^ r * PowerSeries.derivative K f :=
            congrArg (fun t : K⟦X⟧ => (-(f - 1)) ^ r * t)
              (derivative_sub_one_eq_derivative (K := K) f)
          let hcomm :
              (-(f - 1)) ^ r * PowerSeries.derivative K f =
                PowerSeries.derivative K f * (-(f - 1)) ^ r :=
            mul_comm ((-(f - 1)) ^ r) (PowerSeries.derivative K f)
          hterm.trans (hderivative.trans hcomm))
    have hmul :
        PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n =
          ∑ r in Finset.range (n + 1),
            PowerSeries.derivative K f * (-(f - 1)) ^ r := by
      exact Finset.mul_sum
        (s := Finset.range (n + 1))
        (f := fun r => (-(f - 1)) ^ r)
        (a := PowerSeries.derivative K f)
    exact hrange.trans (hdrop.trans (htail.trans hmul.symm))
  have hcoeffDerive :
      PowerSeries.coeff K n
        (∑ k in Finset.range (n + 2),
          ((-1 : K) ^ (k + 1) / (k : K)) •
            PowerSeries.derivative K ((f - 1) ^ k)) =
        PowerSeries.coeff K n
          (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) := by
    exact congrArg (PowerSeries.coeff K n) hderive
  exact hcoeffDerivative.trans
    (hlogMul.trans
      (hsumMul.trans
        (hsumTerm.trans
          (hmapSum.trans hcoeffDerive))))

theorem coeff_derivative_formalLog_to_finiteGeomInverse
    [CharZero K] (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K n
        (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) := by
  exact coeff_derivative_formalLog_eq_coeff_mul_finiteGeomInverse (K := K) f n

theorem coeff_derivative_formalLog_eq_coeff_derivative_mul_inv
    [CharZero K] (f : K⟦X⟧)
    (h0 : PowerSeries.coeff K 0 f = 1) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K n (PowerSeries.derivative K f * f⁻¹) := by
  have hfiniteLog :
      PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
        PowerSeries.coeff K n
          (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) := by
    exact coeff_derivative_formalLog_to_finiteGeomInverse (K := K) f n
  have hg : PowerSeries.constantCoeff K (f - 1) = 0 := by
    exact constantCoeff_sub_one_eq_zero_of_coeff_zero_eq_one (K := K) f h0
  have hfiniteInverse :
      PowerSeries.coeff K n
          (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) =
        PowerSeries.coeff K n (PowerSeries.derivative K f * f⁻¹) := by
    exact coeff_derivative_mul_finiteGeomInverse_eq_coeff_derivative_mul_inv
      (K := K) f n hg
  exact hfiniteLog.trans hfiniteInverse

theorem derivative_formalLog_eq_derivative_mul_inv
    [CharZero K] (f : K⟦X⟧)
    (h0 : PowerSeries.coeff K 0 f = 1) :
    PowerSeries.derivative K (formalLog f) =
      PowerSeries.derivative K f * f⁻¹ := by
  apply PowerSeries.ext
  intro n
  exact coeff_derivative_formalLog_eq_coeff_derivative_mul_inv
    (K := K) f h0 n

end

end TraceExpansion
end Boundary
