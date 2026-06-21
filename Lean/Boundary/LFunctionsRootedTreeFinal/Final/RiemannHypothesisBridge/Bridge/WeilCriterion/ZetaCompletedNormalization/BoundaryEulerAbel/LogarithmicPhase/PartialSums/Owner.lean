import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Core.Owner
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# Boundary logarithmic phase partial sums

This file owns the finite logarithmic-phase sums and elementary endpoint bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

def boundaryLineOnePointRealParam_logarithmicPhasePartialSum
    (t : ℝ)
    (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 M,
    (k : ℂ) ^ (-(t : ℂ) * Complex.I)

/-- Definitional expansion of the logarithmic-phase partial sum. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
    (t : ℝ)
    (M : ℕ) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      ∑ k ∈ Finset.Icc 0 M,
        (k : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rfl

/-- Trivial cardinality bound for logarithmic-phase partial sums. -/
theorem logarithmicPhasePartialSum_norm_le_card
    (t : ℝ)
    (M : ℕ) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤
      (M + 1 : ℝ) := by
  have hsum :
      ‖∑ k ∈ Finset.Icc 0 M, (k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤
        ∑ k ∈ Finset.Icc 0 M, ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
    norm_sum_le (Finset.Icc 0 M)
      (fun k : ℕ => (k : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hterms :
      (∑ k ∈ Finset.Icc 0 M, ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖) ≤
        ∑ k ∈ Finset.Icc 0 M, (1 : ℝ) := by
    exact Finset.sum_le_sum
      (fun k _hk => logarithmicPhase_nat_sample_norm_le_one t k)
  have hcard :
      (∑ k ∈ Finset.Icc 0 M, (1 : ℝ)) = (M + 1 : ℝ) := by
    have hsum_const :
        (∑ k ∈ Finset.Icc 0 M, (1 : ℝ)) =
          ((Finset.Icc 0 M).card • (1 : ℝ)) :=
      Finset.sum_const (1 : ℝ)
    have hnsmul_one :
        ((Finset.Icc 0 M).card • (1 : ℝ)) =
          (((Finset.Icc 0 M).card : ℕ) : ℝ) :=
      nsmul_one (Finset.Icc 0 M).card
    have hcard_nat :
        (Finset.Icc 0 M).card = M + 1 :=
      Nat.card_Icc 0 M
    have hcast_card :
        (((Finset.Icc 0 M).card : ℕ) : ℝ) = ((M + 1 : ℕ) : ℝ) :=
      congrArg (fun n : ℕ => (n : ℝ)) hcard_nat
    have hcast_one_real : ((1 : ℕ) : ℝ) = (1 : ℝ) :=
      show ((1 : ℕ) : ℝ) = (1 : ℝ) from Nat.cast_one
    have hcast_add_raw :
        ((M + 1 : ℕ) : ℝ) = (M : ℝ) + ((1 : ℕ) : ℝ) :=
      Nat.cast_add M 1
    have hcast_add :
        ((M + 1 : ℕ) : ℝ) = (M + 1 : ℝ) :=
      hcast_add_raw.trans
        (congrArg (fun x : ℝ => (M : ℝ) + x) hcast_one_real)
    calc
      (∑ k ∈ Finset.Icc 0 M, (1 : ℝ)) =
          ((Finset.Icc 0 M).card • (1 : ℝ)) :=
        hsum_const
      _ = (((Finset.Icc 0 M).card : ℕ) : ℝ) :=
        hnsmul_one
      _ = ((M + 1 : ℕ) : ℝ) :=
        hcast_card
      _ = (M + 1 : ℝ) :=
        hcast_add
  exact le_trans hsum (le_trans hterms (le_of_eq hcard))

/-- Reciprocal endpoint times the trivial cardinality bound is at most two. -/
theorem logarithmicPhase_endpoint_trivial_bound
    (t : ℝ)
    {M : ℕ}
    (hM : 1 ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ 2 := by
  have hfloor : ⌊((M : ℕ) : ℝ)⌋₊ = M :=
    Nat.floor_natCast M
  have hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ (M + 1 : ℝ) := by
    exact Eq.subst
      (motive := fun R : ℕ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t R‖ ≤
          (M + 1 : ℝ))
      hfloor.symm
      (logarithmicPhasePartialSum_norm_le_card t M)
  have hM_pos : 0 < M :=
    Nat.lt_of_succ_le hM
  have hM_real_pos : (0 : ℝ) < (M : ℝ) :=
    Nat.cast_pos.mpr hM_pos
  have hnorm_inv :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = (1 : ℝ) / (M : ℝ) := by
    have hnorm_real : ‖(((M : ℕ) : ℝ) : ℂ)‖ = (M : ℝ) := by
      have hnorm_cast :
          ‖(((M : ℕ) : ℝ) : ℂ)‖ = ‖((M : ℕ) : ℝ)‖ :=
        RCLike.norm_ofReal ((M : ℕ) : ℝ)
      have hreal_norm : ‖((M : ℕ) : ℝ)‖ = (M : ℝ) :=
        Real.norm_of_nonneg (Nat.cast_nonneg M)
      exact hnorm_cast.trans hreal_norm
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          (‖(((M : ℕ) : ℝ) : ℂ)‖)⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = ((M : ℝ))⁻¹ := by
        exact congrArg Inv.inv hnorm_real
      _ = (1 : ℝ) / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  have hmul_norm :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
        ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) := by
    have hnorm_mul :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ =
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ :=
      norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
        (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊)
    have hscaled :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
          ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) :=
      have hpartial_nonneg :
          0 ≤ ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ :=
        norm_nonneg
          (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊)
      have hinv_nonneg : 0 ≤ (1 : ℝ) / (M : ℝ) :=
        one_div_nonneg.mpr hM_real_pos.le
      mul_le_mul
        (le_of_eq hnorm_inv)
        hpartial
        hpartial_nonneg
        hinv_nonneg
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ))
      hnorm_mul.symm
      hscaled
  have hratio_le_two :
      ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) ≤ 2 := by
    have hM_plus_le : (M + 1 : ℝ) ≤ 2 * (M : ℝ) := by
      have hcast_one_real : ((1 : ℕ) : ℝ) = 1 :=
        show ((1 : ℕ) : ℝ) = (1 : ℝ) from Nat.cast_one
      have hone_le_M_real : (1 : ℝ) ≤ (M : ℝ) :=
        Eq.subst
          (motive := fun x : ℝ => x ≤ (M : ℝ))
          hcast_one_real
          (Nat.cast_le.mpr hM)
      calc
        (M + 1 : ℝ) = (M : ℝ) + 1 := by
          rfl
        _ ≤ (M : ℝ) + (M : ℝ) :=
          add_le_add_left hone_le_M_real (M : ℝ)
        _ = 2 * (M : ℝ) := by
          exact (two_mul (M : ℝ)).symm
    have hdiv_le : (M + 1 : ℝ) / (M : ℝ) ≤ 2 :=
      (div_le_iff₀ hM_real_pos).mpr hM_plus_le
    have hmul_eq : ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) =
        (M + 1 : ℝ) / (M : ℝ) := by
      calc
        ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) =
            (M + 1 : ℝ) * ((1 : ℝ) / (M : ℝ)) := by
          exact mul_comm ((1 : ℝ) / (M : ℝ)) (M + 1 : ℝ)
        _ = (M + 1 : ℝ) / (M : ℝ) := by
          exact mul_one_div (M + 1 : ℝ) (M : ℝ)
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      hmul_eq.symm
      hdiv_le
  exact le_trans hmul_norm hratio_le_two

/-- The logarithmic-phase derivative magnitude `|t| / u` is decreasing on the
positive real axis. -/
theorem logarithmicPhase_derivativeMagnitude_antitoneOn_positive
    (t : ℝ) :
    AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0) := by
  exact
    fun x hx y _hy hxy =>
      have hreciprocal : (1 : ℝ) / y ≤ (1 : ℝ) / x :=
        one_div_le_one_div_of_le (Set.mem_Ioi.mp hx) hxy
      have hnorm_nonneg : 0 ≤ ‖t‖ :=
        norm_nonneg t
      have hleft : ‖t‖ / y = ‖t‖ * ((1 : ℝ) / y) :=
        div_eq_mul_one_div ‖t‖ y
      have hright : ‖t‖ / x = ‖t‖ * ((1 : ℝ) / x) :=
        div_eq_mul_one_div ‖t‖ x
      Eq.subst
        (motive := fun target : ℝ => ‖t‖ / y ≤ target)
        hright.symm
        (Eq.subst
          (motive := fun source : ℝ => source ≤ ‖t‖ * ((1 : ℝ) / x))
          hleft.symm
          (mul_le_mul_of_nonneg_left hreciprocal hnorm_nonneg))
end
end LFunctions
end Boundary
