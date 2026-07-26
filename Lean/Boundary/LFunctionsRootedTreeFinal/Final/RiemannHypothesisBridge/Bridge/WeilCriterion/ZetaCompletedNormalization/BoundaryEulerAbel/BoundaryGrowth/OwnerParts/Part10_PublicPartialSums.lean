import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part09_NormalizedKernelDirichlet

/-!
# Boundary growth owner part 10

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- Exact finite endpoint bookkeeping and public normalization for the
unweighted Dirichlet/Euler-Maclaurin package.

This assembles the finite prefix, the exact post-cutoff identity, the main
integral estimate, the two endpoint terms, and the Bernoulli remainder into the
`500`-constant public partial-sum surface. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_classicalDirichletAbel_package
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  intro x hx
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let M : ℕ := ⌊x⌋₊
  let A : ℝ := (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)
  have hC_nonneg : 0 ≤ ((C : ℕ) : ℝ) :=
    Nat.cast_nonneg C
  have hx_nonneg : 0 ≤ x :=
    le_trans hC_nonneg hx
  have hM : C ≤ M :=
    Nat.le_floor_iff hx_nonneg |>.mpr hx
  have hM_le_x : ((M : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx_nonneg
  have hprefix :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤
        400 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le
      t ht
  have hdecomp :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C +
          (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((C : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
                (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_eulerMaclaurin_decomposition_ownerGap
      t hM
  have hmain :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        2 * (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_mainIntegral_norm_le_ownerGap
      t ht hM
  have hendpoints :
      ‖(-(1 / 2 : ℂ) *
          ((((C : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
      t ht hM
  have hremainder :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        6 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_ownerGap
      t ht hM
  have hlog_C_le : Real.log (2 + C) ≤ Real.log (2 + x) := by
    have hleft_pos : 0 < 2 + ((C : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hC_nonneg)
    have harg_le : 2 + ((C : ℕ) : ℝ) ≤ 2 + x :=
      add_le_add_left hx 2
    exact Real.log_le_log hleft_pos harg_le
  have hlog_M_le : Real.log (2 + M) ≤ Real.log (2 + x) := by
    have hleft_pos : 0 < 2 + ((M : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right (Nat.cast_nonneg M))
    have harg_le : 2 + ((M : ℕ) : ℝ) ≤ 2 + x :=
      add_le_add_left hM_le_x 2
    exact Real.log_le_log hleft_pos harg_le
  have hlog_C_nonneg : 0 ≤ Real.log (2 + C) := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((C : ℕ) : ℝ) :=
      le_trans one_le_two (le_add_of_nonneg_right hC_nonneg)
    exact Real.log_nonneg hone_le_arg
  have hlog_M_nonneg : 0 ≤ Real.log (2 + M) := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((M : ℕ) : ℝ) :=
      le_trans one_le_two
        (le_add_of_nonneg_right (Nat.cast_nonneg M))
    exact Real.log_nonneg hone_le_arg
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hfactor_nonneg : 0 ≤ x / ‖t‖ + Real.sqrt (1 + ‖t‖) :=
    add_nonneg
      (div_nonneg hx_nonneg (norm_nonneg t))
      hsqrt_nonneg
  have hA_nonneg : 0 ≤ A := by
    have hlog_x_nonneg : 0 ≤ Real.log (2 + x) :=
      Real.log_nonneg
        (le_trans one_le_two
          (le_add_of_nonneg_right hx_nonneg))
    exact mul_nonneg hfactor_nonneg hlog_x_nonneg
  have hsqrt_le_factor :
      Real.sqrt (1 + ‖t‖) ≤ x / ‖t‖ + Real.sqrt (1 + ‖t‖) :=
    le_add_of_nonneg_left
      (div_nonneg hx_nonneg (norm_nonneg t))
  have hMfactor_le :
      ((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖) ≤
        x / ‖t‖ + Real.sqrt (1 + ‖t‖) := by
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact add_le_add_right
      (div_le_div_of_nonneg_right hM_le_x (le_of_lt ht_pos))
      (Real.sqrt (1 + ‖t‖))
  have hprefix_A :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤
        400 * A := by
    have hscale :
        Real.sqrt (1 + ‖t‖) * Real.log (2 + C) ≤ A := by
      exact
        Eq.subst
          (motive := fun r : ℝ =>
            Real.sqrt (1 + ‖t‖) * Real.log (2 + C) ≤ r)
          (show
            (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
          (mul_le_mul hsqrt_le_factor hlog_C_le hlog_C_nonneg hfactor_nonneg)
    exact le_trans hprefix
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 400 * A)
        (mul_assoc (400 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + C))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 400 from Nat.cast_nonneg 400)))
  have hmain_A :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        2 * A := by
    have hscale :
        (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + M) ≤ A :=
      Eq.subst
        (motive := fun r : ℝ =>
          (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + M) ≤ r)
        (show
          (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
        (mul_le_mul hMfactor_le hlog_M_le hlog_M_nonneg hfactor_nonneg)
    exact le_trans hmain
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 2 * A)
        (mul_assoc
          (2 : ℝ)
          (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
          (Real.log (2 + M))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 2 from zero_le_two)))
  have hendpoints_A :
      ‖(-(1 / 2 : ℂ) *
          ((((C : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))‖ ≤
        2 * A := by
    have hscale :
        Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ A :=
      Eq.subst
        (motive := fun r : ℝ =>
          Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ r)
        (show
          (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
        (mul_le_mul hsqrt_le_factor hlog_M_le hlog_M_nonneg hfactor_nonneg)
    exact le_trans hendpoints
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 2 * A)
        (mul_assoc (2 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 2 from zero_le_two)))
  have hremainder_A :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        6 * A := by
    have hscale :
        Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ A :=
      Eq.subst
        (motive := fun r : ℝ =>
          Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ r)
        (show
          (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
        (mul_le_mul hsqrt_le_factor hlog_M_le hlog_M_nonneg hfactor_nonneg)
    exact le_trans hremainder
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 6 * A)
        (mul_assoc (6 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 6 from Nat.cast_nonneg 6)))
  let P : ℂ := boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C
  let I : ℂ :=
    ∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    (-(1 / 2 : ℂ) *
      ((((C : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I)))
  let U : ℂ :=
    ((1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I)))
  let E : ℂ :=
    L + U
  let R : ℂ :=
    ∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hsum_bound :
      ‖P + I + E + R‖ ≤ (400 * A + 2 * A) + 2 * A + 6 * A := by
    have hfirst : ‖P + I‖ ≤ 400 * A + 2 * A :=
      le_trans (norm_add_le P I) (add_le_add hprefix_A hmain_A)
    have hsecond : ‖P + I + E‖ ≤ (400 * A + 2 * A) + 2 * A :=
      le_trans (norm_add_le (P + I) E) (add_le_add hfirst hendpoints_A)
    exact
      le_trans (norm_add_le (P + I + E) R)
        (add_le_add hsecond hremainder_A)
  have hconstant :
      (400 * A + 2 * A) + 2 * A + 6 * A ≤ 500 * A := by
    have hcastFourHundredTwo :
        ((400 + 2 : ℕ) : ℝ) = (400 : ℝ) + 2 :=
      Nat.cast_add 400 2
    have hcastFourHundredFour :
        (((400 + 2 : ℕ) + 2 : ℕ) : ℝ) =
          ((400 : ℝ) + 2) + 2 :=
      Eq.trans
        (Nat.cast_add (400 + 2) 2)
        (congrArg (fun y : ℝ => y + 2) hcastFourHundredTwo)
    have hcastFourHundredTen :
        ((((400 + 2 : ℕ) + 2) + 6 : ℕ) : ℝ) =
          (((400 : ℝ) + 2) + 2) + 6 :=
      Eq.trans
        (Nat.cast_add ((400 + 2) + 2) 6)
        (congrArg (fun y : ℝ => y + 6) hcastFourHundredFour)
    have hnaturalFourHundredTen :
        (((400 + 2 : ℕ) + 2) + 6) = 410 := rfl
    have hrealFourHundredTen :
        (((400 : ℝ) + 2) + 2) + 6 = 410 :=
      Eq.trans
        hcastFourHundredTen.symm
        (congrArg (fun n : ℕ => (n : ℝ)) hnaturalFourHundredTen)
    have hleft_eq : (400 * A + 2 * A) + 2 * A + 6 * A = 410 * A := by
      calc
        (400 * A + 2 * A) + 2 * A + 6 * A =
            ((400 + 2) * A + 2 * A) + 6 * A := by
          exact congrArg (fun y : ℝ => (y + 2 * A) + 6 * A)
            (add_mul 400 2 A).symm
        _ = (((400 + 2) + 2) * A) + 6 * A := by
          exact congrArg (fun y : ℝ => y + 6 * A)
            (add_mul (400 + 2) 2 A).symm
        _ = (((400 + 2) + 2) + 6) * A := by
          exact (add_mul ((400 + 2) + 2) 6 A).symm
        _ = 410 * A := by
          exact congrArg (fun y : ℝ => y * A) hrealFourHundredTen
    have hsum_le_public : (410 : ℝ) ≤ 500 :=
      Nat.cast_le.mpr
        (show (410 : ℕ) ≤ 500 from Nat.le_add_right 410 90)
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 500 * A)
      hleft_eq.symm
      (mul_le_mul_of_nonneg_right hsum_le_public hA_nonneg)
  have htarget :
      ‖P + I + E + R‖ ≤ 500 * A :=
    le_trans hsum_bound hconstant
  have hgrouped :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        P + I + E + R := by
    have hright_group :
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C +
            (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
            (-(1 / 2 : ℂ) *
              ((((C : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) +
            ((1 / 2 : ℂ) *
              ((((M : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) +
            (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
                (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
                  (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
          P + I + E + R := by
      exact
        calc
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C +
              (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
              (-(1 / 2 : ℂ) *
                ((((C : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) +
              ((1 / 2 : ℂ) *
                ((((M : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) +
              (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
                  (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
                    (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
            (P + I + L + U) + R := rfl
          _ = (P + I + (L + U)) + R := by
            exact congrArg (fun z : ℂ => z + R)
              (add_assoc (P + I) L U)
          _ = P + I + E + R := rfl
    exact Eq.trans hdecomp hright_group
  have htransported :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤
        500 * A :=
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 500 * A)
      hgrouped.symm
      htarget
  have hindexDefinition : M = ⌊x⌋₊ := rfl
  have hscaleDefinition :
      A = (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := rfl
  have hexpandedScale :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤
        500 * ((x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) :=
    Eq.subst
      (motive := fun scale : ℝ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤ 500 * scale)
      hscaleDefinition
      htransported
  have hreassociatedScale :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤
        500 * (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) :=
    Eq.subst
      (motive := fun bound : ℝ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤ bound)
      (mul_assoc
        (500 : ℝ)
        (x / ‖t‖ + Real.sqrt (1 + ‖t‖))
        (Real.log (2 + x))).symm
      hexpandedScale
  exact
    Eq.subst
      (motive := fun index : ℕ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t index‖ ≤
          500 * (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
      hindexDefinition
      hreassociatedScale

/-- Unconditional logarithmic-phase partial sums on the boundary line.

The former route through `logarithmicPhaseFiniteDifferenceHypothesis` was not
an honest owner proof: unrestricted real frequencies have exact resonances
among adjacent logarithmic increments, e.g. `t = -2π / log 2` makes the first
increment an integral multiple of `2π`.  The unconditional boundary-line
estimate must instead be proved by the classical Dirichlet/Abel or
Euler-Maclaurin argument for `∑ n^{-it}` with cutoff comparable to `|t|`;
cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5.
-/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_classicalDirichletAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_classicalDirichletAbel_package
      t ht

/-- Logarithmic-phase partial sums on the boundary line.

Proof chain:
classical Dirichlet/Abel oscillatory estimate for `∑ n^{-it}`
-> cutoff normalization at `⌊2 + |t|⌋₊`
-> this `500`-constant public boundary hypothesis.
-/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundOwner
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_classicalDirichletAbel
      t ht

/-- Uniformly bounded finite post-cutoff Abel tails on the boundary line.

This is the direct classical bounded-partial-sums input needed by Abel
transport.  The explicit finite Abel majorant above is useful for finite
decompositions, but its endpoint form is not uniformly absorbed by the fixed
Abel-tail constant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBoundedOwner
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded_of_classical_postCutoff_tail
      t ht

/-- Owner package for the real-parameter boundary-line truncation hypotheses. -/
theorem boundaryLineOnePointRealParam_verticalTruncationHypotheses
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t ∧
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t := by
  have hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundOwner t ht
  exact
    ⟨hpartial,
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBoundedOwner t ht⟩

/-- The complex boundary-line hypothesis is owned by the real-parameter
Abel-tail package.  This transport is deliberately explicit so the later
polynomial boundary-growth theorem does not carry an artificial hypothesis. -/
theorem boundaryLineOneVerticalTruncationHypotheses_owner
    (w : ℂ)
    (_hw : w.re = 1)
    (ht : 1 ≤ ‖w.im‖) :
    boundaryLineOneVerticalTruncationHypotheses w := by
  exact boundaryLineOnePointRealParam_verticalTruncationHypotheses w.im ht


end
end LFunctions
end Boundary
