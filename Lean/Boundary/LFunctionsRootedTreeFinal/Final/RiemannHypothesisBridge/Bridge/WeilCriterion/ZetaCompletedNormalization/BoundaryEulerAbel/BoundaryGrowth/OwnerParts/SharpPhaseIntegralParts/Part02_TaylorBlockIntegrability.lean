import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.Part01_TaylorBlockDefinitions

/-!
# Boundary growth sharp phase integral: Taylor block integrability

This file is a semantic split of `BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Local integrability of the Taylor-linear summand in one Bernoulli-weighted
phase-increment block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinear_integrable
    (t : ℝ)
    (n : ℕ) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  let a : ℝ := ((((n - 1 : ℕ) : ℕ) : ℝ))
  let b : ℝ := (((n : ℕ) : ℝ))
  let c : ℂ :=
    (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
      (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hle : a ≤ b :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_kernel :
      ContinuousOn
        (fun x : ℝ => c * ((x : ℂ) - (a : ℂ)))
        (Set.Icc a b) :=
    continuousOn_const.mul
      (Complex.continuous_ofReal.continuousOn.sub continuousOn_const)
  have hkernel :
      IntegrableOn
        (fun x : ℝ => c * ((x : ℂ) - (a : ℂ)))
        (Set.Ioc a b)
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      hcont_kernel.intervalIntegrable
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ => c * ((x : ℂ) - (a : ℂ)))
      a b hkernel

/-- Local integrability of the nonlinear Taylor-remainder summand in one
Bernoulli-weighted phase-increment block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainder_integrable
    (t : ℝ)
    {K n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)) -
            ((((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  let a : ℝ := ((((n - 1 : ℕ) : ℕ) : ℝ))
  let b : ℝ := (((n : ℕ) : ℝ))
  let c : ℂ :=
    (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
      (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle : a ≤ b :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_phase :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc a b) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hcont_left_phase :
      ContinuousOn
        (fun _x : ℝ => (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc a b) :=
    continuousOn_const
  have hcont_linear :
      ContinuousOn
        (fun x : ℝ => c * ((x : ℂ) - (a : ℂ)))
        (Set.Icc a b) :=
    continuousOn_const.mul
      (Complex.continuous_ofReal.continuousOn.sub continuousOn_const)
  have hcont_kernel :
      ContinuousOn
        (fun x : ℝ =>
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
            (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            c * ((x : ℂ) - (a : ℂ)))
        (Set.Icc a b) :=
    (hcont_phase.sub hcont_left_phase).sub hcont_linear
  have hkernel :
      IntegrableOn
        (fun x : ℝ =>
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
            (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            c * ((x : ℂ) - (a : ℂ)))
        (Set.Ioc a b)
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      hcont_kernel.intervalIntegrable
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ =>
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          c * ((x : ℂ) - (a : ℂ)))
      a b hkernel

/-- One-block Taylor-linear/remainder integral split from the two local
integrability inputs. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_integral_add_remainder_integral_of_integrable
    (t : ℝ)
    (n : ℕ)
    (hlinear :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))
        (volume.restrict
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hremainder :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)) -
              ((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))))
        (volume.restrict
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))) +
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)) -
              ((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))) := by
  let s : Set ℝ := Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let L : ℝ → ℂ := fun x =>
    ((((-(t : ℂ) * Complex.I) /
        (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))) *
      ((x : ℂ) - (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))
  let R : ℝ → ℂ := fun x =>
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I)) -
      ((((-(t : ℂ) * Complex.I) /
          (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I))) *
        ((x : ℂ) - (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))
  have hcombined :
      (∫ x in s,
        B x *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) =
        ∫ x in s, B x * (L x + R x) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_add_remainder
      t n
  have hpoint :
      (fun x : ℝ => B x * (L x + R x)) =
        (fun x : ℝ => B x * L x + B x * R x) := by
    funext x
    exact mul_add (B x) (L x) (R x)
  have hsum_integral :
      (∫ x in s, B x * (L x + R x)) =
        (∫ x in s, B x * L x) + (∫ x in s, B x * R x) := by
    exact Eq.trans
      (congrArg (fun φ : ℝ → ℂ => ∫ x in s, φ x) hpoint)
      (integral_add hlinear hremainder)
  exact Eq.trans hcombined hsum_integral

/-- One-block Taylor-linear/remainder integral split for the Bernoulli-weighted
phase increment.

This is the local integrability sink underlying the finite block split: the
pointwise Taylor identity is already available, so the remaining local work is
to justify splitting the weighted integral into its linear and nonlinear
remainder pieces on `(n-1,n]`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_integral_add_remainder_integral
    (t : ℝ)
    {K n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))) +
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)) -
              ((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_integral_add_remainder_integral_of_integrable
      t n
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementLinear_integrable
        t n)
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementRemainder_integrable
        t hn)

end LFunctions
end Boundary
