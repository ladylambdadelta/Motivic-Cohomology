import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.Part04_SharpComponentBounds

/-!
# Boundary growth sharp phase integral: global transport

This file is a semantic split of `BoundaryGrowth.OwnerParts.Part08_SharpPhaseIntegral`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Sharp finite zero-mean block estimate for the Bernoulli-weighted
logarithmic phase integral.

This is the finite cancellation form of the analytic sink: after the
one-interval Bernoulli mean has removed each left-endpoint phase, the remaining
sum is the exact object to be bounded by the logarithmic-phase
Dirichlet/Abel machinery. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerDirichlet
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_of_linear_and_remainder
      t ht hK

/-- Transport of the sharp finite zero-mean block estimate to the global
Bernoulli-weighted logarithmic phase integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerDirichlet
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  have hphase :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_sharp_ownerDirichlet
      t ht hK
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t)
      hphase

/-- Sharp endpoint/variation decomposition for the Bernoulli-weighted
logarithmic phase integral.

The true analytic input is
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerDirichlet`.
This theorem only splits the integral into two equal scalar halves. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_endpointVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        C + V ∧
      ‖C‖ ≤
        (Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) / 2 ∧
      ‖V‖ ≤
        (Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) / 2 := by
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + K)
  let C : ℂ := (1 / 2 : ℝ) • I
  let V : ℂ := (1 / 2 : ℝ) • I
  have hI : ‖I‖ ≤ A :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_single_sharp_ownerDirichlet
      t ht hK
  have hhalf_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) :=
    div_nonneg zero_le_one (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hhalf_norm : ‖(1 / 2 : ℝ)‖ = (1 / 2 : ℝ) :=
    Real.norm_of_nonneg hhalf_nonneg
  have hhalf_mul_A : (1 / 2 : ℝ) * A = A / 2 := by
    calc
      (1 / 2 : ℝ) * A = A * (1 / 2 : ℝ) := by
        exact mul_comm (1 / 2 : ℝ) A
      _ = A / 2 := by
        exact mul_one_div A 2
  have hhalf_smul_norm :
      ‖(1 / 2 : ℝ) • I‖ ≤ A / 2 := by
    have hnorm :
        ‖(1 / 2 : ℝ) • I‖ = ‖(1 / 2 : ℝ)‖ * ‖I‖ :=
      norm_smul (1 / 2 : ℝ) I
    have hscale :
        ‖(1 / 2 : ℝ)‖ * ‖I‖ ≤ (1 / 2 : ℝ) * A :=
      Eq.subst
        (motive := fun r : ℝ => r * ‖I‖ ≤ (1 / 2 : ℝ) * A)
        hhalf_norm.symm
        (mul_le_mul_of_nonneg_left hI hhalf_nonneg)
    exact
      Eq.subst
        (motive := fun r : ℝ => ‖(1 / 2 : ℝ) • I‖ ≤ r)
        hhalf_mul_A
        (Eq.subst
          (motive := fun r : ℝ => r ≤ (1 / 2 : ℝ) * A)
          hnorm.symm
          hscale)
  have hsplit : I = C + V := by
    have hhalves : (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
      (add_halves (1 : ℝ)).symm
    calc
      I = (1 : ℝ) • I := by
        exact (one_smul ℝ I).symm
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • I := by
        exact congrArg (fun r : ℝ => r • I) hhalves
      _ = (1 / 2 : ℝ) • I + (1 / 2 : ℝ) • I := by
        exact add_smul (1 / 2 : ℝ) (1 / 2 : ℝ) I
      _ = C + V := by
        rfl
  exact
    Exists.intro C
      (Exists.intro V
        ⟨hsplit, hhalf_smul_norm, hhalf_smul_norm⟩)

end LFunctions
end Boundary
