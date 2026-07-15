import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.FourierIntegralInterchange
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.AmplitudeNonstationaryPhase
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Combined logarithmic and Fourier phase on a unit block

For a block with left endpoint `a`, Fourier mode `m`, and unit coordinate `u`,
the combined real phase is `2πmu - t log(a+u)`.  Past the canonical cutoff,
every nonzero mode is uniformly nonstationary.
-/

namespace Boundary
namespace LFunctions

noncomputable section

local notation "π" => Real.pi

/-- Combined real phase for a logarithmic oscillation and one Fourier mode on
the unit block with left endpoint `a`. -/
noncomputable def boundaryLineOnePointRealParam_unitBlockCombinedPhase
    (t : ℝ)
    (m : ℤ)
    (a : ℕ)
    (u : ℝ) : ℝ :=
  2 * π * (m : ℝ) * u - t * Real.log ((a : ℝ) + u)

/-- First derivative of the combined unit-block phase. -/
noncomputable def boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
    (t : ℝ)
    (m : ℤ)
    (a : ℕ)
    (u : ℝ) : ℝ :=
  2 * π * (m : ℝ) - t / ((a : ℝ) + u)

/-- Second derivative of the combined unit-block phase. -/
noncomputable def boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) : ℝ :=
  t / (((a : ℝ) + u) ^ (2 : ℕ))

/-- A unit coordinate on a post-cutoff block remains past the canonical
cutoff. -/
theorem boundaryLineOnePointRealParam_unitBlock_postCutoff_le_coordinate
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (a : ℝ) + u := by
  have hcast :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (a : ℝ) :=
    Nat.cast_le.mpr ha
  have ha_le : (a : ℝ) ≤ (a : ℝ) + u :=
    le_add_of_nonneg_right hu
  exact le_trans hcast ha_le

/-- Every point of a post-cutoff unit block is positive. -/
theorem boundaryLineOnePointRealParam_unitBlock_coordinate_pos
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    0 < (a : ℝ) + u := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_fourier_cutoff_pos t
  have hcutoff_real_pos :
      (0 : ℝ) < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hcutoff_pos
  exact lt_of_lt_of_le hcutoff_real_pos
    (boundaryLineOnePointRealParam_unitBlock_postCutoff_le_coordinate
      t ha hu)

/-- Uniform nonstationarity of a nonzero Fourier mode throughout every
post-cutoff unit block. -/
theorem boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative_abs_ge_one
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    (1 : ℝ) ≤
      |boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
        t m a u| := by
  have hx :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_postCutoff_le_coordinate
      t ha hu
  exact
    boundaryLineOnePointRealParam_postCutoff_fourierMode_phaseDerivative_abs_ge_one
      t hm hx

/-- The declared combined-phase derivative is the actual derivative on the
positive part of a unit block. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_unitBlockCombinedPhase
    (t : ℝ)
    (m : ℤ)
    (a : ℕ)
    {u : ℝ}
    (hx : 0 < (a : ℝ) + u) :
    HasDerivAt
      (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a)
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a u)
      u := by
  let angular : ℝ := 2 * π * (m : ℝ)
  let shifted : ℝ → ℝ := fun v => (a : ℝ) + v
  have hshiftRaw : HasDerivAt shifted (0 + 1) u :=
    (hasDerivAt_const u (a : ℝ)).add (hasDerivAt_id u)
  have hshift : HasDerivAt shifted 1 u :=
    hshiftRaw.congr_deriv (zero_add 1)
  have hlogBase :
      HasDerivAt Real.log (((a : ℝ) + u)⁻¹) ((a : ℝ) + u) :=
    Real.hasDerivAt_log (ne_of_gt hx)
  have hlogRaw :
      HasDerivAt
        (fun v : ℝ => Real.log ((a : ℝ) + v))
        ((((a : ℝ) + u)⁻¹) * 1)
        u :=
    hlogBase.comp u hshift
  have hinv_div : (((a : ℝ) + u)⁻¹) = 1 / ((a : ℝ) + u) :=
    (one_div ((a : ℝ) + u)).symm
  have hlogCoefficient :
      (((a : ℝ) + u)⁻¹) * 1 = 1 / ((a : ℝ) + u) :=
    Eq.trans (mul_one _) hinv_div
  have hlog :
      HasDerivAt
        (fun v : ℝ => Real.log ((a : ℝ) + v))
        (1 / ((a : ℝ) + u))
        u :=
    hlogRaw.congr_deriv hlogCoefficient
  have hlinearRaw :
      HasDerivAt (fun v : ℝ => angular * v) (angular * 1) u :=
    (hasDerivAt_id u).const_mul angular
  have hlinear :
      HasDerivAt (fun v : ℝ => angular * v) angular u :=
    hlinearRaw.congr_deriv (mul_one angular)
  have hlogScaled :
      HasDerivAt
        (fun v : ℝ => t * Real.log ((a : ℝ) + v))
        (t * (1 / ((a : ℝ) + u)))
        u :=
    hlog.const_mul t
  have hraw := hlinear.sub hlogScaled
  have hcoefficient :
      angular - t * (1 / ((a : ℝ) + u)) =
        2 * π * (m : ℝ) - t / ((a : ℝ) + u) := by
    have hangular : angular = 2 * π * (m : ℝ) :=
      rfl
    have hdivision :
        t * (1 / ((a : ℝ) + u)) = t / ((a : ℝ) + u) := by
      exact Eq.trans
        (congrArg (fun r : ℝ => t * r) (one_div ((a : ℝ) + u)))
        (div_eq_mul_inv t ((a : ℝ) + u)).symm
    exact congrArg₂ Sub.sub hangular hdivision
  exact hraw.congr_deriv hcoefficient

/-- The declared second derivative differentiates the declared first
derivative on the positive part of a unit block. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
    (t : ℝ)
    (m : ℤ)
    (a : ℕ)
    {u : ℝ}
    (hx : 0 < (a : ℝ) + u) :
    HasDerivAt
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative t a u)
      u := by
  let shifted : ℝ → ℝ := fun v => (a : ℝ) + v
  let angular : ℝ := 2 * π * (m : ℝ)
  have hshiftRaw : HasDerivAt shifted (0 + 1) u :=
    (hasDerivAt_const u (a : ℝ)).add (hasDerivAt_id u)
  have hshift : HasDerivAt shifted 1 u :=
    hshiftRaw.congr_deriv (zero_add 1)
  have hreciprocalBase :
      HasDerivAt
        (fun x : ℝ => -t / x)
        (t / (((a : ℝ) + u) ^ (2 : ℕ)))
        ((a : ℝ) + u) := by
    let x : ℝ := (a : ℝ) + u
    have hinverse :
        HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ (2 : ℕ))⁻¹) x :=
      hasDerivAt_inv (ne_of_gt hx)
    have hscaled :
        HasDerivAt
          (fun y : ℝ => (-t) * y⁻¹)
          ((-t) * (-(x ^ (2 : ℕ))⁻¹))
          x :=
      hinverse.const_mul (-t)
    have hfunction :
        (fun y : ℝ => (-t) * y⁻¹) =
          (fun y : ℝ => -t / y) := by
      funext y
      exact (div_eq_mul_inv (-t) y).symm
    have hcoefficient :
        (-t) * (-(x ^ (2 : ℕ))⁻¹) = t / x ^ (2 : ℕ) := by
      exact Eq.trans
        (neg_mul_neg t (x ^ (2 : ℕ))⁻¹)
        (div_eq_mul_inv t (x ^ (2 : ℕ))).symm
    exact Eq.subst
      (motive := fun f : ℝ → ℝ =>
        HasDerivAt f (t / x ^ (2 : ℕ)) x)
      hfunction
      (hscaled.congr_deriv hcoefficient)
  have hreciprocalRaw :
      HasDerivAt
        (fun v : ℝ => -t / ((a : ℝ) + v))
        ((t / (((a : ℝ) + u) ^ (2 : ℕ))) * 1)
        u :=
    hreciprocalBase.comp u hshift
  have hreciprocal :
      HasDerivAt
        (fun v : ℝ => -t / ((a : ℝ) + v))
        (t / (((a : ℝ) + u) ^ (2 : ℕ)))
        u :=
    hreciprocalRaw.congr_deriv (mul_one _)
  have hconstant :
      HasDerivAt (fun _v : ℝ => angular) 0 u :=
    hasDerivAt_const u angular
  have hraw := hconstant.add hreciprocal
  have hnormalized :
      HasDerivAt
        (fun v : ℝ => angular + -t / ((a : ℝ) + v))
        (t / (((a : ℝ) + u) ^ (2 : ℕ)))
        u :=
    hraw.congr_deriv (zero_add _)
  have hfunction :
      (fun v : ℝ => angular + -t / ((a : ℝ) + v)) =
        boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a := by
    funext v
    have hangular : angular = 2 * π * (m : ℝ) :=
      rfl
    have hnegative :
        -t / ((a : ℝ) + v) = -(t / ((a : ℝ) + v)) :=
      neg_div ((a : ℝ) + v) t
    exact Eq.trans
      (congrArg₂ Add.add hangular hnegative)
      rfl
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      HasDerivAt f
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative
          t a u)
        u)
    hfunction
    hnormalized

end
end LFunctions
end Boundary
