import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianCutoffDerivativeBounds

/-!
# Uniform derivative L1 bounds for Gaussian cutoffs

Finite binomial derivative majorants are integrated term by term.  Translation
invariance removes the horizontal displacement, and completion of the square
provides one constant on the fixed horizontal strip.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- One horizontal Gaussian derivative has a uniform `L1` bound on a symmetric
strip. -/
theorem integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist_le_strip
    (order : ℕ)
    (scale x : ℝ)
    (hscale : 0 < scale)
    (hx : |x| ≤ scale) :
    (∫ t : ℝ,
        ‖iteratedDeriv order
          (physicalGaussianHorizontalTwist x) t‖) ≤
      Real.exp (scale ^ 2) *
        ∫ t : ℝ,
          ‖iteratedDeriv order realPhysicalGaussian t‖ := by
  have hexponential :=
    exp_halfSquare_le_exp_scaleSquare scale x hscale hx
  have hintegralNonnegative :
      0 ≤ ∫ t : ℝ,
        ‖iteratedDeriv order realPhysicalGaussian t‖ :=
    MeasureTheory.integral_nonneg
      (fun t : ℝ =>
        norm_nonneg (iteratedDeriv order realPhysicalGaussian t))
  have hscaled :=
    mul_le_mul_of_nonneg_right
      hexponential
      hintegralNonnegative
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        Real.exp (scale ^ 2) *
          ∫ t : ℝ,
            ‖iteratedDeriv order realPhysicalGaussian t‖)
    (integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist
      order x).symm
    hscaled

/-- The supplied-bound uniform `L1` majorant before adding a positive
margin. -/
noncomputable def admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
    (order : ℕ)
    (scale : ℝ)
    (bound : ℕ → ℝ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1),
    ((order.choose index : ℝ) * bound index) *
      (Real.exp (scale ^ 2) *
        ∫ t : ℝ,
          ‖iteratedDeriv (order - index) realPhysicalGaussian t‖)

/-- The supplied-bound raw uniform derivative bound is nonnegative. -/
theorem admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds_nonnegative
    (order : ℕ)
    (scale : ℝ)
    (bound : ℕ → ℝ)
    (hbound :
      ∀ index : ℕ,
        index ∈ Finset.range (order + 1) →
          AdmissibleGaussianScaledUnitBumpDerivativeBound index
            (bound index)) :
    0 ≤
      admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
        order scale bound := by
  exact Finset.sum_nonneg
    (fun index hindex =>
      mul_nonneg
        (mul_nonneg
          (Nat.cast_nonneg (order.choose index))
          (le_of_lt (hbound index hindex).1))
        (mul_nonneg
          (le_of_lt (Real.exp_pos (scale ^ 2)))
          (MeasureTheory.integral_nonneg
            (fun t : ℝ =>
              norm_nonneg
                (iteratedDeriv (order - index)
                  realPhysicalGaussian t)))))

/-- The supplied-bound positive uniform derivative `L1` bound. -/
noncomputable def admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds
    (order : ℕ)
    (scale : ℝ)
    (bound : ℕ → ℝ) : ℝ :=
  admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
    order scale bound + 1

/-- The supplied-bound uniform derivative `L1` bound is positive. -/
theorem admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds_pos
    (order : ℕ)
    (scale : ℝ)
    (bound : ℕ → ℝ)
    (hbound :
      ∀ index : ℕ,
        index ∈ Finset.range (order + 1) →
          AdmissibleGaussianScaledUnitBumpDerivativeBound index
            (bound index)) :
    0 <
      admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds
        order scale bound :=
  add_pos_of_nonneg_of_pos
    (admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds_nonnegative
      order scale bound hbound)
    zero_lt_one

/-- Integrating the supplied-bound finite pointwise majorant gives the
corresponding finite sum of derivative `L1` norms. -/
theorem integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant_of_bounds
    (order : ℕ)
    (bound : ℕ → ℝ)
    (x : ℝ) :
    (∫ t : ℝ,
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) * bound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖) =
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) * bound index) *
          (∫ t : ℝ,
            ‖iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t‖) := by
  have htermIntegrable :
      ∀ index ∈ Finset.range (order + 1),
        MeasureTheory.Integrable
          (fun t : ℝ =>
            ((order.choose index : ℝ) * bound index) *
              ‖iteratedDeriv (order - index)
                (physicalGaussianHorizontalTwist x) t‖) := by
    intro index hindex
    exact
      (integrable_norm_iteratedDeriv_physicalGaussianHorizontalTwist
        (order - index) x).const_mul
          ((order.choose index : ℝ) * bound index)
  have hsumIntegral :=
    MeasureTheory.integral_finset_sum
      (s := Finset.range (order + 1))
      (f := fun (index : ℕ) (t : ℝ) =>
        ((order.choose index : ℝ) * bound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖)
      htermIntegrable
  have htermIntegral :
      ∀ index ∈ Finset.range (order + 1),
        (∫ t : ℝ,
          ((order.choose index : ℝ) * bound index) *
            ‖iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t‖) =
          ((order.choose index : ℝ) * bound index) *
            (∫ t : ℝ,
              ‖iteratedDeriv (order - index)
                (physicalGaussianHorizontalTwist x) t‖) := by
    intro index hindex
    exact MeasureTheory.integral_smul
      ((order.choose index : ℝ) * bound index)
      (fun t : ℝ =>
        ‖iteratedDeriv (order - index)
          (physicalGaussianHorizontalTwist x) t‖)
  exact Eq.trans hsumIntegral
    (Finset.sum_congr rfl htermIntegral)

/-- The supplied-bound integrated finite derivative majorant is uniformly
bounded on the symmetric strip. -/
theorem integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant_le_rawBound_of_bounds
    (order : ℕ)
    (scale x : ℝ)
    (bound : ℕ → ℝ)
    (hbound :
      ∀ index : ℕ,
        index ∈ Finset.range (order + 1) →
          AdmissibleGaussianScaledUnitBumpDerivativeBound index
            (bound index))
    (hscale : 0 < scale)
    (hx : |x| ≤ scale) :
    (∫ t : ℝ,
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) * bound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖) ≤
      admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
        order scale bound := by
  have hintegralIdentity :=
    integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant_of_bounds
      order bound x
  have hsumBound :
      (∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) * bound index) *
          (∫ t : ℝ,
            ‖iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t‖)) ≤
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) * bound index) *
          (Real.exp (scale ^ 2) *
            ∫ t : ℝ,
              ‖iteratedDeriv (order - index)
                realPhysicalGaussian t‖) := by
    exact Finset.sum_le_sum
      (fun index hindex =>
        mul_le_mul_of_nonneg_left
          (integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist_le_strip
            (order - index) scale x hscale hx)
          (mul_nonneg
            (Nat.cast_nonneg (order.choose index))
            (le_of_lt (hbound index hindex).1)))
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
          order scale bound)
    hintegralIdentity.symm
    hsumBound

/-- All natural cutoff horizontal twists have one supplied-bound derivative
`L1` bound on a fixed symmetric strip. -/
theorem integral_norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le_of_bounds
    (order : ℕ)
    (scale : ℝ)
    (bound : ℕ → ℝ)
    (hbound :
      ∀ index : ℕ,
        index ∈ Finset.range (order + 1) →
          AdmissibleGaussianScaledUnitBumpDerivativeBound index
            (bound index))
    (hscale : 0 < scale)
    (n : ℕ)
    (x : ℝ)
    (hx : |x| ≤ scale) :
    (∫ t : ℝ,
      ‖iteratedDeriv order
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwist
            (admissibleGaussianCutoffNat n) x u)
        t‖) ≤
      admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds
        order scale bound := by
  let source : ℝ → ℂ :=
    fun u : ℝ =>
      zetaPaleyWienerHorizontalTwist
        (admissibleGaussianCutoffNat n) x u
  let majorant : ℝ → ℝ :=
    fun t : ℝ =>
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) * bound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖
  have hsourceIntegrable :
      MeasureTheory.Integrable
        (fun t : ℝ => ‖iteratedDeriv order source t‖) :=
    integrable_norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_of_bounds
      order n bound hbound x
  have hmajorantIntegrable : MeasureTheory.Integrable majorant := by
    exact MeasureTheory.integrable_finset_sum
      (Finset.range (order + 1))
      (fun index hindex =>
        (integrable_norm_iteratedDeriv_physicalGaussianHorizontalTwist
          (order - index) x).const_mul
            ((order.choose index : ℝ) * bound index))
  have hpointwise : ∀ t : ℝ, ‖iteratedDeriv order source t‖ ≤ majorant t :=
    fun t =>
      norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le_majorant_of_bounds
        order n bound hbound x t
  have hintegralBound :
      (∫ t : ℝ, ‖iteratedDeriv order source t‖) ≤
        ∫ t : ℝ, majorant t :=
    MeasureTheory.integral_mono
      hsourceIntegrable
      hmajorantIntegrable
      hpointwise
  have hmajorantBound :
      (∫ t : ℝ, majorant t) ≤
        admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
          order scale bound :=
    integral_admissibleGaussianCutoffHorizontalTwistDerivativeMajorant_le_rawBound_of_bounds
      order scale x bound hbound hscale hx
  have hmargin :
      admissibleGaussianCutoffHorizontalTwistDerivativeRawL1BoundOfBounds
          order scale bound ≤
        admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds
          order scale bound :=
    le_add_of_nonneg_right zero_le_one
  exact le_trans hintegralBound
    (le_trans hmajorantBound hmargin)

/-- All natural cutoff horizontal twists have one derivative `L1` bound on a
fixed symmetric strip, constructed from a finite derivative-bound family. -/
theorem exists_admissibleGaussianCutoffHorizontalTwistDerivativeL1Bound
    (order : ℕ)
    (scale : ℝ)
    (hscale : 0 < scale) :
    ∃ bound : ℝ,
      0 < bound ∧
        ∀ n : ℕ,
          ∀ x : ℝ,
            |x| ≤ scale →
              (∫ t : ℝ,
                ‖iteratedDeriv order
                  (fun u : ℝ =>
                    zetaPaleyWienerHorizontalTwist
                      (admissibleGaussianCutoffNat n) x u)
                  t‖) ≤ bound := by
  match exists_admissibleGaussianScaledUnitBumpDerivativeBoundFamily order with
  | ⟨boundFamily, hboundFamily⟩ =>
      let bound : ℝ :=
        admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds
          order scale boundFamily
      have hboundPositive : 0 < bound :=
        admissibleGaussianCutoffHorizontalTwistDerivativeL1BoundOfBounds_pos
          order scale boundFamily hboundFamily
      have hcontrols :
          ∀ n : ℕ,
            ∀ x : ℝ,
              |x| ≤ scale →
                (∫ t : ℝ,
                  ‖iteratedDeriv order
                    (fun u : ℝ =>
                      zetaPaleyWienerHorizontalTwist
                        (admissibleGaussianCutoffNat n) x u)
                    t‖) ≤ bound := by
        intro n x hx
        exact
          integral_norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le_of_bounds
            order scale boundFamily hboundFamily hscale n x hx
      exact Exists.intro bound (And.intro hboundPositive hcontrols)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
