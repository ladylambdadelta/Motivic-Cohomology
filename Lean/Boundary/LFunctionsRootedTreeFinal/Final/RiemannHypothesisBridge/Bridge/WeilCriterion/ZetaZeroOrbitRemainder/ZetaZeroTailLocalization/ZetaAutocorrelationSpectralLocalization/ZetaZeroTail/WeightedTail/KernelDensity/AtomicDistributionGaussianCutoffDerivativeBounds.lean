import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionGaussianHorizontalTwist
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform derivative bounds for Gaussian cutoffs

The radius-dependent cutoff is a scaled fixed bump times a horizontally
twisted physical Gaussian.  The fixed bump derivatives are uniformly bounded
for radii at least one, while the twisted Gaussian derivatives have exact
translation-invariant `L1` norms.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ContDiff

/-- Complexification of the real horizontal Gaussian twist. -/
noncomputable def physicalGaussianHorizontalTwist
    (x t : ℝ) : ℂ :=
  physicalGaussian t * (Real.exp (x * t) : ℂ)

/-- The complex horizontal twist is the real twist embedded in the complex
line. -/
theorem physicalGaussianHorizontalTwist_eq_ofReal
    (x t : ℝ) :
    physicalGaussianHorizontalTwist x t =
      (realPhysicalGaussianHorizontalTwist x t : ℂ) := by
  have hgaussian :=
    physicalGaussian_eq_ofReal_realPhysicalGaussian t
  have hproductCast :
      ((realPhysicalGaussian t * Real.exp (x * t) : ℝ) : ℂ) =
        (realPhysicalGaussian t : ℂ) *
          (Real.exp (x * t) : ℂ) :=
    Complex.ofReal_mul
      (realPhysicalGaussian t)
      (Real.exp (x * t))
  exact Eq.trans
    (congrArg
      (fun value : ℂ => value * (Real.exp (x * t) : ℂ))
      hgaussian)
    hproductCast.symm

/-- Function-level complexification of the real horizontal twist. -/
theorem physicalGaussianHorizontalTwist_function_eq_ofReal
    (x : ℝ) :
    physicalGaussianHorizontalTwist x =
      Complex.ofRealLI ∘ realPhysicalGaussianHorizontalTwist x := by
  funext t
  exact physicalGaussianHorizontalTwist_eq_ofReal x t

/-- The complex horizontal twist is smooth. -/
theorem physicalGaussianHorizontalTwist_contDiff
    (x : ℝ) :
    ContDiff ℝ ∞ (physicalGaussianHorizontalTwist x) := by
  have hreal := realPhysicalGaussianHorizontalTwist_contDiff x
  have hcomplex :
      ContDiff ℝ ∞
        (Complex.ofRealLI ∘ realPhysicalGaussianHorizontalTwist x) :=
    Complex.ofRealLI.toContinuousLinearMap.contDiff.comp hreal
  exact Eq.mpr
    (congrArg (ContDiff ℝ ∞)
      (physicalGaussianHorizontalTwist_function_eq_ofReal x))
    hcomplex

/-- Complexification preserves the norm of every iterated derivative of the
horizontal Gaussian twist. -/
theorem norm_iteratedDeriv_physicalGaussianHorizontalTwist
    (order : ℕ)
    (x t : ℝ) :
    ‖iteratedDeriv order (physicalGaussianHorizontalTwist x) t‖ =
      ‖iteratedDeriv order
        (realPhysicalGaussianHorizontalTwist x) t‖ := by
  have hfiniteSmooth :
      ContDiff ℝ order (realPhysicalGaussianHorizontalTwist x) :=
    (realPhysicalGaussianHorizontalTwist_contDiff x).of_le
      (naturalOrder_le_contDiffInfinity order)
  have hfrechet :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left
      hfiniteSmooth
      t
      (show (order : WithTop ℕ∞) ≤ (order : WithTop ℕ∞) from
        le_refl (order : WithTop ℕ∞))
  have hcomplexFunction :=
    physicalGaussianHorizontalTwist_function_eq_ofReal x
  exact Eq.trans
    (congrArg
      (fun function : ℝ → ℂ =>
        ‖iteratedDeriv order function t‖)
      hcomplexFunction)
    (Eq.trans
      (norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm)
      (Eq.trans hfrechet
        norm_iteratedFDeriv_eq_norm_iteratedDeriv))

/-- Every complex horizontal-twist derivative norm is integrable. -/
theorem integrable_norm_iteratedDeriv_physicalGaussianHorizontalTwist
    (order : ℕ)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (physicalGaussianHorizontalTwist x) t‖) := by
  have hreal :=
    integrable_norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist
      order x
  have hfunction :
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (physicalGaussianHorizontalTwist x) t‖) =
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (realPhysicalGaussianHorizontalTwist x) t‖) := by
    funext t
    exact norm_iteratedDeriv_physicalGaussianHorizontalTwist order x t
  exact Eq.mp
    (congrArg
      (fun function : ℝ → ℝ =>
        MeasureTheory.Integrable function MeasureTheory.volume)
      hfunction.symm)
    hreal

/-- The complex and real horizontal twists have the same derivative `L1`
norm. -/
theorem integral_norm_iteratedDeriv_physicalGaussianHorizontalTwist
    (order : ℕ)
    (x : ℝ) :
    (∫ t : ℝ,
        ‖iteratedDeriv order
          (physicalGaussianHorizontalTwist x) t‖) =
      Real.exp ((x / 2) ^ 2) *
        ∫ t : ℝ,
          ‖iteratedDeriv order realPhysicalGaussian t‖ := by
  have hfunction :
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (physicalGaussianHorizontalTwist x) t‖) =
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (realPhysicalGaussianHorizontalTwist x) t‖) := by
    funext t
    exact norm_iteratedDeriv_physicalGaussianHorizontalTwist order x t
  exact Eq.trans
    (congrArg (fun function : ℝ → ℝ => ∫ t : ℝ, function t) hfunction)
    (integral_norm_iteratedDeriv_realPhysicalGaussianHorizontalTwist
      order x)

/-- Halving does not increase absolute value. -/
theorem abs_half_le_abs
    (x : ℝ) :
    |x / 2| ≤ |x| := by
  have habsoluteTwo : |(2 : ℝ)| = 2 :=
    abs_of_nonneg zero_le_two
  have hdivisionAbsolute : |x / 2| = |x| / 2 :=
    Eq.trans
      (abs_div x 2)
      (congrArg (fun value : ℝ => |x| / value) habsoluteTwo)
  have hdivisionBound : |x| / 2 ≤ |x| :=
    div_le_self (abs_nonneg x) one_le_two
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ |x|)
    hdivisionAbsolute.symm
    hdivisionBound

/-- Completion-of-square factors are uniformly bounded on a symmetric
horizontal strip. -/
theorem exp_halfSquare_le_exp_scaleSquare
    (scale x : ℝ)
    (hscale : 0 < scale)
    (hx : |x| ≤ scale) :
    Real.exp ((x / 2) ^ 2) ≤ Real.exp (scale ^ 2) := by
  have hscaleAbsolute : |scale| = scale :=
    abs_of_pos hscale
  have hhalfAbsolute : |x / 2| ≤ |scale| :=
    le_trans (abs_half_le_abs x)
      (Eq.subst
        (motive := fun value : ℝ => |x| ≤ value)
        hscaleAbsolute.symm
        hx)
  have hsquare : (x / 2) ^ 2 ≤ scale ^ 2 :=
    sq_le_sq.mpr hhalfAbsolute
  exact Real.exp_le_exp.mpr hsquare

/-- The radius-scaled fixed complex bump. -/
noncomputable def admissibleGaussianScaledUnitBump
    (radius t : ℝ) : ℂ :=
  admissibleGaussianUnitBumpProfile (t / radius)

/-- Natural cutoff horizontal twists factor into the scaled fixed bump and the
horizontal physical Gaussian twist. -/
theorem zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_eq_product
    (n : ℕ)
    (x t : ℝ) :
    zetaPaleyWienerHorizontalTwist
        (admissibleGaussianCutoffNat n) x t =
      admissibleGaussianScaledUnitBump ((n : ℝ) + 1) t *
        physicalGaussianHorizontalTwist x t := by
  have hcutoff :=
    admissibleGaussianCutoffNat_eq_unitProfile_mul_physicalGaussian n t
  have hleft :
      zetaPaleyWienerHorizontalTwist
          (admissibleGaussianCutoffNat n) x t =
        admissibleGaussianCutoffNat n t *
          (Real.exp (x * t) : ℂ) :=
    Eq.refl _
  have hrightReassociate :
      (admissibleGaussianUnitBumpProfile (t / ((n : ℝ) + 1)) *
          physicalGaussian t) *
          (Real.exp (x * t) : ℂ) =
        admissibleGaussianUnitBumpProfile (t / ((n : ℝ) + 1)) *
          (physicalGaussian t * (Real.exp (x * t) : ℂ)) :=
    mul_assoc
      (admissibleGaussianUnitBumpProfile (t / ((n : ℝ) + 1)))
      (physicalGaussian t)
      (Real.exp (x * t) : ℂ)
  exact Eq.trans hleft
    (Eq.trans
      (congrArg
        (fun value : ℂ => value * (Real.exp (x * t) : ℂ))
        hcutoff)
      hrightReassociate)

/-- Function-level cutoff-twist product normal form. -/
theorem zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_function_eq_product
    (n : ℕ)
    (x : ℝ) :
    (fun t : ℝ =>
      zetaPaleyWienerHorizontalTwist
        (admissibleGaussianCutoffNat n) x t) =
      (fun t : ℝ =>
        admissibleGaussianScaledUnitBump ((n : ℝ) + 1) t *
          physicalGaussianHorizontalTwist x t) := by
  funext t
  exact
    zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_eq_product
      n x t

/-- The scaled fixed bump is smooth for every radius. -/
theorem admissibleGaussianScaledUnitBump_contDiff
    (radius : ℝ) :
    ContDiff ℝ ∞ (admissibleGaussianScaledUnitBump radius) := by
  have hdivision : ContDiff ℝ ∞ (fun t : ℝ => t / radius) :=
    contDiff_id.div_const radius
  exact admissibleGaussianUnitBumpProfile_contDiff.comp hdivision

/-- Pointwise binomial derivative bound for every natural cutoff horizontal
twist. -/
theorem norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le
    (order n : ℕ)
    (x t : ℝ) :
    ‖iteratedDeriv order
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwist
            (admissibleGaussianCutoffNat n) x u)
        t‖ ≤
      ∑ index ∈ Finset.range (order + 1),
        (order.choose index : ℝ) *
          ‖iteratedDeriv index
            (admissibleGaussianScaledUnitBump ((n : ℝ) + 1)) t‖ *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖ := by
  let bump : ℝ → ℂ :=
    admissibleGaussianScaledUnitBump ((n : ℝ) + 1)
  let twist : ℝ → ℂ := physicalGaussianHorizontalTwist x
  have hbump : ContDiff ℝ ∞ bump :=
    admissibleGaussianScaledUnitBump_contDiff ((n : ℝ) + 1)
  have htwist : ContDiff ℝ ∞ twist :=
    physicalGaussianHorizontalTwist_contDiff x
  have hproductBound :=
    norm_iteratedFDeriv_mul_le
      hbump
      htwist
      t
      (naturalOrder_le_contDiffInfinity order)
  have hsourceFunction :=
    zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_function_eq_product
      n x
  have hleft :
      ‖iteratedDeriv order
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwist
              (admissibleGaussianCutoffNat n) x u)
          t‖ =
        ‖iteratedFDeriv ℝ order (fun u : ℝ => bump u * twist u) t‖ :=
    Eq.trans
      (congrArg
        (fun function : ℝ → ℂ =>
          ‖iteratedDeriv order function t‖)
        hsourceFunction)
      norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm
  have hright :
      (∑ index ∈ Finset.range (order + 1),
        (order.choose index : ℝ) *
          ‖iteratedFDeriv ℝ index bump t‖ *
          ‖iteratedFDeriv ℝ (order - index) twist t‖) =
      ∑ index ∈ Finset.range (order + 1),
        (order.choose index : ℝ) *
          ‖iteratedDeriv index bump t‖ *
          ‖iteratedDeriv (order - index) twist t‖ := by
    exact Finset.sum_congr rfl
      (fun index hindex =>
        congrArg₂ Mul.mul
          (congrArg
            (fun value : ℝ => (order.choose index : ℝ) * value)
            norm_iteratedFDeriv_eq_norm_iteratedDeriv)
          norm_iteratedFDeriv_eq_norm_iteratedDeriv)
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤
        ∑ index ∈ Finset.range (order + 1),
          (order.choose index : ℝ) *
            ‖iteratedDeriv index bump t‖ *
            ‖iteratedDeriv (order - index) twist t‖)
    hleft.symm
    (Eq.mp
      (congrArg
        (fun right : ℝ =>
          ‖iteratedFDeriv ℝ order (fun u : ℝ => bump u * twist u) t‖ ≤
            right)
        hright)
      hproductBound)

/-- A chosen positive uniform bound for one derivative of every radius-scaled
unit bump with radius at least one. -/
noncomputable def admissibleGaussianScaledUnitBumpDerivativeBound
    (order : ℕ) : ℝ :=
  Classical.choose
    (exists_admissibleGaussianUnitBumpProfile_div_iteratedDeriv_uniform_bound
      order)

/-- The chosen scaled-bump derivative bound is positive. -/
theorem admissibleGaussianScaledUnitBumpDerivativeBound_pos
    (order : ℕ) :
    0 < admissibleGaussianScaledUnitBumpDerivativeBound order :=
  (Classical.choose_spec
    (exists_admissibleGaussianUnitBumpProfile_div_iteratedDeriv_uniform_bound
      order)).1

/-- The chosen bound controls every scaled-bump derivative at every radius at
least one. -/
theorem norm_iteratedDeriv_admissibleGaussianScaledUnitBump_le
    (order : ℕ)
    (radius : ℝ)
    (hradius : 1 ≤ radius)
    (t : ℝ) :
    ‖iteratedDeriv order
        (admissibleGaussianScaledUnitBump radius) t‖ ≤
      admissibleGaussianScaledUnitBumpDerivativeBound order := by
  exact
    (Classical.choose_spec
      (exists_admissibleGaussianUnitBumpProfile_div_iteratedDeriv_uniform_bound
        order)).2
      radius hradius t

/-- Replacing every scaled-bump derivative by its chosen uniform bound gives
an integrable Gaussian majorant. -/
theorem norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le_majorant
    (order n : ℕ)
    (x t : ℝ) :
    ‖iteratedDeriv order
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwist
            (admissibleGaussianCutoffNat n) x u)
        t‖ ≤
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖ := by
  have hraw :=
    norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le
      order n x t
  have hradius : 1 ≤ (n : ℝ) + 1 :=
    le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hsum :
      (∑ index ∈ Finset.range (order + 1),
        (order.choose index : ℝ) *
          ‖iteratedDeriv index
            (admissibleGaussianScaledUnitBump ((n : ℝ) + 1)) t‖ *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖) ≤
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖ := by
    exact Finset.sum_le_sum
      (fun index hindex =>
        have hchooseNonnegative :
            0 ≤ (order.choose index : ℝ) :=
          Nat.cast_nonneg (order.choose index)
        have hbump :=
          norm_iteratedDeriv_admissibleGaussianScaledUnitBump_le
            index ((n : ℝ) + 1) hradius t
        have hscaledBump :
            (order.choose index : ℝ) *
                ‖iteratedDeriv index
                  (admissibleGaussianScaledUnitBump ((n : ℝ) + 1)) t‖ ≤
              (order.choose index : ℝ) *
                admissibleGaussianScaledUnitBumpDerivativeBound index :=
          mul_le_mul_of_nonneg_left hbump hchooseNonnegative
        mul_le_mul_of_nonneg_right
          hscaledBump
          (norm_nonneg
            (iteratedDeriv (order - index)
              (physicalGaussianHorizontalTwist x) t)))
  exact le_trans hraw hsum

/-- Every iterated derivative norm of every natural cutoff horizontal twist is
integrable. -/
theorem integrable_norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat
    (order n : ℕ)
    (x : ℝ) :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        ‖iteratedDeriv order
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwist
              (admissibleGaussianCutoffNat n) x u)
          t‖) := by
  let majorant : ℝ → ℝ :=
    fun t : ℝ =>
      ∑ index ∈ Finset.range (order + 1),
        ((order.choose index : ℝ) *
          admissibleGaussianScaledUnitBumpDerivativeBound index) *
          ‖iteratedDeriv (order - index)
            (physicalGaussianHorizontalTwist x) t‖
  have hmajorantIntegrable : MeasureTheory.Integrable majorant := by
    exact MeasureTheory.integrable_finset_sum
      (Finset.range (order + 1))
      (fun index hindex =>
        (integrable_norm_iteratedDeriv_physicalGaussianHorizontalTwist
          (order - index) x).const_mul
            ((order.choose index : ℝ) *
              admissibleGaussianScaledUnitBumpDerivativeBound index))
  have hsourceSmooth :
      ContDiff ℝ ∞
        (fun u : ℝ =>
          zetaPaleyWienerHorizontalTwist
            (admissibleGaussianCutoffNat n) x u) :=
    zetaPaleyWienerHorizontalTwist_contDiff
      (admissibleGaussianCutoffNat n) x
  have htargetMeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ =>
          ‖iteratedDeriv order
            (fun u : ℝ =>
              zetaPaleyWienerHorizontalTwist
                (admissibleGaussianCutoffNat n) x u)
            t‖) :=
    ((hsourceSmooth.continuous_iteratedDeriv order)
      (naturalOrder_le_contDiffInfinity order)).norm.aestronglyMeasurable
  have hpointwise :
      ∀ t : ℝ,
        ‖‖iteratedDeriv order
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwist
              (admissibleGaussianCutoffNat n) x u)
          t‖‖ ≤ majorant t := by
    intro t
    have hnormNorm :
        ‖‖iteratedDeriv order
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwist
              (admissibleGaussianCutoffNat n) x u)
          t‖‖ =
        ‖iteratedDeriv order
          (fun u : ℝ =>
            zetaPaleyWienerHorizontalTwist
              (admissibleGaussianCutoffNat n) x u)
          t‖ :=
      Real.norm_of_nonneg
        (norm_nonneg
          (iteratedDeriv order
            (fun u : ℝ =>
              zetaPaleyWienerHorizontalTwist
                (admissibleGaussianCutoffNat n) x u)
            t))
    exact Eq.subst
      (motive := fun left : ℝ => left ≤ majorant t)
      hnormNorm.symm
      (norm_iteratedDeriv_zetaPaleyWienerHorizontalTwist_admissibleGaussianCutoffNat_le_majorant
        order n x t)
  exact MeasureTheory.Integrable.mono'
    hmajorantIntegrable
    htargetMeasurable
    (Filter.Eventually.of_forall hpointwise)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
