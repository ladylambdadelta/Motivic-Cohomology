import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

open scoped ContDiff

namespace SchwartzMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth compactly supported function, multiplied by any polynomial weight and
then differentiated any finite number of times, remains uniformly bounded. -/
theorem compactSupport_polynomial_derivative_bound
    (f : E → F)
    (hfSmooth : ContDiff ℝ ∞ f)
    (hfCompact : HasCompactSupport f)
    (k n : ℕ) :
    ∃ C : ℝ, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  let weightedDerivativeNorm : E → ℝ :=
    fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
  have hDerivativeContinuous :
      Continuous (iteratedFDeriv ℝ n f) :=
    ContDiff.continuous_iteratedFDeriv
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (m := n)
      (WithTop.coe_le_coe.mpr
        (show (n : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
      hfSmooth
  have hWeightContinuous : Continuous (fun x : E => ‖x‖ ^ k) :=
    (continuous_norm.pow k)
  have hDerivativeNormContinuous :
      Continuous (fun x : E => ‖iteratedFDeriv ℝ n f x‖) :=
    hDerivativeContinuous.norm
  have hWeightedContinuous : Continuous weightedDerivativeNorm :=
    hWeightContinuous.mul hDerivativeNormContinuous
  have hDerivativeCompact :
      HasCompactSupport (iteratedFDeriv ℝ n f) :=
    hfCompact.iteratedFDeriv n
  have hDerivativeNormCompact :
      HasCompactSupport (fun x : E => ‖iteratedFDeriv ℝ n f x‖) :=
    hDerivativeCompact.norm
  have hWeightedCompact : HasCompactSupport weightedDerivativeNorm :=
    hDerivativeNormCompact.mul_left
  exact
    Exists.elim
      (hWeightedContinuous.bounded_above_of_compact_support hWeightedCompact)
      (fun C hC =>
        Exists.intro C (fun x =>
          calc
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ =
                ‖weightedDerivativeNorm x‖ :=
              (Real.norm_of_nonneg
                (mul_nonneg
                  (pow_nonneg (norm_nonneg x) k)
                  (norm_nonneg (iteratedFDeriv ℝ n f x)))).symm
            _ ≤ C := hC x))

/-- The canonical inclusion of smooth compactly supported functions into Schwartz space. -/
def ofSmoothCompactSupport
    (f : E → F)
    (hfSmooth : ContDiff ℝ ∞ f)
    (hfCompact : HasCompactSupport f) : SchwartzMap E F where
  toFun := f
  smooth' := hfSmooth
  decay' := compactSupport_polynomial_derivative_bound f hfSmooth hfCompact

theorem ofSmoothCompactSupport_apply
    (f : E → F)
    (hfSmooth : ContDiff ℝ ∞ f)
    (hfCompact : HasCompactSupport f)
    (x : E) :
    ofSmoothCompactSupport f hfSmooth hfCompact x = f x :=
  rfl

end SchwartzMap
