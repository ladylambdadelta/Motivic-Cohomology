import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Boundary

open scoped MeasureTheory
open scoped Convolution
open Real Complex Set MeasureTheory

noncomputable section

section Mellin

theorem real_add_sub_right_eq_left (y t : ℝ) : y + (t - y) = t := by
  calc
    y + (t - y) = y + (t + -y) := by
      exact congrArg (fun x : ℝ => y + x) (sub_eq_add_neg t y)
    _ = (y + t) + -y := by
      exact (add_assoc y t (-y)).symm
    _ = y + t - y := by
      exact (sub_eq_add_neg (y + t) y).symm
    _ = t := add_sub_cancel_left y t

theorem complex_mul_pair_reassociate (a b c d : ℂ) :
    (a * b) * (c * d) = (a * c) * (b * d) := by
  calc
    (a * b) * (c * d) = ((a * b) * c) * d := by
      exact (mul_assoc (a * b) c d).symm
    _ = (a * (b * c)) * d := by
      exact congrArg (fun x : ℂ => x * d) (mul_assoc a b c)
    _ = (a * (c * b)) * d := by
      exact congrArg (fun x : ℂ => (a * x) * d) (mul_comm b c)
    _ = ((a * c) * b) * d := by
      exact congrArg (fun x : ℂ => x * d) (mul_assoc a c b).symm
    _ = (a * c) * (b * d) := by
      exact mul_assoc (a * c) b d

theorem complex_ofReal_neg_star (a : ℝ) : -star (a : ℂ) = -(a : ℂ) := by
  exact congrArg Neg.neg (Complex.conj_ofReal a)

/-- The zeta Laplace transform attached to a test function. -/
noncomputable def zetaLaplaceTransform
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) : ℂ :=
  ∫ t : ℝ, φ t * Complex.exp (z * t)

/-- The dagger Laplace kernel is the conjugate of the opposite spectral kernel. This lives in the
base transform file so convolution transform calculus does not depend on the reflection layer. -/
theorem dagger_laplaceKernel_pointwise_base
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) :
    (LFunctions.ZetaAdmissibleFunction.dagger f).toZetaTestFunction' t *
        Complex.exp (z * t) =
      star
        (f.toZetaTestFunction' (-t) *
          Complex.exp ((-star z) * (-t))) := by
  have hdagger :
      (LFunctions.ZetaAdmissibleFunction.dagger f).toZetaTestFunction' t =
        star (f.toZetaTestFunction' (-t)) := by
    exact LFunctions.ZetaAdmissibleFunction.dagger_apply f t
  have hexp :
      Complex.exp (z * t) =
        star (Complex.exp ((-star z) * (-t))) := by
    have harg :
        z * (t : ℂ) = star ((-star z) * (-(t : ℂ))) := by
      have hnegmul :
          (-star z) * (-(t : ℂ)) = star z * (t : ℂ) := by
        exact neg_mul_neg (star z) (t : ℂ)
      have hstar :
          star ((-star z) * (-(t : ℂ))) =
            star (star z * (t : ℂ)) := by
        exact congrArg star hnegmul
      have hstar_mul :
          star (star z * (t : ℂ)) =
            star (t : ℂ) * star (star z) := by
        exact star_mul (star z) (t : ℂ)
      have ht :
          star (t : ℂ) = (t : ℂ) := by
        exact Complex.conj_ofReal t
      have hzz :
          star (star z) = z := by
        exact star_star z
      calc
        z * (t : ℂ) = (t : ℂ) * z := by
          exact mul_comm z (t : ℂ)
        _ = star (t : ℂ) * z := by
          exact congrArg (fun w : ℂ => w * z) ht.symm
        _ = star (t : ℂ) * star (star z) := by
          exact congrArg (fun w : ℂ => star (t : ℂ) * w) hzz.symm
        _ = star (star z * (t : ℂ)) := by
          exact hstar_mul.symm
        _ = star ((-star z) * (-(t : ℂ))) := by
          exact hstar.symm
    calc
      Complex.exp (z * t) =
          Complex.exp (star ((-star z) * (-t))) := by
        exact congrArg Complex.exp harg
      _ = star (Complex.exp ((-star z) * (-t))) := by
        exact Complex.exp_conj ((-star z) * (-t))
  calc
    (LFunctions.ZetaAdmissibleFunction.dagger f).toZetaTestFunction' t *
        Complex.exp (z * t) =
        star (f.toZetaTestFunction' (-t)) * Complex.exp (z * t) := by
      exact congrArg
        (fun w : ℂ => w * Complex.exp (z * t))
        hdagger
    _ =
        star (f.toZetaTestFunction' (-t)) *
          star (Complex.exp ((-star z) * (-t))) := by
      exact congrArg
        (fun w : ℂ => star (f.toZetaTestFunction' (-t)) * w)
        hexp
    _ =
        star
          (f.toZetaTestFunction' (-t) *
            Complex.exp ((-star z) * (-t))) := by
      have hcomm :
          star (f.toZetaTestFunction' (-t)) *
              star (Complex.exp ((-star z) * (-t))) =
            star (Complex.exp ((-star z) * (-t))) *
              star (f.toZetaTestFunction' (-t)) := by
        exact mul_comm
          (star (f.toZetaTestFunction' (-t)))
          (star (Complex.exp ((-star z) * (-t))))
      exact hcomm.trans
        (star_mul
          (f.toZetaTestFunction' (-t))
          (Complex.exp ((-star z) * (-t)))).symm

/-- The dagger Laplace transform is the conjugate of the opposite spectral transform. -/
theorem zetaLaplaceTransform_dagger_base
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.dagger f).toZetaTestFunction' z =
      star (zetaLaplaceTransform f.toZetaTestFunction' (-star z)) := by
  unfold zetaLaplaceTransform
  calc
    (∫ t : ℝ,
        (LFunctions.ZetaAdmissibleFunction.dagger f).toZetaTestFunction' t *
          Complex.exp (z * t)) =
        ∫ t : ℝ,
          star
            (f.toZetaTestFunction' (-t) *
              Complex.exp ((-star z) * (-t))) := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall
          (fun t : ℝ => dagger_laplaceKernel_pointwise_base f z t))
    _ =
        ∫ t : ℝ,
          star
            (f.toZetaTestFunction' t *
              Complex.exp ((-star z) * t)) := by
      have hneg : MeasurePreserving (fun x : ℝ => -x)
          (volume : Measure ℝ) (volume : Measure ℝ) :=
        ⟨measurable_neg, Measure.map_neg_eq_self (volume : Measure ℝ)⟩
      let G : ℝ → ℂ := fun t : ℝ =>
          star
            (f.toZetaTestFunction' t *
              Complex.exp ((-star z) * t))
      have hleft :
          (∫ t : ℝ,
            star
              (f.toZetaTestFunction' (-t) *
                Complex.exp ((-star z) * (-t)))) =
            ∫ t : ℝ, G (-t) := by
        exact integral_congr_ae
          (Filter.Eventually.of_forall
            (fun t : ℝ =>
              congrArg
                (fun w : ℂ =>
                  star
                    (f.toZetaTestFunction' (-t) *
                      Complex.exp ((-star z) * w)))
                (Complex.ofReal_neg t).symm))
      have hright :
          (∫ t : ℝ, G t) =
            ∫ t : ℝ,
              star
                (f.toZetaTestFunction' t *
                  Complex.exp ((-star z) * t)) := by
        rfl
      have hcomp :=
        hneg.integral_comp
          (Homeomorph.neg ℝ).measurableEmbedding
          G
      change (∫ x : ℝ, G (-x)) =
        ∫ y : ℝ, G y at hcomp
      exact hleft.trans (hcomp.trans hright)
    _ =
        star
          (∫ t : ℝ,
            f.toZetaTestFunction' t *
              Complex.exp ((-star z) * t)) := by
      exact integral_conj

/-- The Laplace transform of the convolution autocorrelation unfolds to the single integral
whose integrand contains the autocorrelation integral. -/
theorem zetaLaplaceTransform_convolutionAutocorrelation_unfold
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction'
        z =
      ∫ t : ℝ,
        (∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))) *
          Complex.exp (z * t) := by
  unfold zetaLaplaceTransform
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun t : ℝ =>
    congrArg (fun y : ℂ => y * Complex.exp (z * t))
      ((LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelation_toZetaTestFunction'_apply
          f t).trans
        (LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelationKernel_apply f t))

/-- The weighted standard convolution integrand equals the convolution of the weighted faces. -/
theorem weighted_standardConvolutionPair_pointwise
    (f h : LFunctions.ZetaAdmissibleFunction) (z : ℂ) (t : ℝ) :
    LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
        Complex.exp (z * t) =
      (((fun v : ℝ => f v * Complex.exp (z * v)) ⋆[ContinuousLinearMap.mul ℝ ℂ]
          (fun w : ℝ =>
            (LFunctions.ZetaAdmissibleFunction.dagger h) w * Complex.exp (z * w))) t) := by
  let A : ℝ → ℂ := fun v : ℝ => f v * Complex.exp (z * v)
  let B : ℝ → ℂ := fun w : ℝ =>
    (LFunctions.ZetaAdmissibleFunction.dagger h) w * Complex.exp (z * w)
  let C : ℝ → ℂ := fun y : ℝ =>
    f y * (LFunctions.ZetaAdmissibleFunction.dagger h) (t - y)
  have hmul_integral :
      LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
          Complex.exp (z * t) =
        ∫ y : ℝ, C y * Complex.exp (z * t) := by
    unfold LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard
    unfold MeasureTheory.convolution
    change (∫ y : ℝ, C y) * Complex.exp (z * t) =
      ∫ y : ℝ, C y * Complex.exp (z * t)
    exact (integral_mul_right (Complex.exp (z * t)) C).symm
  have hpoint :
      (fun y : ℝ => C y * Complex.exp (z * t)) =
        fun y : ℝ => A y * B (t - y) := by
    funext y
    have hsplit : (t : ℂ) = (y : ℂ) + ((t - y : ℝ) : ℂ) := by
      have hreal : y + (t - y) = t := by
        exact real_add_sub_right_eq_left y t
      calc
        (t : ℂ) = ((y + (t - y) : ℝ) : ℂ) := by
          exact congrArg (fun x : ℝ => (x : ℂ)) hreal.symm
        _ = (y : ℂ) + ((t - y : ℝ) : ℂ) := by
          exact Complex.ofReal_add y (t - y)
    have harg : z * (t : ℂ) =
        z * (y : ℂ) + z * ((t - y : ℝ) : ℂ) := by
      calc
        z * (t : ℂ) =
            z * ((y : ℂ) + ((t - y : ℝ) : ℂ)) := by
          exact congrArg (fun w : ℂ => z * w) hsplit
        _ = z * (y : ℂ) + z * ((t - y : ℝ) : ℂ) := by
          exact mul_add z (y : ℂ) ((t - y : ℝ) : ℂ)
    have hexp :
        Complex.exp (z * t) =
          Complex.exp (z * y) * Complex.exp (z * ((t - y : ℝ) : ℂ)) := by
      calc
        Complex.exp (z * t) =
            Complex.exp (z * (y : ℂ) + z * ((t - y : ℝ) : ℂ)) := by
          exact congrArg Complex.exp harg
        _ =
            Complex.exp (z * y) * Complex.exp (z * ((t - y : ℝ) : ℂ)) := by
          exact Complex.exp_add (z * y) (z * ((t - y : ℝ) : ℂ))
    calc
      C y * Complex.exp (z * t) =
          (f y * (LFunctions.ZetaAdmissibleFunction.dagger h) (t - y)) *
            Complex.exp (z * t) := by
        rfl
      _ =
          (f y * (LFunctions.ZetaAdmissibleFunction.dagger h) (t - y)) *
            (Complex.exp (z * y) *
              Complex.exp (z * ((t - y : ℝ) : ℂ))) := by
        exact congrArg
          (fun w : ℂ =>
            (f y * (LFunctions.ZetaAdmissibleFunction.dagger h) (t - y)) * w)
          hexp
      _ =
          (f y * Complex.exp (z * y)) *
            ((LFunctions.ZetaAdmissibleFunction.dagger h) (t - y) *
              Complex.exp (z * ((t - y : ℝ) : ℂ))) := by
        exact complex_mul_pair_reassociate
          (f y)
          ((LFunctions.ZetaAdmissibleFunction.dagger h) (t - y))
          (Complex.exp (z * y))
          (Complex.exp (z * ((t - y : ℝ) : ℂ)))
      _ = A y * B (t - y) := by
        rfl
  calc
    LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
        Complex.exp (z * t) =
        ∫ y : ℝ, C y * Complex.exp (z * t) := hmul_integral
    _ = ∫ y : ℝ, A y * B (t - y) := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
        congrArg (fun F : ℝ → ℂ => F y) hpoint)
    _ = ((A ⋆[ContinuousLinearMap.mul ℝ ℂ] B) t) := by
      rfl

/-- Weighted Laplace kernels of admissible functions are integrable by continuity and compact
support. This local owner lemma is placed before the convolution transform factorization. -/
theorem integrable_admissible_laplaceKernel
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    Integrable
      (fun t : ℝ => f t * Complex.exp (z * t))
      (volume : Measure ℝ) := by
  have hcont : Continuous (fun t : ℝ => f t * Complex.exp (z * t)) := by
    have hf : Continuous fun t : ℝ => f t :=
      f.toZetaTestFunction.continuous
    have hmul : Continuous (fun t : ℝ => (z : ℂ) * t) := by
      exact continuous_const.mul Complex.continuous_ofReal
    have hexp : Continuous (fun t : ℝ => Complex.exp (z * t)) :=
      Complex.continuous_exp.comp hmul
    exact hf.mul hexp
  have hsupport :
      HasCompactSupport (fun t : ℝ => f t * Complex.exp (z * t)) := by
    exact f.toZetaTestFunction.hasCompactSupport.mul_right
  exact hcont.integrable_of_hasCompactSupport hsupport

/-- The Laplace transform of the standard convolution-pair kernel factors by the convolution
integral theorem. -/
theorem zetaLaplaceTransform_standardConvolutionPair
    (f h : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    (∫ t : ℝ,
        LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
          Complex.exp (z * t)) =
      zetaLaplaceTransform f.toZetaTestFunction' z *
        star (zetaLaplaceTransform h.toZetaTestFunction' (-star z)) := by
  let A : ℝ → ℂ := fun v : ℝ => f v * Complex.exp (z * v)
  let B : ℝ → ℂ := fun w : ℝ =>
    (LFunctions.ZetaAdmissibleFunction.dagger h) w * Complex.exp (z * w)
  have hpoint :
      (fun t : ℝ =>
        LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
          Complex.exp (z * t)) =
        fun t : ℝ => (A ⋆[ContinuousLinearMap.mul ℝ ℂ] B) t := by
    funext t
    exact weighted_standardConvolutionPair_pointwise f h z t
  have hA : Integrable A (volume : Measure ℝ) :=
    integrable_admissible_laplaceKernel f z
  have hB : Integrable B (volume : Measure ℝ) :=
    integrable_admissible_laplaceKernel
      (LFunctions.ZetaAdmissibleFunction.dagger h) z
  have hconv :
      (∫ t : ℝ, (A ⋆[ContinuousLinearMap.mul ℝ ℂ] B) t) =
        (∫ t : ℝ, A t) * (∫ t : ℝ, B t) := by
    exact MeasureTheory.integral_convolution
      (ContinuousLinearMap.mul ℝ ℂ)
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      hA hB
  have hdagger :
      (∫ t : ℝ, B t) =
        star (zetaLaplaceTransform h.toZetaTestFunction' (-star z)) := by
    exact zetaLaplaceTransform_dagger_base h z
  unfold zetaLaplaceTransform
  change (∫ t : ℝ,
      LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
        Complex.exp (z * t)) =
    (∫ t : ℝ, A t) *
      star (∫ t : ℝ, h.toZetaTestFunction' t * Complex.exp ((-star z) * t))
  calc
    (∫ t : ℝ,
        LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
          Complex.exp (z * t)) =
        ∫ t : ℝ, (A ⋆[ContinuousLinearMap.mul ℝ ℂ] B) t := by
      exact congrArg (fun F : ℝ → ℂ => ∫ t : ℝ, F t) hpoint
    _ = (∫ t : ℝ, A t) * (∫ t : ℝ, B t) := hconv
    _ =
        (∫ t : ℝ, A t) *
          star (∫ t : ℝ, h.toZetaTestFunction' t * Complex.exp ((-star z) * t)) := by
      exact congrArg (fun w : ℂ => (∫ t : ℝ, A t) * w) hdagger

/-- The Laplace transform of the standard autocorrelation kernel factors by the convolution
integral theorem. -/
theorem zetaLaplaceTransform_standardConvolutionAutocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    (∫ t : ℝ,
        LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelationKernelStandard f t *
          Complex.exp (z * t)) =
      zetaLaplaceTransform f.toZetaTestFunction' z *
        star (zetaLaplaceTransform f.toZetaTestFunction' (-star z)) := by
  exact zetaLaplaceTransform_standardConvolutionPair f f z

/-- The separated two-variable integral factors into the product of the two seed Laplace
transforms. -/
theorem zetaLaplaceTransform_convolutionAutocorrelation_factorSeparated
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    (∫ v : ℝ, ∫ w : ℝ,
        (f v * Complex.exp (z * v)) *
          star (f w * Complex.exp ((-star z) * w))) =
      zetaLaplaceTransform f.toZetaTestFunction' z *
        star (zetaLaplaceTransform f.toZetaTestFunction' (-star z)) := by
  let A : ℝ → ℂ := fun v : ℝ => f v * Complex.exp (z * v)
  let B : ℝ → ℂ := fun w : ℝ => f w * Complex.exp ((-star z) * w)
  have hinner :
      (fun v : ℝ => ∫ w : ℝ, A v * star (B w)) =
        fun v : ℝ => A v * ∫ w : ℝ, star (B w) := by
    funext v
    exact integral_mul_left (A v) (fun w : ℝ => star (B w))
  have houter :
      (∫ v : ℝ, A v * ∫ w : ℝ, star (B w)) =
        (∫ v : ℝ, A v) * (∫ w : ℝ, star (B w)) := by
    exact integral_mul_right (∫ w : ℝ, star (B w)) A
  have hstar :
      (∫ w : ℝ, star (B w)) =
        star (∫ w : ℝ, B w) := by
    exact integral_conj
  unfold zetaLaplaceTransform
  change (∫ v : ℝ, ∫ w : ℝ, A v * star (B w)) =
      (∫ t : ℝ, A t) * star (∫ t : ℝ, B t)
  calc
    (∫ v : ℝ, ∫ w : ℝ, A v * star (B w)) =
        ∫ v : ℝ, A v * ∫ w : ℝ, star (B w) := by
      exact congrArg (fun F : ℝ → ℂ => ∫ v : ℝ, F v) hinner
    _ = (∫ v : ℝ, A v) * (∫ w : ℝ, star (B w)) := houter
    _ = (∫ v : ℝ, A v) * star (∫ w : ℝ, B w) := by
      exact congrArg (fun y : ℂ => (∫ v : ℝ, A v) * y) hstar

/-- The convolution autocorrelation Laplace integral becomes a separated two-variable integral
after the linear change of variables `v = u + t/2`, `w = u-t/2`.

The owner proof factors through the standard convolution theorem; this displayed equality is the
coordinate form consumed downstream. -/
theorem zetaLaplaceTransform_convolutionAutocorrelation_changeVariables
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    (∫ t : ℝ,
        (∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))) *
          Complex.exp (z * t)) =
      ∫ v : ℝ, ∫ w : ℝ,
        (f v * Complex.exp (z * v)) *
          star (f w * Complex.exp ((-star z) * w)) := by
  have hleft :
      (∫ t : ℝ,
          (∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))) *
            Complex.exp (z * t)) =
        ∫ t : ℝ,
          LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelationKernelStandard f t *
            Complex.exp (z * t) := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      congrArg (fun y : ℂ => y * Complex.exp (z * t))
        ((LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelationKernel_apply f t).symm.trans
          (congrFun
            (LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelationKernel_eq_standard f)
            t)))
  have hstandard :
      (∫ t : ℝ,
          LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelationKernelStandard f t *
            Complex.exp (z * t)) =
        zetaLaplaceTransform f.toZetaTestFunction' z *
          star (zetaLaplaceTransform f.toZetaTestFunction' (-star z)) :=
    zetaLaplaceTransform_standardConvolutionAutocorrelation f z
  have hright :
      (∫ v : ℝ, ∫ w : ℝ,
          (f v * Complex.exp (z * v)) *
            star (f w * Complex.exp ((-star z) * w))) =
        zetaLaplaceTransform f.toZetaTestFunction' z *
          star (zetaLaplaceTransform f.toZetaTestFunction' (-star z)) :=
    zetaLaplaceTransform_convolutionAutocorrelation_factorSeparated f z
  exact hleft.trans (hstandard.trans hright.symm)

/-- Laplace transform of the convolution autocorrelation kernel.

For `g_f(t) = ∫ f(u+t/2) * conj(f(u-t/2)) du`, the two-variable change of variables
`v = u+t/2`, `w = u-t/2` factors the Laplace transform of `g_f` into the Hermitian product
of the seed transforms. This is the transform-level owner theorem consumed by the
explicit-formula spectral packet bridge. -/
theorem zetaLaplaceTransform_convolutionAutocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction'
        z =
      zetaLaplaceTransform f.toZetaTestFunction' z *
        star (zetaLaplaceTransform f.toZetaTestFunction' (-star z)) := by
  exact
    (zetaLaplaceTransform_convolutionAutocorrelation_unfold f z).trans
      ((zetaLaplaceTransform_convolutionAutocorrelation_changeVariables f z).trans
        (zetaLaplaceTransform_convolutionAutocorrelation_factorSeparated f z))

/-- On real spectral parameters, the convolution autocorrelation transform pairs the opposite
real spectral parameters. The later packet normalization is responsible for folding this paired
coordinate into a Hermitian square when the explicit-formula symmetry identifies the paired
amplitudes. -/
theorem zetaLaplaceTransform_convolutionAutocorrelation_real_pair
    (f : LFunctions.ZetaAdmissibleFunction) (a : ℝ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction'
        (a : ℂ) =
      zetaLaplaceTransform f.toZetaTestFunction' (a : ℂ) *
        star (zetaLaplaceTransform f.toZetaTestFunction' (-(a : ℂ))) := by
  have hstar_arg : -star (a : ℂ) = -(a : ℂ) := complex_ofReal_neg_star a
  calc
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction'
        (a : ℂ) =
      zetaLaplaceTransform f.toZetaTestFunction' (a : ℂ) *
        star (zetaLaplaceTransform f.toZetaTestFunction' (-star (a : ℂ))) := by
      exact zetaLaplaceTransform_convolutionAutocorrelation f (a : ℂ)
    _ =
      zetaLaplaceTransform f.toZetaTestFunction' (a : ℂ) *
        star (zetaLaplaceTransform f.toZetaTestFunction' (-(a : ℂ))) := by
      exact congrArg
        (fun w : ℂ =>
          zetaLaplaceTransform f.toZetaTestFunction' (a : ℂ) *
            star (zetaLaplaceTransform f.toZetaTestFunction' w))
        hstar_arg

/-- The two-variable convolution-pair Laplace integral unfolds to the kernel integral. -/
theorem zetaLaplaceTransform_convolutionPair_unfold
    (f h : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.convolutionPair f h).toZetaTestFunction'
        z =
      ∫ t : ℝ,
        (∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2))) *
          Complex.exp (z * t) := by
  unfold zetaLaplaceTransform
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun t : ℝ =>
    congrArg (fun y : ℂ => y * Complex.exp (z * t))
      ((LFunctions.ZetaAdmissibleFunction.convolutionPair_toZetaTestFunction'_apply
          f h t).trans
        (LFunctions.ZetaAdmissibleFunction.convolutionPairKernel_apply f h t))

/-- The separated two-variable convolution-pair integral factors into seed transforms. -/
theorem zetaLaplaceTransform_convolutionPair_factorSeparated
    (f h : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    (∫ v : ℝ, ∫ w : ℝ,
        (f v * Complex.exp (z * v)) *
          star (h w * Complex.exp ((-star z) * w))) =
      zetaLaplaceTransform f.toZetaTestFunction' z *
        star (zetaLaplaceTransform h.toZetaTestFunction' (-star z)) := by
  let A : ℝ → ℂ := fun v : ℝ => f v * Complex.exp (z * v)
  let B : ℝ → ℂ := fun w : ℝ => h w * Complex.exp ((-star z) * w)
  have hinner :
      (fun v : ℝ => ∫ w : ℝ, A v * star (B w)) =
        fun v : ℝ => A v * ∫ w : ℝ, star (B w) := by
    funext v
    exact integral_mul_left (A v) (fun w : ℝ => star (B w))
  have houter :
      (∫ v : ℝ, A v * ∫ w : ℝ, star (B w)) =
        (∫ v : ℝ, A v) * (∫ w : ℝ, star (B w)) := by
    exact integral_mul_right (∫ w : ℝ, star (B w)) A
  have hstar :
      (∫ w : ℝ, star (B w)) =
        star (∫ w : ℝ, B w) := by
    exact integral_conj
  unfold zetaLaplaceTransform
  change (∫ v : ℝ, ∫ w : ℝ, A v * star (B w)) =
      (∫ t : ℝ, A t) * star (∫ t : ℝ, B t)
  calc
    (∫ v : ℝ, ∫ w : ℝ, A v * star (B w)) =
        ∫ v : ℝ, A v * ∫ w : ℝ, star (B w) := by
      exact congrArg (fun F : ℝ → ℂ => ∫ v : ℝ, F v) hinner
    _ = (∫ v : ℝ, A v) * (∫ w : ℝ, star (B w)) := houter
    _ = (∫ v : ℝ, A v) * star (∫ w : ℝ, B w) := by
      exact congrArg (fun y : ℂ => (∫ v : ℝ, A v) * y) hstar

/-- The two-variable convolution-pair Laplace integral becomes separated after the centered
linear change of variables.

The owner proof factors through the standard convolution theorem; this displayed equality is the
coordinate form consumed downstream. -/
theorem zetaLaplaceTransform_convolutionPair_changeVariables
    (f h : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    (∫ t : ℝ,
        (∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2))) *
          Complex.exp (z * t)) =
      ∫ v : ℝ, ∫ w : ℝ,
        (f v * Complex.exp (z * v)) *
          star (h w * Complex.exp ((-star z) * w)) := by
  have hleft :
      (∫ t : ℝ,
          (∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2))) *
            Complex.exp (z * t)) =
        ∫ t : ℝ,
          LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
            Complex.exp (z * t) := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
      congrArg (fun y : ℂ => y * Complex.exp (z * t))
        ((LFunctions.ZetaAdmissibleFunction.convolutionPairKernel_apply f h t).symm.trans
          (congrFun
            (LFunctions.ZetaAdmissibleFunction.convolutionPairKernel_eq_standard f h)
            t)))
  have hstandard :
      (∫ t : ℝ,
          LFunctions.ZetaAdmissibleFunction.convolutionPairKernelStandard f h t *
            Complex.exp (z * t)) =
        zetaLaplaceTransform f.toZetaTestFunction' z *
          star (zetaLaplaceTransform h.toZetaTestFunction' (-star z)) :=
    zetaLaplaceTransform_standardConvolutionPair f h z
  have hright :
      (∫ v : ℝ, ∫ w : ℝ,
          (f v * Complex.exp (z * v)) *
            star (h w * Complex.exp ((-star z) * w))) =
        zetaLaplaceTransform f.toZetaTestFunction' z *
          star (zetaLaplaceTransform h.toZetaTestFunction' (-star z)) :=
    zetaLaplaceTransform_convolutionPair_factorSeparated f h z
  exact hleft.trans (hstandard.trans hright.symm)

/-- Laplace transform of the two-variable convolution-pair kernel. -/
theorem zetaLaplaceTransform_convolutionPair
    (f h : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.convolutionPair f h).toZetaTestFunction'
        z =
      zetaLaplaceTransform f.toZetaTestFunction' z *
        star (zetaLaplaceTransform h.toZetaTestFunction' (-star z)) := by
  exact
    (zetaLaplaceTransform_convolutionPair_unfold f h z).trans
      ((zetaLaplaceTransform_convolutionPair_changeVariables f h z).trans
        (zetaLaplaceTransform_convolutionPair_factorSeparated f h z))

/-- The pointwise integrand for additivity. -/
theorem zetaLaplaceTransform_add_integrand
    (φ ψ : LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (φ + ψ) t * Complex.exp (z * t)) =
      fun t : ℝ => φ t * Complex.exp (z * t) + ψ t * Complex.exp (z * t) := by
  funext t
  exact add_mul (φ t) (ψ t) (Complex.exp (z * t))

/-- The zeta Laplace transform is additive. -/
theorem zetaLaplaceTransform_add
    (φ ψ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ))
    (hψ : Integrable (fun t : ℝ => ψ t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (φ + ψ) z =
      zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z := by
  unfold zetaLaplaceTransform
  calc
    zetaLaplaceTransform (φ + ψ) z
        = ∫ t : ℝ, φ t * Complex.exp (z * t) + ψ t * Complex.exp (z * t) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              congrArg (fun g => g t) (zetaLaplaceTransform_add_integrand φ ψ z))
    _ = zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z := by
          exact integral_add hφ hψ

/-- The pointwise integrand for scalar multiplication. -/
theorem zetaLaplaceTransform_smul_integrand
    (a : ℂ) (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (a • φ) t * Complex.exp (z * t)) =
      fun t : ℝ => a * (φ t * Complex.exp (z * t)) := by
  funext t
  change (a * φ t) * Complex.exp (z * t) = a * (φ t * Complex.exp (z * t))
  exact mul_assoc a (φ t) (Complex.exp (z * t))

/-- The zeta Laplace transform is homogeneous under scalar multiplication. -/
theorem zetaLaplaceTransform_smul
    (a : ℂ) (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    :
    zetaLaplaceTransform (a • φ) z = a * zetaLaplaceTransform φ z := by
  unfold zetaLaplaceTransform
  calc
    ∫ t : ℝ, (a • φ) t * Complex.exp (z * t)
        = ∫ t : ℝ, a * (φ t * Complex.exp (z * t)) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              congrArg (fun g => g t) (zetaLaplaceTransform_smul_integrand a φ z))
    _ = a * zetaLaplaceTransform φ z := by
          exact integral_mul_left a (fun t : ℝ => φ t * Complex.exp (z * t))

/-- Pointwise equal test functions have equal zeta Laplace transforms. -/
theorem zetaLaplaceTransform_congr
    {φ ψ : LFunctions.ZetaTestFunction}
    (hφψ : ∀ t : ℝ, φ t = ψ t) :
    zetaLaplaceTransform φ = zetaLaplaceTransform ψ := by
  funext z
  unfold zetaLaplaceTransform
  exact integral_congr_ae
    (Filter.Eventually.of_forall
      (fun t : ℝ =>
        congrArg
          (fun u : ℂ => u * Complex.exp (z * t))
          (hφψ t)))

/-- The pointwise Laplace integrand is continuous in the pair `(z, t)`. -/
theorem continuous_laplaceIntegrand
    (φ : LFunctions.ZetaTestFunction) :
    Continuous (fun p : ℂ × ℝ => φ p.2 * Complex.exp (p.1 * p.2)) := by
  have hφ : Continuous (fun p : ℂ × ℝ => φ p.2) :=
    φ.continuous.comp continuous_snd
  have hmul : Continuous (fun p : ℂ × ℝ => p.1 * p.2) :=
    continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd)
  have hexp : Continuous (fun p : ℂ × ℝ => Complex.exp (p.1 * p.2)) :=
    Complex.continuous_exp.comp hmul
  exact hφ.mul hexp

/-- The Laplace integrand, viewed as a curried function, is continuous on the full product. -/
theorem continuousOn_laplaceIntegrand_uncurried
    (φ : LFunctions.ZetaTestFunction) :
    ContinuousOn (Function.uncurry fun z (t : ℝ) => φ t * Complex.exp (z * t))
      ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ)) := by
  change ContinuousOn (fun p : ℂ × ℝ => φ p.2 * Complex.exp (p.1 * p.2))
    ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ))
  exact (continuous_laplaceIntegrand φ).continuousOn

/-- The weighted pointwise Laplace integrand is continuous in the pair `(z, t)`. -/
theorem continuous_weightedLaplaceIntegrand
    (φ : LFunctions.ZetaTestFunction) :
    Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)) := by
  have ht : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hφ : Continuous (fun p : ℂ × ℝ => φ p.2) :=
    φ.continuous.comp continuous_snd
  have hmul : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2) :=
    ht.mul hφ
  have hmul' : Continuous (fun p : ℂ × ℝ => p.1 * p.2) :=
    continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd)
  have hexp : Continuous (fun p : ℂ × ℝ => Complex.exp (p.1 * p.2)) :=
    Complex.continuous_exp.comp hmul'
  exact hmul.mul hexp

/-- The weighted Laplace integrand, viewed as a curried function, is continuous on the full product. -/
theorem continuousOn_weightedLaplaceIntegrand_uncurried
    (φ : LFunctions.ZetaTestFunction) :
    ContinuousOn (Function.uncurry fun z (t : ℝ) => (t : ℂ) * φ t * Complex.exp (z * t))
      ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ)) := by
  change ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2))
    ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ))
  exact (continuous_weightedLaplaceIntegrand φ).continuousOn

/-- The one-variable Laplace kernel is continuous. -/
theorem continuous_laplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    Continuous (fun t : ℝ => φ t * Complex.exp (z * t)) := by
  have hφ : Continuous (fun t : ℝ => φ t) :=
    φ.continuous
  have hmul : Continuous (fun t : ℝ => (z : ℂ) * t) := by
    exact continuous_const.mul Complex.continuous_ofReal
  have hexp : Continuous (fun t : ℝ => Complex.exp (z * t)) :=
    Complex.continuous_exp.comp hmul
  exact hφ.mul hexp

/-- The Laplace kernel inherits compact support from the underlying test function. -/
theorem hasCompactSupport_laplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun t : ℝ => φ t * Complex.exp (z * t)) := by
  exact hφ.mul_right

theorem integrable_laplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : HasCompactSupport φ) :
    Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ) := by
  exact (continuous_laplaceKernel φ z).integrable_of_hasCompactSupport
    (hasCompactSupport_laplaceKernel_of_hasCompactSupport φ z hφ)

/-- The Laplace kernel is strongly measurable whenever it is continuous. -/
theorem aestronglyMeasurable_laplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ) := by
  exact (continuous_laplaceKernel φ z).aestronglyMeasurable

/-- The one-variable weighted Laplace kernel is continuous. -/
theorem continuous_weightedLaplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    Continuous (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) := by
  have ht : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal
  have hφ : Continuous (fun t : ℝ => φ t) :=
    φ.continuous
  have hmul : Continuous (fun t : ℝ => (t : ℂ) * φ t) :=
    ht.mul hφ
  have hmul' : Continuous (fun t : ℝ => (z : ℂ) * t) := by
    exact continuous_const.mul Complex.continuous_ofReal
  have hexp : Continuous (fun t : ℝ => Complex.exp (z * t)) :=
    Complex.continuous_exp.comp hmul'
  exact hmul.mul hexp

/-- A compact-support kernel stays compactly supported after multiplying by `t`. -/
theorem hasCompactSupport_weightedLaplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) := by
  have hkernel_eq :
      ((fun t : ℝ => (t : ℂ)) * (fun t : ℝ => φ t * Complex.exp (z * t))) =
        fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t) := by
    funext t
    exact (mul_assoc (t : ℂ) (φ t) (Complex.exp (z * t))).symm
  have h :
      HasCompactSupport
        ((fun t : ℝ => (t : ℂ)) * (fun t : ℝ => φ t * Complex.exp (z * t))) := by
    exact HasCompactSupport.mul_left
      (f := fun t : ℝ => (t : ℂ))
      (f' := fun t : ℝ => φ t * Complex.exp (z * t))
      (hf := hasCompactSupport_laplaceKernel_of_hasCompactSupport φ z hφ)
  exact Eq.subst (motive := fun F : ℝ → ℂ => HasCompactSupport F) hkernel_eq h

/-- A Laplace kernel vanishes outside the support of the underlying test function. -/
theorem laplaceKernel_eq_zero_of_nmem_tsupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    φ t * Complex.exp (z * t) = 0 := by
  have hφ : φ t = 0 := image_eq_zero_of_nmem_tsupport ht
  calc
    φ t * Complex.exp (z * t) = 0 * Complex.exp (z * t) := by
      exact congrArg (fun x => x * Complex.exp (z * t)) hφ
    _ = 0 := by
      exact zero_mul _

/-- A weighted Laplace kernel vanishes outside the support of the underlying test function. -/
theorem weightedLaplaceKernel_eq_zero_of_nmem_tsupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    (t : ℂ) * φ t * Complex.exp (z * t) = 0 := by
  have hφ : φ t = 0 := image_eq_zero_of_nmem_tsupport ht
  calc
    (t : ℂ) * φ t * Complex.exp (z * t) = (t : ℂ) * 0 * Complex.exp (z * t) := by
      exact congrArg (fun x => (t : ℂ) * x * Complex.exp (z * t)) hφ
    _ = 0 * Complex.exp (z * t) := by
      exact congrArg (fun x => x * Complex.exp (z * t)) (mul_zero (t : ℂ))
    _ = 0 := by
      exact zero_mul _

/-- The indicator of a support set is equal to the constant on points inside the set. -/
theorem indicator_eq_of_mem {K : Set ℝ} {C : ℝ} {t : ℝ} (ht : t ∈ K) :
    K.indicator (fun _ => C) t = C := by
  exact Set.indicator_of_mem (s := K) (f := fun _ : ℝ => C) ht

/-- The indicator of a support set is zero outside the set. -/
theorem indicator_eq_zero_of_not_mem {K : Set ℝ} {C : ℝ} {t : ℝ} (ht : t ∉ K) :
    K.indicator (fun _ => C) t = 0 := by
  exact Set.indicator_of_not_mem (s := K) (f := fun _ : ℝ => C) ht

/-- Reflection turns the Laplace kernel at `z` into the unreflected kernel at `-z`. -/
theorem reflect_laplaceKernel_eq_comp_neg_pointwise
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) (t : ℝ) :
    (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t) =
      φ (-t) * Complex.exp (-z * (-t)) := by
  have hmul : z * t = (-z) * (-t) := by
    exact (neg_mul_neg z t).symm
  calc
    (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t)
        = φ (-t) * Complex.exp (z * t) := by
            exact congrArg (fun x => x * Complex.exp (z * t))
              (LFunctions.ZetaTestFunction.reflect_apply φ t)
    _ = φ (-t) * Complex.exp (-z * (-t)) := by
          exact congrArg (fun x => φ (-t) * Complex.exp x) hmul

theorem reflect_laplaceKernel_eq_comp_neg
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t)) =
      fun t : ℝ => φ (-t) * Complex.exp (-z * (-t)) := by
  funext t
  exact reflect_laplaceKernel_eq_comp_neg_pointwise φ z t

/-- The weighted Laplace kernel vanishes outside the support of the underlying test function. -/
theorem weightedLaplaceKernel_eq_zero_of_nmem_tsupport'
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    (fun x : ℝ => (x : ℂ) * φ x * Complex.exp (z * x)) t = 0 := by
  exact weightedLaplaceKernel_eq_zero_of_nmem_tsupport φ z ht

/-- The weighted Laplace kernel with compact support is integrable. -/
theorem integrable_weightedLaplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : HasCompactSupport φ) :
    Integrable (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) (volume : Measure ℝ) := by
  have hcs : HasCompactSupport (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) :=
    hasCompactSupport_weightedLaplaceKernel_of_hasCompactSupport φ z hφ
  exact (continuous_weightedLaplaceKernel φ z).integrable_of_hasCompactSupport hcs

/-- The weighted Laplace kernel is strongly measurable whenever it is continuous. -/
theorem aestronglyMeasurable_weightedLaplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t))
      (volume : Measure ℝ) := by
  exact (continuous_weightedLaplaceKernel φ z).aestronglyMeasurable

/-- The zeta Laplace transform of an autocorrelation unfolds pointwise. -/
theorem zetaLaplaceTransform_autocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform
        (LFunctions.ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  unfold zetaLaplaceTransform
  exact congrArg (fun g : ℝ → ℂ => ∫ t : ℝ, g t * Complex.exp (z * t))
    (LFunctions.ZetaAdmissibleFunction.autocorrelation_eq f)

/-- The zeta Laplace transform of an admissible function is continuous in the spectral variable. -/
theorem zetaLaplaceTransform_continuous
    (φ : LFunctions.ZetaAdmissibleFunction) :
    Continuous (fun z => zetaLaplaceTransform φ.toZetaTestFunction' z) := by
  have hcs : HasCompactSupport φ.toZetaTestFunction' := by
    exact φ.toZetaTestFunction.hasCompactSupport
  let K : Set ℝ := tsupport φ.toZetaTestFunction'
  have hK : IsCompact K := by
    exact hcs.isCompact
  have hcont :
      Continuous (fun p : ℂ × ℝ => φ.toZetaTestFunction' p.2 * Complex.exp (p.1 * p.2)) :=
    continuous_laplaceIntegrand φ.toZetaTestFunction'
  have hcontOn :=
    continuousOn_laplaceIntegrand_uncurried φ.toZetaTestFunction'
  have hzero :
      ∀ p : ℂ, ∀ t : ℝ, p ∈ (Set.univ : Set ℂ) → t ∉ K →
        φ.toZetaTestFunction' t * Complex.exp (p * t) = 0 := by
    intro p t _ ht
    exact laplaceKernel_eq_zero_of_nmem_tsupport φ.toZetaTestFunction' p ht
  have hcont' :
      ContinuousOn (fun z => ∫ t : ℝ, φ.toZetaTestFunction' t * Complex.exp (z * t))
        (Set.univ : Set ℂ) := by
    exact continuousOn_integral_of_compact_support
      (μ := (volume : Measure ℝ))
      (f := fun z t => φ.toZetaTestFunction' t * Complex.exp (z * t))
      (s := (Set.univ : Set ℂ))
      (k := K)
      hK
      hcontOn
      hzero
  exact continuous_iff_continuousOn_univ.mpr hcont'

end Mellin
