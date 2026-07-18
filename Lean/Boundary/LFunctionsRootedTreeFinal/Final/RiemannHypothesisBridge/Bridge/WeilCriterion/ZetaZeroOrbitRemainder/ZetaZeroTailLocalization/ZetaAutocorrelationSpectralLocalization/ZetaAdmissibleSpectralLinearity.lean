import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.CompletedZeroDagger

/-!
# Linear completed-zero spectral coordinates

This file owns the linear probe-to-spectral-coordinate map used by weighted
completed-zero tail constructions.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ENNReal

def zetaCompletedZeroAutocorrelationSideCoordinate
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) : ℂ :=
  - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
    (zetaSpectralEval f (rho : ℂ) *
      star (zetaSpectralEval f (-star (rho : ℂ))))

/-- Spectral evaluation is additive on admissible probes. -/
theorem zetaSpectralEval_add
    (f g : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (f + g) z =
      zetaSpectralEval f z + zetaSpectralEval g z := by
  exact
    zetaSpectralTransform_add
      f.toZetaTestFunction'
      g.toZetaTestFunction'
      z
      (integrable_laplaceKernel_at f z)
      (integrable_laplaceKernel_at g z)

/-- Spectral evaluation is homogeneous on admissible probes. -/
theorem zetaSpectralEval_smul
    (c : ℂ) (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (c • f) z =
      c * zetaSpectralEval f z := by
  exact zetaSpectralTransform_smul c f.toZetaTestFunction' z

/-- The linear spectral-coordinate map indexed by completed zeros. -/
def zetaCompletedZeroSpectralCoordinateLinearMap :
    ZetaAdmissibleFunction →ₗ[ℂ] ({ρ : ℂ // ZetaCompletedZero ρ} → ℂ) where
  toFun := fun f ρ => zetaSpectralEval f (ρ : ℂ)
  map_add' := fun f g =>
    funext (fun ρ => zetaSpectralEval_add f g (ρ : ℂ))
  map_smul' := fun c f =>
    funext (fun ρ => zetaSpectralEval_smul c f (ρ : ℂ))

/-- The completed-zero coordinate map evaluates at the underlying zero. -/
theorem zetaCompletedZeroSpectralCoordinateLinearMap_apply
    (f : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroSpectralCoordinateLinearMap f ρ =
      zetaSpectralEval f (ρ : ℂ) := by
  rfl

/-- A completed-zero side contribution is additive in its probe argument. -/
theorem zetaZeroSideContribution_add
    (ρ : ℂ)
    (f g : ZetaAdmissibleFunction) :
    zetaZeroSideContribution ρ (f + g) =
      zetaZeroSideContribution ρ f + zetaZeroSideContribution ρ g := by
  calc
    zetaZeroSideContribution ρ (f + g) =
        - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval (f + g) ρ := by
          rfl
    _ = - (zetaZeroMultiplicity ρ : ℂ) *
          (zetaSpectralEval f ρ + zetaSpectralEval g ρ) := by
          exact congrArg (fun w : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * w)
            (zetaSpectralEval_add f g ρ)
    _ = - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval f ρ +
          - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval g ρ := by
          exact mul_add
            (- (zetaZeroMultiplicity ρ : ℂ))
            (zetaSpectralEval f ρ)
            (zetaSpectralEval g ρ)
    _ = zetaZeroSideContribution ρ f + zetaZeroSideContribution ρ g := by
          rfl

/-- A completed-zero side contribution is homogeneous in its probe argument. -/
theorem zetaZeroSideContribution_smul
    (ρ : ℂ)
    (c : ℂ)
    (f : ZetaAdmissibleFunction) :
    zetaZeroSideContribution ρ (c • f) =
      c * zetaZeroSideContribution ρ f := by
  calc
    zetaZeroSideContribution ρ (c • f) =
        - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval (c • f) ρ := by
          rfl
    _ = - (zetaZeroMultiplicity ρ : ℂ) *
          (c * zetaSpectralEval f ρ) := by
          exact congrArg (fun w : ℂ => - (zetaZeroMultiplicity ρ : ℂ) * w)
            (zetaSpectralEval_smul c f ρ)
    _ = c * (- (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval f ρ) := by
          calc
            - (zetaZeroMultiplicity ρ : ℂ) *
                (c * zetaSpectralEval f ρ) =
                (- (zetaZeroMultiplicity ρ : ℂ) * c) *
                  zetaSpectralEval f ρ := by
                    exact (mul_assoc
                      (- (zetaZeroMultiplicity ρ : ℂ))
                      c
                      (zetaSpectralEval f ρ)).symm
            _ = (c * - (zetaZeroMultiplicity ρ : ℂ)) *
                  zetaSpectralEval f ρ := by
                    exact congrArg (fun w : ℂ => w * zetaSpectralEval f ρ)
                      (mul_comm (- (zetaZeroMultiplicity ρ : ℂ)) c)
            _ = c * (- (zetaZeroMultiplicity ρ : ℂ) *
                  zetaSpectralEval f ρ) := by
                    exact mul_assoc
                      c
                      (- (zetaZeroMultiplicity ρ : ℂ))
                      (zetaSpectralEval f ρ)
    _ = c * zetaZeroSideContribution ρ f := by
          rfl

/-- The norm of a direct completed-zero side coordinate is its positive
multiplicity times the norm of the underlying spectral evaluation. -/
theorem norm_zetaZeroSideContribution
    (ρ : ℂ)
    (f : ZetaAdmissibleFunction) :
    norm (zetaZeroSideContribution ρ f) =
      (zetaZeroMultiplicity ρ : ℝ) * norm (zetaSpectralEval f ρ) := by
  unfold zetaZeroSideContribution
  calc
    norm (- (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval f ρ) =
        norm (- (zetaZeroMultiplicity ρ : ℂ)) * norm (zetaSpectralEval f ρ) :=
      norm_mul _ _
    _ = norm (zetaZeroMultiplicity ρ : ℂ) * norm (zetaSpectralEval f ρ) := by
      exact
        congrArg (fun coefficient : ℝ => coefficient * norm (zetaSpectralEval f ρ))
          (norm_neg (zetaZeroMultiplicity ρ : ℂ))
    _ = (zetaZeroMultiplicity ρ : ℝ) * norm (zetaSpectralEval f ρ) := by
      exact
        congrArg (fun coefficient : ℝ => coefficient * norm (zetaSpectralEval f ρ))
          (Complex.norm_natCast (zetaZeroMultiplicity (ρ : ℂ)))

/-- At a completed zero, the direct side-coordinate norm dominates the
underlying spectral-evaluation norm. -/
theorem norm_zetaSpectralEval_le_norm_zetaZeroSideContribution
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (f : ZetaAdmissibleFunction) :
    norm (zetaSpectralEval f (ρ : ℂ)) ≤
      norm (zetaZeroSideContribution (ρ : ℂ) f) := by
  have hMultiplicityPositive : 0 < zetaZeroMultiplicity (ρ : ℂ) :=
    zetaZeroMultiplicity_pos_of_completedZero ρ
  have hMultiplicityOne : 1 ≤ zetaZeroMultiplicity (ρ : ℂ) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hMultiplicityPositive)
  have hMultiplicityOneCast :
      ((1 : ℕ) : ℝ) ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    (Nat.cast_le (α := ℝ)).mpr hMultiplicityOne
  have hMultiplicityOneReal : (1 : ℝ) ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
    exact Eq.mp
      (congrArg
        (fun left : ℝ => left ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ))
        Nat.cast_one)
      hMultiplicityOneCast
  calc
    norm (zetaSpectralEval f (ρ : ℂ)) =
        (1 : ℝ) * norm (zetaSpectralEval f (ρ : ℂ)) := (one_mul _).symm
    _ ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
          norm (zetaSpectralEval f (ρ : ℂ)) :=
      mul_le_mul_of_nonneg_right hMultiplicityOneReal (norm_nonneg _)
    _ = norm (zetaZeroSideContribution (ρ : ℂ) f) :=
      (norm_zetaZeroSideContribution (ρ : ℂ) f).symm

/-- The norm of an autocorrelation coordinate is the multiplicity times the two
seed-transform norms.  This helper is placed before the direct-product bound
because that bound consumes the explicit norm computation. -/
theorem norm_zetaCompletedZeroAutocorrelationSideCoordinate_aux
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    norm (zetaCompletedZeroAutocorrelationSideCoordinate f rho) =
      (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
        (norm (zetaSpectralEval f (rho : ℂ)) *
          norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
  unfold zetaCompletedZeroAutocorrelationSideCoordinate
  calc
    norm (- (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
        (zetaSpectralEval f (rho : ℂ) *
          star (zetaSpectralEval f (-star (rho : ℂ))))) =
        norm (- (zetaZeroMultiplicity (rho : ℂ) : ℂ)) *
          norm (zetaSpectralEval f (rho : ℂ) *
            star (zetaSpectralEval f (-star (rho : ℂ)))) :=
      norm_mul _ _
    _ = norm (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          (norm (zetaSpectralEval f (rho : ℂ)) *
            norm (star (zetaSpectralEval f (-star (rho : ℂ))))) := by
      exact congrArg₂ HMul.hMul
        (norm_neg (zetaZeroMultiplicity (rho : ℂ) : ℂ))
        (norm_mul _ _)
    _ = (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (norm (zetaSpectralEval f (rho : ℂ)) *
            norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
      exact congrArg₂ HMul.hMul
        (Complex.norm_natCast (zetaZeroMultiplicity (rho : ℂ)))
        (congrArg (fun value : ℝ => norm (zetaSpectralEval f (rho : ℂ)) * value)
          (norm_star (zetaSpectralEval f (-star (rho : ℂ)))))

/-- Each autocorrelation coordinate is bounded by the product of the direct
side-coordinate norms at a completed zero and its dagger partner. -/
theorem norm_zetaCompletedZeroAutocorrelationSideCoordinate_le_directProduct
    (f : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    norm (zetaCompletedZeroAutocorrelationSideCoordinate f ρ) ≤
      norm (zetaZeroSideContribution (ρ : ℂ) f) *
        norm (zetaZeroSideContribution
          (zetaCompletedZeroDagger ρ : ℂ) f) := by
  let ρDagger : {ρ : ℂ // ZetaCompletedZero ρ} := zetaCompletedZeroDagger ρ
  have hDaggerValue : (ρDagger : ℂ) = -star (ρ : ℂ) :=
    zetaCompletedZeroDagger_coe ρ
  have hDaggerBound :
      norm (zetaSpectralEval f (-star (ρ : ℂ))) ≤
        norm (zetaZeroSideContribution (ρDagger : ℂ) f) := by
    calc
      norm (zetaSpectralEval f (-star (ρ : ℂ))) =
          norm (zetaSpectralEval f (ρDagger : ℂ)) := by
            exact congrArg (fun value : ℂ => norm (zetaSpectralEval f value))
              hDaggerValue.symm
      _ ≤ norm (zetaZeroSideContribution (ρDagger : ℂ) f) :=
        norm_zetaSpectralEval_le_norm_zetaZeroSideContribution ρDagger f
  calc
    norm (zetaCompletedZeroAutocorrelationSideCoordinate f ρ) =
        norm (zetaZeroSideContribution (ρ : ℂ) f) *
          norm (zetaSpectralEval f (-star (ρ : ℂ))) := by
      calc
        norm (zetaCompletedZeroAutocorrelationSideCoordinate f ρ) =
            (zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
              (norm (zetaSpectralEval f (ρ : ℂ)) *
                norm (zetaSpectralEval f (-star (ρ : ℂ)))) :=
          norm_zetaCompletedZeroAutocorrelationSideCoordinate_aux f ρ
        _ = ((zetaZeroMultiplicity (ρ : ℂ) : ℝ) *
              norm (zetaSpectralEval f (ρ : ℂ))) *
              norm (zetaSpectralEval f (-star (ρ : ℂ))) := by
          exact (mul_assoc _ _ _).symm
        _ = norm (zetaZeroSideContribution (ρ : ℂ) f) *
              norm (zetaSpectralEval f (-star (ρ : ℂ))) := by
          exact
            congrArg
              (fun value : ℝ => value * norm (zetaSpectralEval f (-star (ρ : ℂ))))
              (norm_zetaZeroSideContribution (ρ : ℂ) f).symm
    _ ≤ norm (zetaZeroSideContribution (ρ : ℂ) f) *
          norm (zetaZeroSideContribution (ρDagger : ℂ) f) :=
      mul_le_mul_of_nonneg_left hDaggerBound (norm_nonneg _)
    _ = norm (zetaZeroSideContribution (ρ : ℂ) f) *
          norm (zetaZeroSideContribution
            (zetaCompletedZeroDagger ρ : ℂ) f) := by
      rfl

/-- At a completed zero, a vanishing multiplicity-weighted side coordinate forces
the underlying spectral evaluation to vanish. -/
theorem zetaSpectralEval_eq_zero_of_zetaZeroSideContribution_eq_zero
    (rho : {rho : ℂ // ZetaCompletedZero rho})
    (f : ZetaAdmissibleFunction)
    (hcoordinate : zetaZeroSideContribution (rho : ℂ) f = 0) :
    zetaSpectralEval f (rho : ℂ) = 0 := by
  have hmultiplicityPositive : 0 < zetaZeroMultiplicity (rho : ℂ) :=
    zetaZeroMultiplicity_pos_of_completedZero rho
  have hmultiplicityNonzero : (zetaZeroMultiplicity (rho : ℂ) : ℂ) ≠ 0 := by
    exact
      Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt hmultiplicityPositive)
  have hfactorNonzero : - (zetaZeroMultiplicity (rho : ℂ) : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr hmultiplicityNonzero
  have hproduct :
      - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          zetaSpectralEval f (rho : ℂ) = 0 := by
    exact hcoordinate
  exact (mul_eq_zero.mp hproduct).resolve_left hfactorNonzero

/-- A vanishing spectral evaluation has vanishing multiplicity-weighted side
coordinate. -/
theorem zetaZeroSideContribution_eq_zero_of_zetaSpectralEval_eq_zero
    (rho : ℂ)
    (f : ZetaAdmissibleFunction)
    (hspectral : zetaSpectralEval f rho = 0) :
    zetaZeroSideContribution rho f = 0 := by
  unfold zetaZeroSideContribution
  calc
    - (zetaZeroMultiplicity rho : ℂ) * zetaSpectralEval f rho =
        - (zetaZeroMultiplicity rho : ℂ) * 0 := by
          exact congrArg (fun z : ℂ => - (zetaZeroMultiplicity rho : ℂ) * z) hspectral
    _ = 0 := mul_zero (- (zetaZeroMultiplicity rho : ℂ))

/-- Spectral evaluation of a two-variable convolution pair factors through the
left seed transform and the dagger-reflected right seed transform. -/
theorem zetaSpectralEval_convolutionPair_eq_seed_daggerProduct
    (f h : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (convolutionPair f h) z =
      zetaSpectralEval f z * star (zetaSpectralEval h (-star z)) := by
  change
    Boundary.zetaLaplaceTransform
        (convolutionPair f h).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z *
        star (Boundary.zetaLaplaceTransform h.toZetaTestFunction' (-star z))
  exact Boundary.zetaLaplaceTransform_convolutionPair f h z

/-- The completed-zero side coordinate of a two-variable convolution pair. -/
def zetaCompletedZeroConvolutionPairSideCoordinate
    (f h : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) : ℂ :=
  - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
    (zetaSpectralEval f (rho : ℂ) *
      star (zetaSpectralEval h (-star (rho : ℂ))))

/-- The cross coordinate is exactly the zero-side contribution of the
corresponding two-variable convolution pair. -/
theorem zetaCompletedZeroConvolutionPairSideCoordinate_eq
    (f h : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    zetaCompletedZeroConvolutionPairSideCoordinate f h rho =
      zetaZeroSideContribution (rho : ℂ) (convolutionPair f h) := by
  unfold zetaCompletedZeroConvolutionPairSideCoordinate
  unfold zetaZeroSideContribution
  exact
    congrArg
      (fun spectralValue : ℂ =>
        - (zetaZeroMultiplicity (rho : ℂ) : ℂ) * spectralValue)
      (zetaSpectralEval_convolutionPair_eq_seed_daggerProduct
        f h (rho : ℂ)).symm

/-- The diagonal of the two-variable coordinate is the autocorrelation
coordinate. -/
theorem zetaCompletedZeroConvolutionPairSideCoordinate_self
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    zetaCompletedZeroConvolutionPairSideCoordinate f f rho =
      zetaCompletedZeroAutocorrelationSideCoordinate f rho := by
  rfl

/-- The autocorrelation coordinate of a sum decomposes into its two diagonal
coordinates and the two oriented convolution-pair coordinates. -/
theorem zetaCompletedZeroAutocorrelationSideCoordinate_add
    (f g : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    zetaCompletedZeroAutocorrelationSideCoordinate (f + g) rho =
      (zetaCompletedZeroAutocorrelationSideCoordinate f rho +
        zetaCompletedZeroConvolutionPairSideCoordinate g f rho) +
        (zetaCompletedZeroConvolutionPairSideCoordinate f g rho +
          zetaCompletedZeroAutocorrelationSideCoordinate g rho) := by
  have hleft :
      zetaSpectralEval (f + g) (rho : ℂ) =
        zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ) :=
    zetaSpectralEval_add f g (rho : ℂ)
  have hrightSeed :
      zetaSpectralEval (f + g) (-star (rho : ℂ)) =
        zetaSpectralEval f (-star (rho : ℂ)) +
          zetaSpectralEval g (-star (rho : ℂ)) :=
    zetaSpectralEval_add f g (-star (rho : ℂ))
  have hright :
      star (zetaSpectralEval (f + g) (-star (rho : ℂ))) =
        star (zetaSpectralEval f (-star (rho : ℂ))) +
          star (zetaSpectralEval g (-star (rho : ℂ))) := by
    exact
      Eq.trans
        (congrArg star hrightSeed)
        (star_add
          (zetaSpectralEval f (-star (rho : ℂ)))
          (zetaSpectralEval g (-star (rho : ℂ))))
  have hproduct :
      (zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ)) *
          (star (zetaSpectralEval f (-star (rho : ℂ))) +
            star (zetaSpectralEval g (-star (rho : ℂ)))) =
        (zetaSpectralEval f (rho : ℂ) *
          star (zetaSpectralEval f (-star (rho : ℂ))) +
          zetaSpectralEval g (rho : ℂ) *
            star (zetaSpectralEval f (-star (rho : ℂ)))) +
          (zetaSpectralEval f (rho : ℂ) *
            star (zetaSpectralEval g (-star (rho : ℂ))) +
            zetaSpectralEval g (rho : ℂ) *
              star (zetaSpectralEval g (-star (rho : ℂ)))) := by
    calc
      (zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ)) *
          (star (zetaSpectralEval f (-star (rho : ℂ))) +
            star (zetaSpectralEval g (-star (rho : ℂ)))) =
          (zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ)) *
              star (zetaSpectralEval f (-star (rho : ℂ))) +
            (zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ)) *
              star (zetaSpectralEval g (-star (rho : ℂ))) := by
            exact mul_add
              (zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ))
              (star (zetaSpectralEval f (-star (rho : ℂ))))
              (star (zetaSpectralEval g (-star (rho : ℂ))))
      _ =
          (zetaSpectralEval f (rho : ℂ) *
            star (zetaSpectralEval f (-star (rho : ℂ))) +
            zetaSpectralEval g (rho : ℂ) *
              star (zetaSpectralEval f (-star (rho : ℂ)))) +
            (zetaSpectralEval f (rho : ℂ) *
              star (zetaSpectralEval g (-star (rho : ℂ))) +
              zetaSpectralEval g (rho : ℂ) *
                star (zetaSpectralEval g (-star (rho : ℂ)))) := by
            exact
              congrArg₂ HAdd.hAdd
                (add_mul
                  (zetaSpectralEval f (rho : ℂ))
                  (zetaSpectralEval g (rho : ℂ))
                  (star (zetaSpectralEval f (-star (rho : ℂ)))))
                (add_mul
                  (zetaSpectralEval f (rho : ℂ))
                  (zetaSpectralEval g (rho : ℂ))
                  (star (zetaSpectralEval g (-star (rho : ℂ)))))
  unfold zetaCompletedZeroAutocorrelationSideCoordinate
  unfold zetaCompletedZeroConvolutionPairSideCoordinate
  calc
    - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
        (zetaSpectralEval (f + g) (rho : ℂ) *
          star (zetaSpectralEval (f + g) (-star (rho : ℂ)))) =
        - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          ((zetaSpectralEval f (rho : ℂ) + zetaSpectralEval g (rho : ℂ)) *
            (star (zetaSpectralEval f (-star (rho : ℂ))) +
              star (zetaSpectralEval g (-star (rho : ℂ))))) := by
          exact
            congrArg₂ HMul.hMul
              (Eq.refl (- (zetaZeroMultiplicity (rho : ℂ) : ℂ)))
              (congrArg₂ HMul.hMul hleft hright)
    _ =
        - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          ((zetaSpectralEval f (rho : ℂ) *
            star (zetaSpectralEval f (-star (rho : ℂ))) +
            zetaSpectralEval g (rho : ℂ) *
              star (zetaSpectralEval f (-star (rho : ℂ)))) +
            (zetaSpectralEval f (rho : ℂ) *
              star (zetaSpectralEval g (-star (rho : ℂ))) +
              zetaSpectralEval g (rho : ℂ) *
                star (zetaSpectralEval g (-star (rho : ℂ))))) := by
          exact
            congrArg
              (fun product : ℂ => - (zetaZeroMultiplicity (rho : ℂ) : ℂ) * product)
              hproduct
    _ =
        (- (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          (zetaSpectralEval f (rho : ℂ) *
            star (zetaSpectralEval f (-star (rho : ℂ)))) +
          - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
            (zetaSpectralEval g (rho : ℂ) *
              star (zetaSpectralEval f (-star (rho : ℂ))))) +
          (- (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
            (zetaSpectralEval f (rho : ℂ) *
              star (zetaSpectralEval g (-star (rho : ℂ)))) +
            - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
              (zetaSpectralEval g (rho : ℂ) *
                star (zetaSpectralEval g (-star (rho : ℂ))))) := by
          exact
            Eq.trans
              (mul_add
                (- (zetaZeroMultiplicity (rho : ℂ) : ℂ))
                (zetaSpectralEval f (rho : ℂ) *
                  star (zetaSpectralEval f (-star (rho : ℂ))) +
                  zetaSpectralEval g (rho : ℂ) *
                    star (zetaSpectralEval f (-star (rho : ℂ))))
                (zetaSpectralEval f (rho : ℂ) *
                  star (zetaSpectralEval g (-star (rho : ℂ))) +
                  zetaSpectralEval g (rho : ℂ) *
                    star (zetaSpectralEval g (-star (rho : ℂ)))))
              (congrArg₂ HAdd.hAdd
                (mul_add
                  (- (zetaZeroMultiplicity (rho : ℂ) : ℂ))
                  (zetaSpectralEval f (rho : ℂ) *
                    star (zetaSpectralEval f (-star (rho : ℂ))))
                  (zetaSpectralEval g (rho : ℂ) *
                    star (zetaSpectralEval f (-star (rho : ℂ)))))
                (mul_add
                  (- (zetaZeroMultiplicity (rho : ℂ) : ℂ))
                  (zetaSpectralEval f (rho : ℂ) *
                    star (zetaSpectralEval g (-star (rho : ℂ))))
                  (zetaSpectralEval g (rho : ℂ) *
                    star (zetaSpectralEval g (-star (rho : ℂ))))))

/-- The quadratic completed-zero coordinate is exactly the zero-side contribution
of the corresponding autocorrelation. -/
theorem zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct_local
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (convolutionAutocorrelation f) z =
      zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) := by
  exact zetaSpectralEval_convolutionPair_eq_seed_daggerProduct f f z

theorem zetaCompletedZeroAutocorrelationSideCoordinate_eq
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    zetaCompletedZeroAutocorrelationSideCoordinate f rho =
      zetaZeroSideContribution (rho : ℂ) (convolutionAutocorrelation f) := by
  unfold zetaCompletedZeroAutocorrelationSideCoordinate
  unfold zetaZeroSideContribution
  exact
    congrArg
      (fun spectralValue : ℂ =>
        - (zetaZeroMultiplicity (rho : ℂ) : ℂ) * spectralValue)
      (zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct_local
        f
        (rho : ℂ)).symm

/-- Killing the seed transform at a completed zero kills the corresponding
dagger-paired autocorrelation coordinate. -/
theorem zetaCompletedZeroAutocorrelationSideCoordinate_eq_zero_of_seed_eval_eq_zero
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho})
    (hseed : zetaSpectralEval f (rho : ℂ) = 0) :
    zetaCompletedZeroAutocorrelationSideCoordinate f rho = 0 := by
  unfold zetaCompletedZeroAutocorrelationSideCoordinate
  calc
    - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
        (zetaSpectralEval f (rho : ℂ) *
          star (zetaSpectralEval f (-star (rho : ℂ)))) =
        - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          (0 * star (zetaSpectralEval f (-star (rho : ℂ)))) := by
            exact
              congrArg
                (fun seedValue : ℂ =>
                  - (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
                    (seedValue * star (zetaSpectralEval f (-star (rho : ℂ)))))
                hseed
    _ = - (zetaZeroMultiplicity (rho : ℂ) : ℂ) * 0 := by
          exact
            congrArg
              (fun product : ℂ =>
                - (zetaZeroMultiplicity (rho : ℂ) : ℂ) * product)
              (zero_mul (star (zetaSpectralEval f (-star (rho : ℂ)))) )
    _ = 0 := mul_zero (- (zetaZeroMultiplicity (rho : ℂ) : ℂ))

/-- The norm of the dagger-paired autocorrelation coordinate is the zero
multiplicity times the product of the two seed-transform norms. -/
theorem norm_zetaCompletedZeroAutocorrelationSideCoordinate
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    norm (zetaCompletedZeroAutocorrelationSideCoordinate f rho) =
      (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
        (norm (zetaSpectralEval f (rho : ℂ)) *
          norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
  unfold zetaCompletedZeroAutocorrelationSideCoordinate
  calc
    norm
        (- (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          (zetaSpectralEval f (rho : ℂ) *
            star (zetaSpectralEval f (-star (rho : ℂ))))) =
        norm (- (zetaZeroMultiplicity (rho : ℂ) : ℂ)) *
          norm
            (zetaSpectralEval f (rho : ℂ) *
              star (zetaSpectralEval f (-star (rho : ℂ)))) :=
          norm_mul
            (- (zetaZeroMultiplicity (rho : ℂ) : ℂ))
            (zetaSpectralEval f (rho : ℂ) *
              star (zetaSpectralEval f (-star (rho : ℂ))))
    _ = norm (zetaZeroMultiplicity (rho : ℂ) : ℂ) *
          norm
            (zetaSpectralEval f (rho : ℂ) *
              star (zetaSpectralEval f (-star (rho : ℂ)))) := by
          exact
            congrArg
              (fun coefficient : ℝ =>
                coefficient *
                  norm
                    (zetaSpectralEval f (rho : ℂ) *
                      star (zetaSpectralEval f (-star (rho : ℂ)))))
              (norm_neg (zetaZeroMultiplicity (rho : ℂ) : ℂ))
    _ = (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (norm (zetaSpectralEval f (rho : ℂ)) *
            norm (star (zetaSpectralEval f (-star (rho : ℂ)))) ) := by
          exact
            congrArg₂ HMul.hMul
              (Complex.norm_natCast (zetaZeroMultiplicity (rho : ℂ)))
              (norm_mul
                (zetaSpectralEval f (rho : ℂ))
                (star (zetaSpectralEval f (-star (rho : ℂ)))))
    _ = (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (norm (zetaSpectralEval f (rho : ℂ)) *
            norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
          exact
            congrArg
              (fun secondNorm : ℝ =>
                (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
                  (norm (zetaSpectralEval f (rho : ℂ)) * secondNorm))
              (norm_star (zetaSpectralEval f (-star (rho : ℂ))))

/-- The dagger-paired autocorrelation coordinate is bounded by the weighted
sum of the two seed-transform squares. -/
theorem two_mul_norm_zetaCompletedZeroAutocorrelationSideCoordinate_le
    (f : ZetaAdmissibleFunction)
    (rho : {rho : ℂ // ZetaCompletedZero rho}) :
    2 * norm (zetaCompletedZeroAutocorrelationSideCoordinate f rho) ≤
      (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
        (norm (zetaSpectralEval f (rho : ℂ)) ^ 2 +
          norm (zetaSpectralEval f (-star (rho : ℂ))) ^ 2) := by
  have hweightNonnegative : 0 ≤ (zetaZeroMultiplicity (rho : ℂ) : ℝ) :=
    Nat.cast_nonneg (zetaZeroMultiplicity (rho : ℂ))
  have hmeanSquare :
      2 * norm (zetaSpectralEval f (rho : ℂ)) *
          norm (zetaSpectralEval f (-star (rho : ℂ))) ≤
        norm (zetaSpectralEval f (rho : ℂ)) ^ 2 +
          norm (zetaSpectralEval f (-star (rho : ℂ))) ^ 2 :=
    two_mul_le_add_sq
      (norm (zetaSpectralEval f (rho : ℂ)))
      (norm (zetaSpectralEval f (-star (rho : ℂ))))
  have hweightedMeanSquare :
      (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (2 * norm (zetaSpectralEval f (rho : ℂ)) *
            norm (zetaSpectralEval f (-star (rho : ℂ)))) ≤
        (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (norm (zetaSpectralEval f (rho : ℂ)) ^ 2 +
            norm (zetaSpectralEval f (-star (rho : ℂ))) ^ 2) :=
    mul_le_mul_of_nonneg_left hmeanSquare hweightNonnegative
  calc
    2 * norm (zetaCompletedZeroAutocorrelationSideCoordinate f rho) =
        2 *
          ((zetaZeroMultiplicity (rho : ℂ) : ℝ) *
            (norm (zetaSpectralEval f (rho : ℂ)) *
              norm (zetaSpectralEval f (-star (rho : ℂ))))) := by
          exact
            congrArg
              (fun coordinateNorm : ℝ => 2 * coordinateNorm)
              (norm_zetaCompletedZeroAutocorrelationSideCoordinate f rho)
    _ = (2 * (zetaZeroMultiplicity (rho : ℂ) : ℝ)) *
          (norm (zetaSpectralEval f (rho : ℂ)) *
            norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
          exact
            (mul_assoc
              2
              (zetaZeroMultiplicity (rho : ℂ) : ℝ)
              (norm (zetaSpectralEval f (rho : ℂ)) *
                norm (zetaSpectralEval f (-star (rho : ℂ))))).symm
    _ = ((zetaZeroMultiplicity (rho : ℂ) : ℝ) * 2) *
          (norm (zetaSpectralEval f (rho : ℂ)) *
            norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
          exact
            congrArg
              (fun coefficient : ℝ =>
                coefficient *
                  (norm (zetaSpectralEval f (rho : ℂ)) *
                    norm (zetaSpectralEval f (-star (rho : ℂ)))))
              (mul_comm 2 (zetaZeroMultiplicity (rho : ℂ) : ℝ))
    _ = (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (2 *
            (norm (zetaSpectralEval f (rho : ℂ)) *
              norm (zetaSpectralEval f (-star (rho : ℂ))))) := by
          exact
            mul_assoc
              (zetaZeroMultiplicity (rho : ℂ) : ℝ)
              2
              (norm (zetaSpectralEval f (rho : ℂ)) *
                norm (zetaSpectralEval f (-star (rho : ℂ))))
    _ = (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (2 * norm (zetaSpectralEval f (rho : ℂ)) *
            norm (zetaSpectralEval f (-star (rho : ℂ)))) := by
          exact
            congrArg
              (fun product : ℝ =>
                (zetaZeroMultiplicity (rho : ℂ) : ℝ) * product)
              (mul_assoc
                2
                (norm (zetaSpectralEval f (rho : ℂ)))
                (norm (zetaSpectralEval f (-star (rho : ℂ))))).symm
    _ ≤ (zetaZeroMultiplicity (rho : ℂ) : ℝ) *
          (norm (zetaSpectralEval f (rho : ℂ)) ^ 2 +
            norm (zetaSpectralEval f (-star (rho : ℂ))) ^ 2) :=
          hweightedMeanSquare

/-- The multiplicity-weighted completed-zero coordinate map. -/
def zetaCompletedZeroSideCoordinateLinearMap :
    ZetaAdmissibleFunction →ₗ[ℂ] ({ρ : ℂ // ZetaCompletedZero ρ} → ℂ) where
  toFun := fun f ρ => zetaZeroSideContribution (ρ : ℂ) f
  map_add' := fun f g =>
    funext (fun ρ => zetaZeroSideContribution_add (ρ : ℂ) f g)
  map_smul' := fun c f =>
    funext (fun ρ => zetaZeroSideContribution_smul (ρ : ℂ) c f)

/-- The weighted coordinate map is evaluation of the zero-side contribution. -/
theorem zetaCompletedZeroSideCoordinateLinearMap_apply
    (f : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaCompletedZeroSideCoordinateLinearMap f ρ =
      zetaZeroSideContribution (ρ : ℂ) f := by
  rfl

/-- The extended weighted `ℓ¹` mass of the completed-zero side coordinates. -/
def zetaCompletedZeroSideWeightedTailMass
    (weight : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ≥0∞)
    (f : ZetaAdmissibleFunction) : ℝ≥0∞ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    weight ρ * ‖zetaCompletedZeroSideCoordinateLinearMap f ρ‖₊

/-- The linear probes having finite mass for a prescribed completed-zero weight. -/
def ZetaCompletedZeroSideWeightedTailFinite
    (weight : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ≥0∞) :
    Set ZetaAdmissibleFunction :=
  fun f => zetaCompletedZeroSideWeightedTailMass weight f ≠ ⊤

/-- The multiplicity-weighted seed energy controlling dagger-paired
autocorrelation coordinates.  Each completed-zero coordinate records both
members of its `-star` pair, so no second centered-coordinate translation is
introduced. -/
def zetaCompletedZeroSeedSquareTailMass
    (weight : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ≥0∞)
    (f : ZetaAdmissibleFunction) : ℝ≥0∞ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    weight ρ * (zetaZeroMultiplicity (ρ : ℂ) : ℝ≥0∞) *
      (‖zetaSpectralEval f (ρ : ℂ)‖₊ ^ 2 +
        ‖zetaSpectralEval f (-star (ρ : ℂ))‖₊ ^ 2)

/-- The probes of finite weighted seed energy.  This is the quadratic carrier
used to transfer finite-window approximation through autocorrelation
positivity. -/
def ZetaCompletedZeroSeedSquareTailFinite
    (weight : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ≥0∞) :
    Set ZetaAdmissibleFunction :=
  fun f => zetaCompletedZeroSeedSquareTailMass weight f ≠ ⊤

/-- The mass summand is the weighted norm of the corresponding zero-side contribution. -/
theorem zetaCompletedZeroSideWeightedTailMass_summand
    (weight : {ρ : ℂ // ZetaCompletedZero ρ} → ℝ≥0∞)
    (f : ZetaAdmissibleFunction)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    weight ρ * ‖zetaCompletedZeroSideCoordinateLinearMap f ρ‖₊ =
      weight ρ * ‖zetaZeroSideContribution (ρ : ℂ) f‖₊ := by
  exact congrArg (fun w : NNReal => weight ρ * (w : ENNReal))
    (congrArg (fun z : ℂ => ‖z‖₊)
      (zetaCompletedZeroSideCoordinateLinearMap_apply f ρ))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
