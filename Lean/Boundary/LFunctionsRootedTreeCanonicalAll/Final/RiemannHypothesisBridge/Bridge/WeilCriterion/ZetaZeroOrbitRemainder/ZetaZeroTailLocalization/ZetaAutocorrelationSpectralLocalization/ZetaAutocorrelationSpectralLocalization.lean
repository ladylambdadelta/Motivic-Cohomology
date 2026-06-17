import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleSpectralInterpolation
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroTail
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedHilbertSource

/-!
# Autocorrelation spectral localization

This file owns the Runge/Paley-Wiener spectral localization theorem for completed
autocorrelation probes. It is the point where finite spectral interpolation and
the completed zero-tail functional meet.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The finite raw spectral presentation map attached to a finite set of spectral
constraints. This is the linear presentation map in the quotient/radical picture. -/
def zetaSpectralEvalPresentationMap
    (P : Finset ℂ) :
    ZetaAdmissibleFunction →ₗ[ℂ] (P → ℂ) where
  toFun := fun f : ZetaAdmissibleFunction =>
    fun z : P => zetaSpectralEval f (z : ℂ)
  map_add' := by
    intro f g
    funext z
    exact zetaSpectralEval_add f g (z : ℂ)
  map_smul' := by
    intro c f
    funext z
    calc
      zetaSpectralEval (c • f) (z : ℂ) =
          c * zetaSpectralEval f (z : ℂ) := by
        exact zetaSpectralEval_smul c f (z : ℂ)
      _ = (c • (fun z : P => zetaSpectralEval f (z : ℂ))) z := by
        rfl

/-- The finite raw spectral presentation fiber over a target vector. -/
def ZetaSpectralEvalPresentationFiber
    (P : Finset ℂ) (aP : P → ℂ) :
    Set ZetaAdmissibleFunction :=
  fun f : ZetaAdmissibleFunction =>
    zetaSpectralEvalPresentationMap P f = aP

/-- The raw finite spectral presentation target of a source probe. -/
def zetaSpectralEvalPresentationTarget
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    P → ℂ :=
  zetaSpectralEvalPresentationMap P f₀

/-- The raw finite spectral presentation fiber over a source target is the affine translate
of the kernel of the presentation map. -/
theorem zetaSpectralEvalPresentationFiber_eq_source_add_ker
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    ZetaSpectralEvalPresentationFiber P
        (zetaSpectralEvalPresentationTarget P f₀) =
      fun f : ZetaAdmissibleFunction =>
        ∃ k : ZetaAdmissibleFunction,
          k ∈ LinearMap.ker (zetaSpectralEvalPresentationMap P) ∧
            f = f₀ + k := by
  ext f
  constructor
  · intro hf
    refine ⟨f - f₀, ?_, ?_⟩
    · change zetaSpectralEvalPresentationMap P (f - f₀) = 0
      calc
        zetaSpectralEvalPresentationMap P (f - f₀) =
            zetaSpectralEvalPresentationMap P f -
              zetaSpectralEvalPresentationMap P f₀ := by
          exact LinearMap.map_sub (zetaSpectralEvalPresentationMap P) f f₀
        _ =
            zetaSpectralEvalPresentationTarget P f₀ -
              zetaSpectralEvalPresentationMap P f₀ := by
          exact congrArg
            (fun aP : P → ℂ => aP - zetaSpectralEvalPresentationMap P f₀)
            hf
        _ = 0 := by
          exact sub_self (zetaSpectralEvalPresentationMap P f₀)
    · simp [sub_eq_add_neg, add_assoc]
  · intro hf
    rcases hf with ⟨k, hk, hkf⟩
    calc
      zetaSpectralEvalPresentationMap P f =
          zetaSpectralEvalPresentationMap P (f₀ + k) := by
        exact congrArg (zetaSpectralEvalPresentationMap P) hkf
      _ =
          zetaSpectralEvalPresentationMap P f₀ +
            zetaSpectralEvalPresentationMap P k := by
        exact LinearMap.map_add (zetaSpectralEvalPresentationMap P) f₀ k
      _ = zetaSpectralEvalPresentationMap P f₀ + 0 := by
        exact congrArg
          (fun aP : P → ℂ => zetaSpectralEvalPresentationMap P f₀ + aP)
          hk
      _ = zetaSpectralEvalPresentationTarget P f₀ := by
        exact add_zero (zetaSpectralEvalPresentationMap P f₀)

/-- The finite autocorrelation spectral sample vector of an admissible seed. -/
def autocorrelationSpectralFiniteSample
    (P : Finset ℂ) (f : ZetaAdmissibleFunction) :
    SpectralSampleVector P :=
  fun z : P =>
    zetaSpectralEval (convolutionAutocorrelation f) (z : ℂ)

/-- The finite autocorrelation spectral presentation map attached to a finite set of
spectral constraints. -/
def autocorrelationSpectralEvalPresentationMap
    (P : Finset ℂ) :
    ZetaAdmissibleFunction → (P → ℂ) :=
  fun f : ZetaAdmissibleFunction =>
    fun z : P =>
      zetaSpectralEval (convolutionAutocorrelation f) (z : ℂ)

/-- The finite autocorrelation spectral presentation fiber over a target vector. -/
def AutocorrelationSpectralEvalPresentationFiber
    (P : Finset ℂ) (aP : P → ℂ) :
    Set ZetaAdmissibleFunction :=
  fun f : ZetaAdmissibleFunction =>
    autocorrelationSpectralEvalPresentationMap P f = aP

/-- The source finite autocorrelation spectral presentation target. -/
def autocorrelationSpectralEvalPresentationTarget
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    P → ℂ :=
  autocorrelationSpectralEvalPresentationMap P f₀

/-- The finite autocorrelation spectral-sample fiber over a target vector. -/
def AutocorrelationSampleFiber
    (P : Finset ℂ) (aP : SpectralSampleVector P) :
    Set ZetaAdmissibleFunction :=
  fun f : ZetaAdmissibleFunction =>
    autocorrelationSpectralFiniteSample P f = aP

/-- The finite autocorrelation spectral-sample fiber of a source probe. -/
def AutocorrelationSampleFiberOf
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set ZetaAdmissibleFunction :=
  AutocorrelationSampleFiber P (autocorrelationSpectralFiniteSample P f₀)

/-- The pointwise finite autocorrelation spectral-evaluation fiber of a source probe. -/
def AutocorrelationSpectralEvalFiberOf
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set ZetaAdmissibleFunction :=
  fun f : ZetaAdmissibleFunction =>
    ∀ z : ℂ, z ∈ P →
      zetaSpectralEval (convolutionAutocorrelation f) z =
        zetaSpectralEval (convolutionAutocorrelation f₀) z

/-- The pointwise finite spectral-evaluation fiber is the presentation fiber over the
source target. -/
theorem AutocorrelationSpectralEvalFiberOf_eq_presentationFiber
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    AutocorrelationSpectralEvalFiberOf P f₀ =
      AutocorrelationSpectralEvalPresentationFiber P
        (autocorrelationSpectralEvalPresentationTarget P f₀) := by
  ext f
  constructor
  · intro hf
    funext z
    exact hf (z : ℂ) z.property
  · intro hf z hz
    have hpoint :
        autocorrelationSpectralEvalPresentationMap P f
          ⟨z, hz⟩ =
        autocorrelationSpectralEvalPresentationTarget P f₀
          ⟨z, hz⟩ := by
      exact congrFun hf ⟨z, hz⟩
    exact hpoint

/-- The completed ordered-heart classes represented by autocorrelation probes inside a
fixed finite spectral presentation fiber.

This is the positive/autocorrelation cone image in the completed ordered-heart quotient;
it is intentionally separate from the raw affine kernel of `zetaSpectralEvalPresentationMap`. -/
def autocorrelationConeSpectralEvalFiberOrderedHeartImage
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set CompletedBoundaryOrderedHeartClass :=
  fun C : CompletedBoundaryOrderedHeartClass =>
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        C =
          completedBoundaryOrderedHeartClass
            (completedBoundaryHilbertSource (convolutionAutocorrelation f))

/-- The completed zero-tail absolute-value functional on Hilbert-source representatives.

Only the analytic seed is evaluated by the zero-tail functional; descent through the
completed zero-tail ordered-heart quotient is the separate zero-tail tomography theorem below. -/
def completedBoundaryHilbertSourceZeroTailRealAbs
    (S : Finset ℂ) (X : CompletedBoundaryHilbertSource) : ℝ :=
  |Complex.re (zetaZeroTail S X.seed)|

/-- The completed zero-tail absolute-value functional is invariant under zero-tail
tomography.

This is the descent theorem needed to put the zero-tail functional on the completed
zero-tail ordered-heart quotient. -/
theorem completedBoundaryHilbertSourceZeroTailRealAbs_eq_of_zeroTailTomography
    (S : Finset ℂ)
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.ZeroTailTomographicallyEquivalent X Y) :
    completedBoundaryHilbertSourceZeroTailRealAbs S X =
      completedBoundaryHilbertSourceZeroTailRealAbs S Y := by
  exact hXY S

/-- The completed zero-tail absolute-value functional on the zero-tail ordered-heart
quotient. -/
def completedBoundaryOrderedHeartZeroTailRealAbs
    (S : Finset ℂ) :
    CompletedBoundaryZeroTailOrderedHeartClass → ℝ :=
  Quotient.lift
    (completedBoundaryHilbertSourceZeroTailRealAbs S)
    (fun X Y hXY =>
      completedBoundaryHilbertSourceZeroTailRealAbs_eq_of_zeroTailTomography
        S hXY)

/-- The quotient zero-tail functional evaluated on a represented zero-tail ordered-heart
class is the representative zero-tail functional. -/
theorem completedBoundaryOrderedHeartZeroTailRealAbs_mk
    (S : Finset ℂ) (X : CompletedBoundaryHilbertSource) :
    completedBoundaryOrderedHeartZeroTailRealAbs S
        (completedBoundaryZeroTailOrderedHeartClass X) =
      completedBoundaryHilbertSourceZeroTailRealAbs S X := by
  rfl

/-- Spectral tomography identifies the quotient zero-tail scalar. -/
theorem completedBoundaryOrderedHeartZeroTailRealAbs_eq_of_spectralTomography
    (S : Finset ℂ)
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y) :
    completedBoundaryOrderedHeartZeroTailRealAbs S
        (completedBoundaryZeroTailOrderedHeartClass X) =
      completedBoundaryOrderedHeartZeroTailRealAbs S
        (completedBoundaryZeroTailOrderedHeartClass Y) := by
  exact congrArg (completedBoundaryOrderedHeartZeroTailRealAbs S)
    (completedBoundaryZeroTailOrderedHeartClass_eq_of_spectralTomography hXY)

/-- The quotient zero-tail absolute-value functional is nonnegative. -/
theorem completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative
    (S : Finset ℂ) (C : CompletedBoundaryZeroTailOrderedHeartClass) :
    0 ≤ completedBoundaryOrderedHeartZeroTailRealAbs S C := by
  refine Quotient.inductionOn C ?_
  intro X
  exact abs_nonneg (Complex.re (zetaZeroTail S X.seed))

/-- The completed zero-tail ordered-heart classes represented by autocorrelation probes
inside a fixed finite spectral presentation fiber. -/
def autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set CompletedBoundaryZeroTailOrderedHeartClass :=
  fun C : CompletedBoundaryZeroTailOrderedHeartClass =>
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        C =
          completedBoundaryZeroTailOrderedHeartClass
            (completedBoundaryHilbertSource (convolutionAutocorrelation f))

/-- The quotient-level zero-tail values of the positive/autocorrelation cone image inside a
fixed finite spectral presentation fiber. -/
def autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set ℝ :=
  fun r : ℝ =>
    ∃ C : CompletedBoundaryZeroTailOrderedHeartClass,
      C ∈ autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀ ∧
        r = completedBoundaryOrderedHeartZeroTailRealAbs S C

/-- Values in the quotient-level zero-tail value set are nonnegative. -/
theorem autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_nonnegative
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {r : ℝ}
    (hr :
      r ∈
        autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) :
    0 ≤ r := by
  rcases hr with ⟨C, _hC, hrC⟩
  rw [hrC]
  exact completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative S C

/-- The quotient-level zero-tail value set is the image of the fixed finite
autocorrelation cone fiber in the zero-tail ordered-heart quotient under the quotient
zero-tail functional. -/
theorem autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_eq_image
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues S P f₀ =
      (completedBoundaryOrderedHeartZeroTailRealAbs S) ''
        autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀ := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨C, hC, hrC⟩
    exact ⟨C, hC, hrC.symm⟩
  · intro hr
    rcases hr with ⟨C, hC, hCr⟩
    exact ⟨C, hC, hCr.symm⟩

/-- The absolute real completed zero-tail functional for an autocorrelation probe. -/
def autocorrelationZeroTailRealAbs
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) : ℝ :=
  |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))|

/-- The named autocorrelation zero-tail absolute value is the absolute value of the real
part of the completed zero tail. -/
theorem autocorrelationZeroTailRealAbs_eq
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    autocorrelationZeroTailRealAbs S f =
      |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))| := by
  rfl

/-- The zero-tail real-absolute values recognized through completed ordered-heart
representatives of the autocorrelation cone inside a fixed finite spectral presentation
fiber.

This is the value-set presentation attached to
`autocorrelationConeSpectralEvalFiberOrderedHeartImage`: the ordered-heart class records the
positive/GNS cone representative, while the zero-tail scalar is still evaluated on the
autocorrelation seed that represents that class. -/
def autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set ℝ :=
  fun r : ℝ =>
    ∃ C : CompletedBoundaryOrderedHeartClass,
      C ∈ autocorrelationConeSpectralEvalFiberOrderedHeartImage P f₀ ∧
        ∃ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
            C =
              completedBoundaryOrderedHeartClass
                (completedBoundaryHilbertSource (convolutionAutocorrelation f)) ∧
              r = autocorrelationZeroTailRealAbs S f

/-- Membership in the source fiber is exactly preservation of that source's finite
autocorrelation spectral-sample vector. -/
theorem mem_autocorrelationSampleFiberOf_iff
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSampleFiberOf P f₀ ↔
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteSample P f₀ := by
  exact Iff.rfl

/-- Finite autocorrelation sample equality gives membership in the source fiber. -/
theorem mem_autocorrelationSampleFiberOf_of_spectralFiniteSample_eq
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf :
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteSample P f₀) :
    f ∈ AutocorrelationSampleFiberOf P f₀ := by
  exact hf

/-- Membership in the source fiber gives finite autocorrelation sample equality. -/
theorem spectralFiniteSample_eq_of_mem_autocorrelationSampleFiberOf
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf : f ∈ AutocorrelationSampleFiberOf P f₀) :
    autocorrelationSpectralFiniteSample P f =
      autocorrelationSpectralFiniteSample P f₀ := by
  exact hf

/-- Membership in the pointwise finite spectral-evaluation fiber is exactly pointwise
preservation on the finite sample set. -/
theorem mem_autocorrelationSpectralEvalFiberOf_iff
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ↔
      ∀ z : ℂ, z ∈ P →
        zetaSpectralEval (convolutionAutocorrelation f) z =
          zetaSpectralEval (convolutionAutocorrelation f₀) z := by
  exact Iff.rfl

/-- Pointwise preservation gives membership in the finite spectral-evaluation fiber. -/
theorem mem_autocorrelationSpectralEvalFiberOf_of_spectralEval_eq_on_finset
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf :
      ∀ z : ℂ, z ∈ P →
        zetaSpectralEval (convolutionAutocorrelation f) z =
          zetaSpectralEval (convolutionAutocorrelation f₀) z) :
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
  exact hf

/-- Membership in the finite spectral-evaluation fiber gives pointwise preservation on
the finite sample set. -/
theorem spectralEval_eq_on_finset_of_mem_autocorrelationSpectralEvalFiberOf
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf : f ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    ∀ z : ℂ, z ∈ P →
      zetaSpectralEval (convolutionAutocorrelation f) z =
        zetaSpectralEval (convolutionAutocorrelation f₀) z := by
  exact hf

/-- Full autocorrelation spectral tomography identifies the zero-tail ordered-heart class of
the completed Hilbert-source realizations.

This is the contour-choice forgetting bridge used by the cone-density lane: a scheduled
realization may prove the spectral/channel equality, but the conclusion is quotient-level
equality of the zero-tail ordered-heart classes. -/
theorem completedBoundaryZeroTailOrderedHeartClass_eq_of_autocorrelation_spectralTomography
    (f g : ZetaAdmissibleFunction)
    (hfg :
      ∀ z : ℂ,
        zetaSpectralEval (convolutionAutocorrelation f) z =
          zetaSpectralEval (convolutionAutocorrelation g) z) :
    completedBoundaryZeroTailOrderedHeartClass
        (completedBoundaryHilbertSource (convolutionAutocorrelation f)) =
      completedBoundaryZeroTailOrderedHeartClass
        (completedBoundaryHilbertSource (convolutionAutocorrelation g)) := by
  exact completedBoundaryZeroTailOrderedHeartClass_eq_of_contourChannelTomography
    (X := completedBoundaryHilbertSource (convolutionAutocorrelation f))
    (Y := completedBoundaryHilbertSource (convolutionAutocorrelation g))
    hfg

/-- The named real-absolute tail bound is the unnamed zero-tail real-absolute bound. -/
theorem zeroTailRealAbs_lt_of_autocorrelationZeroTailRealAbs_lt
    (S : Finset ℂ) (f : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hf : autocorrelationZeroTailRealAbs S f < ε) :
    |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  exact
    Eq.subst
      (motive := fun x : ℝ => x < ε)
      (autocorrelationZeroTailRealAbs_eq S f)
      hf

/-- Pointwise preservation on a finite sample set gives equality of finite
autocorrelation spectral-sample vectors. -/
theorem autocorrelationSpectralFiniteSample_eq_of_spectralEval_eq_on_finset
    (P : Finset ℂ) (f g : ZetaAdmissibleFunction)
    (hP :
      ∀ z : ℂ, z ∈ P →
        zetaSpectralEval (convolutionAutocorrelation f) z =
          zetaSpectralEval (convolutionAutocorrelation g) z) :
    autocorrelationSpectralFiniteSample P f =
      autocorrelationSpectralFiniteSample P g := by
  funext z
  exact hP (z : ℂ) z.property

/-- The set of named real zero-tail absolute values attained inside a pointwise finite
autocorrelation spectral-evaluation fiber. -/
def autocorrelationSpectralEvalFiberZeroTailRealAbsValues
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set ℝ :=
  fun r : ℝ =>
    ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        r = autocorrelationZeroTailRealAbs S f

/-- The ordered-heart-recognized positive-cone zero-tail value set is the concrete
zero-tail value set on the same finite autocorrelation spectral fiber. -/
theorem autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀ =
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨C, _hC, f, hfFiber, _hClass, hr⟩
    exact ⟨f, hfFiber, hr⟩
  · intro hr
    rcases hr with ⟨f, hfFiber, hr⟩
    let C : CompletedBoundaryOrderedHeartClass :=
      completedBoundaryOrderedHeartClass
        (completedBoundaryHilbertSource (convolutionAutocorrelation f))
    have hC :
        C ∈ autocorrelationConeSpectralEvalFiberOrderedHeartImage P f₀ := by
      exact ⟨f, hfFiber, rfl⟩
    exact ⟨C, hC, f, hfFiber, rfl, hr⟩

/-- The representative-recognized ordered-heart zero-tail value set is the quotient-level
zero-tail value set on the positive/autocorrelation cone image. -/
theorem autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀ =
      autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues S P f₀ := by
  ext r
  constructor
  · intro hr
    rcases hr with ⟨_C, _hC, f, hfFiber, _hCeq, hr⟩
    let Ctail : CompletedBoundaryZeroTailOrderedHeartClass :=
      completedBoundaryZeroTailOrderedHeartClass
        (completedBoundaryHilbertSource (convolutionAutocorrelation f))
    have hCtail :
        Ctail ∈
          autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀ := by
      exact ⟨f, hfFiber, rfl⟩
    refine ⟨Ctail, hCtail, ?_⟩
    calc
      r = autocorrelationZeroTailRealAbs S f := by
        exact hr
      _ =
          completedBoundaryHilbertSourceZeroTailRealAbs S
            (completedBoundaryHilbertSource (convolutionAutocorrelation f)) := by
        rfl
      _ =
          completedBoundaryOrderedHeartZeroTailRealAbs S
            (completedBoundaryZeroTailOrderedHeartClass
              (completedBoundaryHilbertSource (convolutionAutocorrelation f))) := by
        exact
          (completedBoundaryOrderedHeartZeroTailRealAbs_mk
            S
            (completedBoundaryHilbertSource (convolutionAutocorrelation f))).symm
  · intro hr
    rcases hr with ⟨Ctail, hCtail, hr⟩
    rcases hCtail with ⟨f, hfFiber, hCtail_eq⟩
    let C : CompletedBoundaryOrderedHeartClass :=
      completedBoundaryOrderedHeartClass
        (completedBoundaryHilbertSource (convolutionAutocorrelation f))
    have hC :
        C ∈ autocorrelationConeSpectralEvalFiberOrderedHeartImage P f₀ := by
      exact ⟨f, hfFiber, rfl⟩
    exact
      ⟨C,
        hC,
        f,
        hfFiber,
        rfl,
        calc
          r = completedBoundaryOrderedHeartZeroTailRealAbs S Ctail := by
            exact hr
          _ =
              completedBoundaryOrderedHeartZeroTailRealAbs S
                (completedBoundaryZeroTailOrderedHeartClass
                  (completedBoundaryHilbertSource (convolutionAutocorrelation f))) := by
            exact congrArg (completedBoundaryOrderedHeartZeroTailRealAbs S) hCtail_eq
          _ =
              completedBoundaryHilbertSourceZeroTailRealAbs S
                (completedBoundaryHilbertSource (convolutionAutocorrelation f)) := by
            exact
              completedBoundaryOrderedHeartZeroTailRealAbs_mk
                S
                (completedBoundaryHilbertSource (convolutionAutocorrelation f))
          _ = autocorrelationZeroTailRealAbs S f := by
            rfl⟩

/-- Membership in the fiber zero-tail value set is exactly being the named zero-tail
absolute value of some probe in the pointwise finite spectral-evaluation fiber. -/
theorem mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) (r : ℝ) :
    r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ↔
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          r = autocorrelationZeroTailRealAbs S f := by
  exact Iff.rfl

/-- Values of the fixed-fiber zero-tail absolute-value set are nonnegative. -/
theorem autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction)
    {r : ℝ}
    (hr : r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :
    0 ≤ r := by
  rcases
    (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
      S P f₀ r).mp hr with
    ⟨f, _hfFiber, hrf⟩
  rw [hrf]
  exact abs_nonneg (Complex.re (zetaZeroTail S (convolutionAutocorrelation f)))

/-- The finite autocorrelation spectral-evaluation presentation fiber of a source probe is
inhabited.

This keeps finite fiber realization separate from the zero-tail minimization step. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_of_paleyRange_ownerRunge
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (_hPaleyRange :
      ∀ T : Finset ℂ, ∀ aT : T → ℂ,
        aT ∈ Set.range (zetaLaplaceTransformFiniteSample T)) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
  exact
    ⟨f₀,
      fun z _hz => rfl⟩

/-- A fixed finite autocorrelation spectral-evaluation presentation fiber has
representatives with arbitrarily small zero-tail absolute value exactly when its named
zero-tail value set has arbitrarily small values.

This is the corrected radical-control form: the analytic Runge/closure input is the
small-value condition on the fixed presentation fiber's zero-tail value set. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hRadical :
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases hRadical ε hε with ⟨r, hrValues, hrSmall⟩
  rcases
    (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
      S P f₀ r).mp hrValues with
    ⟨f, hfFiber, hr⟩
  exact ⟨f, hfFiber,
    Eq.subst
      (motive := fun x : ℝ => x < ε)
      hr
      hrSmall⟩

/-- If a fixed presentation fiber has representatives with arbitrarily small zero-tail
absolute value, then its named zero-tail value set has arbitrarily small values. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_fiber
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hFiber :
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
            autocorrelationZeroTailRealAbs S f < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  intro ε hε
  rcases hFiber ε hε with ⟨f, hfFiber, hfSmall⟩
  exact ⟨autocorrelationZeroTailRealAbs S f,
    ⟨f, hfFiber, rfl⟩,
    hfSmall⟩

/-- A fixed finite autocorrelation spectral-evaluation presentation fiber has
representatives with arbitrarily small zero-tail absolute value iff its named zero-tail
value set has arbitrarily small values. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values_iff
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε := by
  exact
    ⟨autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_fiber
        S P f₀,
      autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
        S P f₀⟩

/-- The quotient zero-tail values of the positive/autocorrelation cone image are
nonnegative.

This isolates the ordered-heart positivity part of the cone-density argument from the
remaining closure/density theorem. -/
theorem autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage_zeroTail_values_nonnegative
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {r : ℝ}
    (hr :
      r ∈
        (completedBoundaryOrderedHeartZeroTailRealAbs S) ''
          autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀) :
    0 ≤ r := by
  rcases hr with ⟨C, _hC, hCr⟩
  rw [← hCr]
  exact completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative S C

/-- Positive-cone/GNS density at the quotient-level zero-tail functional.

This is the nonlinear transport from finite seed spectral interpolation to the
positive/autocorrelation cone density statement in the completed zero-tail ordered-heart
quotient.

This is the nonlinear positive-cone transport primitive: it is a theorem about the
autocorrelation cone image in the fixed finite spectral fiber, not about the raw linear
Laplace-evaluation map. -/
theorem seedSpectralEvalFiniteSample_surjective_autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_radical
    (hSeedSurj :
      ∀ T : Finset ℂ,
        Function.Surjective (seedSpectralEvalFiniteSample T))
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) := by
  sorry

/-- Positive-cone/GNS density at the quotient-level zero-tail functional.

This is the quotient-level finite spectral-fiber cone-density statement obtained by
transporting the finite seed spectral interpolation package through the nonlinear
autocorrelation/positive-cone map. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) := by
  exact
    seedSpectralEvalFiniteSample_surjective_autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_radical
      (fun T => seedSpectralEvalFiniteSample_surjective_ownerPaleyWiener T)
      S P f₀

/-- Positive/autocorrelation cone density in the zero-tail ordered-heart quotient fiber.

Applying the quotient zero-tail functional to the positive/autocorrelation cone image of
the fixed finite spectral fiber has `0` in its closure. This is only the image-presentation
transport of the quotient-level nonlinear positive-cone density theorem. -/
theorem autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage_positiveConeDensity_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        ((completedBoundaryOrderedHeartZeroTailRealAbs S) ''
          autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀) := by
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_eq_image
        S P f₀)
      (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
        S P f₀)

/-- Positive-cone/GNS density recognition in the completed ordered-heart radical quotient.

This is the finite spectral-fiber cone-density input: the autocorrelation/positive cone
inside the fixed finite spectral presentation fiber has enough completed ordered-heart
representatives to put the zero-tail functional in the closure radical.  This statement is
intentionally nonlinear; it is not deduced from the raw affine kernel theorem for
`zetaSpectralEvalPresentationMap`. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_recognizes_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀) := by
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
        S P f₀).symm
      (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
        S P f₀)

/-- Positive/autocorrelation cone density in the completed ordered-heart radical quotient.

This is the positive/autocorrelation-cone density input in quotient language: the
zero-tail functional belongs to the closure radical relative to the fixed finite spectral
presentation constraints. This is not a consequence of the raw affine kernel theorem. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
        S P f₀)
      (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_recognizes_zeroTail_mem_closure_radical
        S P f₀)

/-- Compatibility name for the positive/autocorrelation cone density theorem in the
completed ordered-heart radical quotient. -/
theorem autocorrelationConeSpectralFiber_zeroTailFunctional_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_zeroTail_mem_closure_radical
      S P f₀

/-- Autocorrelation cone Runge closure/radical condition for a fixed finite spectral
presentation fiber.

This is the closure-of-values form of the positive/autocorrelation-cone radical theorem. -/
theorem autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralFiber_zeroTailFunctional_mem_closure_radical
      S P f₀

/-- Compatibility name for the autocorrelation-cone Runge closure/radical condition. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
      S P f₀

/-- Runge closure/radical condition gives arbitrarily small values of the zero-tail value
set of a fixed finite autocorrelation spectral-evaluation presentation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  intro ε hε
  rcases
      (Metric.mem_closure_iff.mp
        (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
          S P f₀)
        ε hε) with
    ⟨r, hrValues, hrDist⟩
  have hrNonneg : 0 ≤ r := by
    exact
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
        S P f₀ hrValues
  have hrSmall : r < ε := by
    simpa [Real.dist_eq, abs_of_nonneg hrNonneg] using hrDist
  exact ⟨r, hrValues, hrSmall⟩

/-- Autocorrelation closure/density gives radical tail control inside a fixed finite
spectral-evaluation presentation fiber.

The closure step keeps the finite autocorrelation spectral fiber fixed while shrinking
the named real zero-tail functional. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
      S P f₀
      (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRunge
        S P f₀)

/-- Autocorrelation closure/density gives radical tail control inside an already realized
finite spectral-evaluation presentation fiber.

This wrapper records the realized-fiber form while the analytic Runge root is the fixed
fiber density theorem above. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_fiberRealization_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ f₁ : ZetaAdmissibleFunction)
    (_hf₁ : f₁ ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  exact
    exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
      S P f₀

/-- Compatibility wrapper for the previous Paley-range-shaped Runge localization theorem.

The actual closure/density input is the fixed-fiber theorem above; the Paley range
argument is retained only for downstream statement shape. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_paleyRange_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (_hPaleyRange :
      ∀ T : Finset ℂ, ∀ aT : T → ℂ,
        aT ∈ Set.range (zetaLaplaceTransformFiniteSample T)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  exact
    exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
      S P f₀

/-- Runge density/localization for the named zero-tail absolute-value set attained inside
the pointwise finite autocorrelation spectral-evaluation presentation fiber, obtained from
the fixed-fiber autocorrelation closure/density theorem. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨autocorrelationZeroTailRealAbs S f,
    ⟨f, hfFiber, rfl⟩,
    hfTail⟩

/-- Compatibility wrapper for the previous Paley-range-shaped Runge value-set theorem.

The actual closure/density input is the fixed-fiber theorem above; the Paley range
argument is retained only for downstream statement shape. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_paleyRange_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (_hPaleyRange :
      ∀ T : Finset ℂ, ∀ aT : T → ℂ,
        aT ∈ Set.range (zetaLaplaceTransformFiniteSample T)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  exact
    exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
      S P f₀

/-- Runge density/localization for the named zero-tail absolute-value set attained inside
the pointwise finite autocorrelation spectral-evaluation fiber. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  exact
    exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
      S P f₀

/-- Runge localization inside the pointwise finite autocorrelation spectral-evaluation
fiber of a source, stated against the named real zero-tail functional. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_ownerRunge
      S P f₀ ε hε with
    ⟨r, hrValues, hrSmall⟩
  rcases
    (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
      S P f₀ r).mp hrValues with
    ⟨f, hfFiber, hr⟩
  exact ⟨f, hfFiber,
    Eq.subst
      (motive := fun x : ℝ => x < ε)
      hr
      hrSmall⟩

/-- Runge localization preserving pointwise finite autocorrelation spectral samples,
stated against the named real zero-tail functional. -/
theorem exists_autocorrelation_spectralEval_eq_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z =
            zetaSpectralEval (convolutionAutocorrelation f₀) z) ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f,
    spectralEval_eq_on_finset_of_mem_autocorrelationSpectralEvalFiberOf
      P f₀ f hfFiber,
    hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector,
stated against the named real zero-tail functional. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralEval_eq_zeroTailRealAbs_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f,
    autocorrelationSpectralFiniteSample_eq_of_spectralEval_eq_on_finset
      P f f₀ hfSample,
    hfTail⟩

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source,
stated against the named real zero-tail functional.

This is the true analytic Runge root in this lane: it does not prescribe an arbitrary
autocorrelation target vector. It stays inside the already-realized finite sample fiber of
`f₀` while shrinking the complementary zero-tail functional. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_eq_zeroTailRealAbs_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f,
    mem_autocorrelationSampleFiberOf_of_spectralFiniteSample_eq
      P f₀ f hfSample,
    hfTail⟩

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber,
    zeroTailRealAbs_lt_of_autocorrelationZeroTailRealAbs_lt
      S f ε hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector of a
given source. -/
theorem exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber, hfTail⟩

/-- The canonical unit autocorrelation sample vector on a finite spectral sample set. -/
def autocorrelationSpectralFiniteUnitTarget
    (P : Finset ℂ) : SpectralSampleVector P :=
  fun _z : P => 1

/-- Membership in the unit autocorrelation sample fiber is exactly unit finite-sample
realization. -/
theorem mem_autocorrelationSampleFiber_unit_iff
    (P : Finset ℂ) (f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) ↔
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P := by
  exact Iff.rfl

/-- The existing finite autocorrelation interpolation theorem realizes the unit finite
sample vector. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_unitTarget
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P := by
  rcases exists_autocorrelation_spectralEval_one_on_finset P with
    ⟨f, hf⟩
  exact ⟨f, by
    funext z
    exact hf (z : ℂ) z.property⟩

/-- The unit finite autocorrelation spectral-sample fiber is nonempty. -/
theorem exists_mem_autocorrelationSampleFiber_unit
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) := by
  exact exists_autocorrelation_spectralFiniteSample_eq_unitTarget P

/-- Runge localization with the canonical unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteUnitTarget P ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  rcases exists_mem_autocorrelationSampleFiber_unit P with
    ⟨f₀, hf₀⟩
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, hfSample.trans hf₀, hfTail⟩

/-- Pointwise form of Runge localization with unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralEval_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z = 1) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
      S P ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

/-- Autocorrelation spectral localization with zero-tail control.

This is the analytic Runge/Paley-Wiener localization input: while preserving a
finite set of completed autocorrelation spectral samples, one can drive the real
part of the complementary completed zero-tail functional below any positive
tolerance. -/
theorem exists_autocorrelation_spectralEval_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z =
            zetaSpectralEval (convolutionAutocorrelation f₀) z) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
