import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZeroTailTomography.Owner

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
    exact
      Exists.intro (f - f₀)
        (And.intro
          (by
            show zetaSpectralEvalPresentationMap P (f - f₀) = 0
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
                exact sub_self (zetaSpectralEvalPresentationMap P f₀))
          (by
            calc
              f = (f - f₀) + f₀ := by
                exact (sub_add_cancel f f₀).symm
              _ = f₀ + (f - f₀) := by
                exact add_comm _ _))
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
  exact
    Quotient.inductionOn C
      (fun X : CompletedBoundaryHilbertSource =>
        abs_nonneg (Complex.re (zetaZeroTail S X.seed)))

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
  exact hrC ▸ completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative S C

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
    exact
      Exists.intro Ctail
        (And.intro hCtail
          (by
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
                    (completedBoundaryHilbertSource (convolutionAutocorrelation f))).symm))
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
  exact hrf ▸ abs_nonneg (Complex.re (zetaZeroTail S (convolutionAutocorrelation f)))

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

/-- Closure of the fixed-fiber zero-tail value set at `0`, together with the
nonnegativity of those values, gives arbitrarily small positive upper bounds.

This is the topological bridge from the Runge/tomography closure theorem to the concrete
small-values statement consumed by downstream zero-tail localization. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hClosure :
      (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  intro ε hε
  match (Metric.mem_closure_iff.mp hClosure) ε hε with
  | ⟨r, hrValues, hdist⟩ =>
    have hrNonnegative :
        0 ≤ r :=
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
        S P f₀ hrValues
    have hdist_zero_r_eq_r : dist 0 r = r := by
      calc
        dist 0 r = dist r 0 := by
          exact dist_comm 0 r
        _ = |r - 0| := by
          exact Real.dist_eq r 0
        _ = |r| := by
          exact congrArg (fun x : ℝ => |x|) (sub_zero r)
        _ = r := by
          exact abs_of_nonneg hrNonnegative
    exact ⟨r,
      hrValues,
      Eq.subst
        (motive := fun x : ℝ => x < ε)
        hdist_zero_r_eq_r
        hdist⟩

/-- Arbitrarily small values of the fixed-fiber zero-tail value set put `0` in the
closure of that value set.

This is the reverse topological bridge: the analytic Runge input may be supplied as
small attained values, while the closure formulation is the canonical cone-radical form. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    Metric.mem_closure_iff.mpr
      (fun ε hε =>
        match hSmall ε hε with
        | ⟨r, hrValues, hrSmall⟩ =>
          Exists.intro r
            (And.intro hrValues
              (by
                have hrNonnegative :
                    0 ≤ r :=
                  autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
                    S P f₀ hrValues
                have hdist_zero_r_eq_r : dist 0 r = r := by
                  calc
                    dist 0 r = dist r 0 := by
                      exact dist_comm 0 r
                    _ = |r - 0| := by
                      exact Real.dist_eq r 0
                    _ = |r| := by
                      exact congrArg (fun x : ℝ => |x|) (sub_zero r)
                    _ = r := by
                      exact abs_of_nonneg hrNonnegative
                exact
                  Eq.subst
                    (motive := fun x : ℝ => x < ε)
                    hdist_zero_r_eq_r.symm
                    hrSmall)))

/-- For the nonnegative fixed-fiber zero-tail value set, closure at `0` is equivalent to
having values below every positive bound. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_iff_has_arbitrarily_small_values
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε := by
  exact
    ⟨autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
        S P f₀,
      autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
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
  exact hCr.symm ▸ completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative S C

/-- Seed interpolation target used to preserve a finite autocorrelation fiber while
annihilating a finite batch of centered zero samples outside the dagger-closed fiber
constraints. -/
def finiteAutocorrelationFiberZeroAnnihilationSeedTarget
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ℂ → ℂ :=
  fun z : ℂ =>
    if _hz : z ∈ daggerClosedSpectralSampleFinset P then
      zetaSpectralEval f₀ z
    else
      0

/-- On the dagger-closed fiber constraints, the finite annihilation target agrees with the
source seed spectral evaluation. -/
theorem finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_of_mem_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {z : ℂ}
    (hz : z ∈ daggerClosedSpectralSampleFinset P) :
    finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z =
      zetaSpectralEval f₀ z := by
  unfold finiteAutocorrelationFiberZeroAnnihilationSeedTarget
  exact dif_pos hz

/-- Away from the dagger-closed fiber constraints, the finite annihilation target is zero. -/
theorem finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_zero_of_not_mem_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {z : ℂ}
    (hz : z ∉ daggerClosedSpectralSampleFinset P) :
    finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z = 0 := by
  unfold finiteAutocorrelationFiberZeroAnnihilationSeedTarget
  exact dif_neg hz

/-- A seed realizing the finite annihilation target preserves the autocorrelation spectral
fiber on `P`. -/
theorem mem_autocorrelationSpectralEvalFiberOf_of_seed_finiteAnnihilationTarget
    (P : Finset ℂ)
    (f₀ f : ZetaAdmissibleFunction)
    (hf :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P →
          zetaSpectralEval f z =
            finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z) :
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
  intro z hz
  have hz_dagger :
      z ∈ daggerClosedSpectralSampleFinset P :=
    mem_daggerClosedSpectralSampleFinset_self P z hz
  have hreflection_dagger :
      -star z ∈ daggerClosedSpectralSampleFinset P :=
    mem_daggerClosedSpectralSampleFinset_reflection P z hz
  have hf_z :
      zetaSpectralEval f z = zetaSpectralEval f₀ z := by
    calc
      zetaSpectralEval f z =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z := by
        exact hf z hz_dagger
      _ = zetaSpectralEval f₀ z := by
        exact
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_of_mem_daggerClosed
            P f₀ hz_dagger
  have hf_reflection :
      zetaSpectralEval f (-star z) = zetaSpectralEval f₀ (-star z) := by
    calc
      zetaSpectralEval f (-star z) =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ (-star z) := by
        exact hf (-star z) hreflection_dagger
      _ = zetaSpectralEval f₀ (-star z) := by
        exact
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_of_mem_daggerClosed
            P f₀ hreflection_dagger
  calc
    zetaSpectralEval (convolutionAutocorrelation f) z =
        zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) := by
      exact zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct f z
    _ =
        zetaSpectralEval f₀ z * star (zetaSpectralEval f (-star z)) := by
      exact congrArg
        (fun w : ℂ => w * star (zetaSpectralEval f (-star z)))
        hf_z
    _ =
        zetaSpectralEval f₀ z * star (zetaSpectralEval f₀ (-star z)) := by
      exact congrArg
        (fun w : ℂ => zetaSpectralEval f₀ z * star w)
        hf_reflection
    _ = zetaSpectralEval (convolutionAutocorrelation f₀) z := by
      exact (zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct f₀ z).symm

/-- A seed realizing the finite annihilation target has zero autocorrelation spectral value
at any centered zero sample outside the dagger-closed fiber constraints. -/
theorem autocorrelationSpectralEval_centeredZero_eq_zero_of_seed_finiteAnnihilationTarget
    (P : Finset ℂ)
    (f₀ f : ZetaAdmissibleFunction)
    {ρ : ℂ}
    (hρ :
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hf :
      zetaSpectralEval f (zetaCenteredZero ρ) =
        finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀
          (zetaCenteredZero ρ)) :
    zetaSpectralEval (convolutionAutocorrelation f) (zetaCenteredZero ρ) = 0 := by
  have hf_zero :
      zetaSpectralEval f (zetaCenteredZero ρ) = 0 := by
    calc
      zetaSpectralEval f (zetaCenteredZero ρ) =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀
            (zetaCenteredZero ρ) := by
        exact hf
      _ = 0 := by
        exact
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_zero_of_not_mem_daggerClosed
            P f₀ hρ
  calc
    zetaSpectralEval (convolutionAutocorrelation f) (zetaCenteredZero ρ) =
        zetaSpectralEval f (zetaCenteredZero ρ) *
          star (zetaSpectralEval f (-star (zetaCenteredZero ρ))) := by
      exact
        zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
          f (zetaCenteredZero ρ)
    _ =
        0 * star (zetaSpectralEval f (-star (zetaCenteredZero ρ))) := by
      exact congrArg
        (fun w : ℂ => w * star (zetaSpectralEval f (-star (zetaCenteredZero ρ))))
        hf_zero
    _ = 0 := by
      exact zero_mul (star (zetaSpectralEval f (-star (zetaCenteredZero ρ))))

/-- Finite Paley-Wiener interpolation can preserve the fixed finite autocorrelation
spectral fiber while annihilating any finite batch of centered zero samples which lies
outside the dagger-closed fiber constraints. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_and_centeredZero_batch_zero_of_disjoint_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        ∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            (zetaCenteredZero ρ) = 0 := by
  let U : Finset ℂ :=
    daggerClosedSpectralSampleFinset P ∪ T.image zetaCenteredZero
  rcases exists_seed_spectralEval_sample_on_finset
      U (finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀) with
    ⟨f, hfU⟩
  have hf_dagger :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P →
          zetaSpectralEval f z =
            finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z := by
    intro z hz
    exact hfU z (Finset.mem_union.mpr (Or.inl hz))
  have hfFiber :
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
    mem_autocorrelationSpectralEvalFiberOf_of_seed_finiteAnnihilationTarget
      P f₀ f hf_dagger
  have hzero :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0 := by
    intro ρ hρT
    have hcenter_mem_U :
        zetaCenteredZero ρ ∈ U := by
      exact
        Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨ρ, hρT, rfl⟩))
    have hf_center :
        zetaSpectralEval f (zetaCenteredZero ρ) =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀
            (zetaCenteredZero ρ) :=
      hfU (zetaCenteredZero ρ) hcenter_mem_U
    exact
      autocorrelationSpectralEval_centeredZero_eq_zero_of_seed_finiteAnnihilationTarget
        P f₀ f (hT ρ hρT) hf_center
  exact ⟨f, hfFiber, hzero⟩

/-- A finite annihilation window plus a uniform tail-control estimate gives a probe with
small named zero-tail absolute value.

This is the finite-set/descent part of the Runge argument: the only analytic input is the
last hypothesis, which says that every interpolating probe annihilating the selected finite
completed-zero window has small complementary zero tail. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_lt_of_finiteWindow_tailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            autocorrelationZeroTailRealAbs S f < ε) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        autocorrelationZeroTailRealAbs S f < ε := by
  rcases
      exists_mem_autocorrelationSpectralEvalFiberOf_and_centeredZero_batch_zero_of_disjoint_daggerClosed
        P f₀ T hT with
    ⟨f, hfFiber, hfzero⟩
  exact ⟨f, hfFiber, htail f hfFiber hfzero⟩

/-- A finite annihilation window plus a uniform tail-control estimate gives a value in the
named zero-tail value set below the requested bound. -/
theorem autocorrelationSpectralEvalFiberZeroTailRealAbsValues_exists_lt_of_finiteWindow_tailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            autocorrelationZeroTailRealAbs S f < ε) :
    ∃ r : ℝ,
      r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
        r < ε := by
  rcases
      exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_lt_of_finiteWindow_tailControl
        S P f₀ ε T hT htail with
    ⟨f, hfFiber, hfTail⟩
  exact
    ⟨autocorrelationZeroTailRealAbs S f,
      (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
        S P f₀ (autocorrelationZeroTailRealAbs S f)).mpr
        ⟨f, hfFiber, rfl⟩,
      hfTail⟩

/-- A chosen finite zero window carries the exact tail-control property needed by the
finite descent argument. -/
def AutocorrelationSpectralEvalFiberFiniteWindowTailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T →
    zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        (∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            (zetaCenteredZero ρ) = 0) →
          autocorrelationZeroTailRealAbs S f < ε

/-- The finite-window tail-control package is exactly the pair of hypotheses consumed by
the finite descent theorem. -/
theorem autocorrelationSpectralEvalFiberFiniteWindowTailControl.elim
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T) :
    (∀ ρ : ℂ, ρ ∈ T →
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            autocorrelationZeroTailRealAbs S f < ε := by
  exact hT

/-- The window-selection form of the Runge/tomographic tail theorem. -/
theorem autocorrelationSpectralEvalFiber_exists_finiteWindowTailControl_of_ownerTailPackage
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (hpackage :
      ∃ T : Finset ℂ,
        AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T) :
    ∃ T : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                (zetaCenteredZero ρ) = 0) →
              autocorrelationZeroTailRealAbs S f < ε := by
  match hpackage with
  | ⟨T, hT⟩ =>
      exact ⟨T,
        autocorrelationSpectralEvalFiberFiniteWindowTailControl.elim
          S P f₀ ε T hT⟩

/-- Runge/tomographic zero-tail localization for all fixed finite autocorrelation
spectral-evaluation fibers.

This is the owner-level analytic proposition.  It does not assert a uniform bounded-family
envelope for every probe in an infinite-dimensional finite-sample fiber; finite spectral
constraints alone do not give such a bound.  The correct Runge output is that the named
zero-tail real absolute value has arbitrarily small attained values inside the fixed
autocorrelation fiber. -/
def AutocorrelationSpectralEvalFiberZeroTailSmallValuesRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε

/-- The owner Runge proposition specialized to a fixed finite autocorrelation
spectral-evaluation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRungeCore
    (hRunge : AutocorrelationSpectralEvalFiberZeroTailSmallValuesRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  exact hRunge S P f₀

/-- Forced dagger-constrained completed-zero contributions outside the excluded set vanish.

These are the completed zeros whose centered samples already lie in the fixed finite
autocorrelation fiber constraints.  They cannot be inserted into a disjoint annihilation
window, so the Runge tail theorem must account for them at the owner level rather than
through finite interpolation. -/
theorem autocorrelationSpectralEvalFiber_forcedDaggerConstrainedZeroContribution_vanishes_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        ∀ ρ : ℂ,
          ZetaCompletedZero ρ →
            ρ ∉ S →
              zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0 := by
  intro f hfFiber ρ hρ hρS hρDagger
  exact False.elim (hdaggerExcluded ρ hρ hρS hρDagger)

/-- Vanishing on an enlarged finite zero window supplies the base-window vanishing
hypothesis required by a polynomial envelope chosen before the enlargement. -/
theorem autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
    (P : Finset ℂ)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (f : ZetaAdmissibleFunction)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    ∀ ρ : ℂ, ρ ∈ T₀ →
      zetaSpectralEval (convolutionAutocorrelation f)
        (zetaCenteredZero ρ) = 0 := by
  intro ρ hρT₀
  exact hfT ρ (hT₀T hρT₀)

/-- A common polynomial envelope selected on `T₀` remains available for probes which
vanish on any later finite window containing `T₀`. -/
theorem autocorrelationSpectralEvalFiber_envelope_of_enlargedWindowVanishes
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (A : ℝ)
    (k : ℕ)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
      ‖zetaZeroSideContribution (ρ : ℂ)
          (convolutionAutocorrelation f)‖ ≤
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  exact
    henv f hfFiber
      (autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
        P T₀ T hT₀T f hfT)

/-- The absolute real zero-tail is controlled by the complex norm of the zero-tail. -/
theorem autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (ε : ℝ)
    (htail :
      ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    autocorrelationZeroTailRealAbs S f < ε := by
  exact
    lt_of_le_of_lt
      (RCLike.abs_re_le_norm
        (zetaZeroTail S (convolutionAutocorrelation f)))
      htail

/-- A zero spectral value at a centered completed zero kills the zero-side contribution. -/
theorem zetaZeroSideContribution_eq_zero_of_centeredZero_spectralEval_zero
    (φ : ZetaAdmissibleFunction)
    (ρ : ℂ)
    (hρ :
      zetaSpectralEval φ ρ = 0) :
    zetaZeroSideContribution ρ φ = 0 := by
  calc
    zetaZeroSideContribution ρ φ =
        (-(zetaZeroMultiplicity ρ : ℂ)) *
          zetaSpectralEval φ ρ := by
      exact zetaZeroSideContribution_def ρ φ
    _ = (-(zetaZeroMultiplicity ρ : ℂ)) * 0 := by
      exact congrArg
        (fun z : ℂ => (-(zetaZeroMultiplicity ρ : ℂ)) * z)
        hρ
    _ = 0 := by
      exact mul_zero (-(zetaZeroMultiplicity ρ : ℂ))

/-- The common polynomial envelope also bounds zeros in the base finite window after the
enlarged window has been killed. -/
theorem zetaZeroSideContribution_norm_le_commonPolynomialEnvelope_of_window
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (henvT :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}) :
    ‖zetaZeroSideContribution (ρ : ℂ)
        (convolutionAutocorrelation f)‖ ≤
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  match (inferInstance : Decidable ((ρ : ℂ) ∈ T₀)) with
  | isTrue hρT₀ =>
      have hρT : (ρ : ℂ) ∈ T := hT₀T hρT₀
      have hcontribution_zero :
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0 :=
        zetaZeroSideContribution_eq_zero_of_centeredZero_spectralEval_zero
          (convolutionAutocorrelation f) (ρ : ℂ) (hfT (ρ : ℂ) hρT)
      have hnorm_zero :
          ‖zetaZeroSideContribution (ρ : ℂ)
              (convolutionAutocorrelation f)‖ = 0 :=
        congrArg norm hcontribution_zero
      have henvelope_nonneg :
          0 ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
        zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ})
      Eq.subst
        (motive := fun x : ℝ =>
          x ≤
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
        hnorm_zero.symm
        henvelope_nonneg
  | isFalse hρT₀ =>
      henvT f hfFiber hfT
        (⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT₀⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀})

/-- Removing a finite killed zero window identifies the zero-tail `tsum` with the
complementary completed-zero `tsum`. -/
theorem zetaZeroTail_eq_complement_tsum_of_zero_on_window_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (φ : ZetaAdmissibleFunction)
    (hsummable :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} =>
          zetaZeroSideContribution (ρ : ℂ) φ))
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) φ = 0) :
    zetaZeroTail S φ =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) φ := by
  let α := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}
  let β := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T}
  let contribution : α → ℂ :=
    fun ρ => zetaZeroSideContribution (ρ : ℂ) φ
  let killed : Set α := fun ρ => (ρ : ℂ) ∈ T
  let complementEquiv : β ≃ (killedᶜ : Set α) where
    toFun := fun ρ =>
      ⟨⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1⟩, ρ.2.2.2⟩
    invFun := fun ρ =>
      ⟨(ρ : α), ρ.1.2.1, ρ.1.2.2, ρ.2⟩
    left_inv := fun ρ => Subtype.ext rfl
    right_inv := fun ρ => Subtype.ext rfl
  have hsplit :
      (∑' ρ : killed, contribution ρ) +
          (∑' ρ : (killedᶜ : Set α), contribution ρ) =
        ∑' ρ : α, contribution ρ :=
    tsum_subtype_add_tsum_subtype_compl hsummable killed
  have hkilled_fun :
      (fun ρ : killed => contribution ρ) = fun _ρ : killed => 0 :=
    funext
      (fun ρ =>
        hzeroT (ρ : α) ρ.2)
  have hkilled_tsum :
      (∑' ρ : killed, contribution ρ) = 0 :=
    Eq.trans
      (congrArg
        (fun f : killed → ℂ => ∑' ρ : killed, f ρ)
        hkilled_fun)
      tsum_zero
  have htail_unfold :
      zetaZeroTail S φ = ∑' ρ : α, contribution ρ := rfl
  have hright_transport :
      (∑' ρ : (killedᶜ : Set α), contribution ρ) =
        ∑' ρ : β, zetaZeroSideContribution (ρ : ℂ) φ :=
    have hraw :
        (∑' ρ : (killedᶜ : Set α), contribution ρ) =
          ∑' ρ : β, contribution (complementEquiv ρ) :=
      ((complementEquiv).tsum_eq
        (fun ρ : (killedᶜ : Set α) => contribution ρ)).symm
    have hterm :
        (fun ρ : β => contribution (complementEquiv ρ)) =
          fun ρ : β => zetaZeroSideContribution (ρ : ℂ) φ :=
      funext (fun _ρ => rfl)
    Eq.trans hraw
      (congrArg (fun F : β → ℂ => ∑' ρ : β, F ρ) hterm)
  have htotal_eq_right :
      (∑' ρ : α, contribution ρ) =
        ∑' ρ : β, zetaZeroSideContribution (ρ : ℂ) φ :=
    Eq.trans
      hsplit.symm
      (Eq.trans
        (congrArg
          (fun z : ℂ =>
            z + (∑' ρ : (killedᶜ : Set α), contribution ρ))
          hkilled_tsum)
        (Eq.trans
          (zero_add (∑' ρ : (killedᶜ : Set α), contribution ρ))
          hright_transport))
  exact Eq.trans htail_unfold htotal_eq_right

/-- The norm of a complementary completed-zero `tsum` is bounded by a summable
nonnegative polynomial envelope. -/
theorem zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_tsum_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  let envelope :
      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T} → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let contribution :
      {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T} → ℂ :=
    fun ρ =>
      zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)
  have henvelope_summable : Summable envelope :=
    hsum.subtype
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        (ρ : ℂ) ∉ S ∧ (ρ : ℂ) ∉ T)
  have hnorm_summable : Summable (fun ρ => ‖contribution ρ‖) := by
    refine Summable.of_norm_bounded envelope henvelope_summable ?_
    intro ρ
    calc
      ‖‖contribution ρ‖‖ = ‖contribution ρ‖ := by
        exact norm_norm (contribution ρ)
      _ ≤ envelope ρ := hbound ρ
  have hnorm_tsum :
      ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          contribution ρ)‖ ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          ‖contribution ρ‖ :=
    norm_tsum_le_tsum_norm hnorm_summable
  have hmajorant_tsum :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          ‖contribution ρ‖) ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          envelope ρ :=
    tsum_le_tsum hbound hnorm_summable henvelope_summable
  exact hnorm_tsum.trans hmajorant_tsum

/-- The remaining summable-tail cutoff for a common completed-zero polynomial envelope.

This is the finite-excision estimate behind the common-envelope norm estimate: after
the killed finite window is removed, the remaining complementary `tsum` is bounded by
the complementary polynomial-envelope tail. -/
theorem zetaZeroTail_norm_le_commonPolynomialEnvelope_complement_tsum_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ ≤
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  have htail_eq :
      zetaZeroTail S (convolutionAutocorrelation f) =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) :=
    let envelope :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℝ :=
      fun ρ =>
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
    let contribution :
        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S} → ℂ :=
      fun ρ =>
        zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)
    have henvelope_summable : Summable envelope :=
      hsum.subtype
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          (ρ : ℂ) ∉ S)
    have htail_contribution_summable : Summable contribution := by
      exact
        Summable.of_norm_bounded envelope henvelope_summable
          (fun ρ =>
            match (inferInstance : Decidable ((ρ : ℂ) ∈ T)) with
            | isTrue hρT =>
                have hcontribution_zero : contribution ρ = 0 :=
                  hzeroT ρ hρT
                have hnorm_zero : ‖contribution ρ‖ = 0 :=
                  congrArg norm hcontribution_zero
                have henvelope_nonneg : 0 ≤ envelope ρ :=
                  zetaZeroMultiplicityTransformEnvelope_nonnegative hA k
                    (⟨(ρ : ℂ), ρ.2.1⟩ :
                      {ρ : ℂ // ZetaCompletedZero ρ})
                calc
                  ‖‖contribution ρ‖‖ = ‖contribution ρ‖ := by
                    exact norm_norm (contribution ρ)
                  _ = 0 := hnorm_zero
                  _ ≤ envelope ρ := henvelope_nonneg
            | isFalse hρT =>
                calc
                  ‖‖contribution ρ‖‖ = ‖contribution ρ‖ := by
                    exact norm_norm (contribution ρ)
                  _ ≤ envelope ρ :=
                    hbound
                      (⟨(ρ : ℂ), ρ.2.1, ρ.2.2, hρT⟩ :
                        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T}))
    zetaZeroTail_eq_complement_tsum_of_zero_on_window_ownerGap
      S T (convolutionAutocorrelation f) htail_contribution_summable hzeroT
  have hcomplement_bound :
      ‖(∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f))‖ ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
    zetaZeroTail_complement_tsum_norm_le_commonPolynomialEnvelope_tsum_ownerGap
      S T A k hsum f hbound
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
      htail_eq.symm
      hcomplement_bound

/-- A summable completed-zero polynomial envelope admits a finite supported cutoff.

The returned support condition records that the enlargement only adds completed zeros
outside `S`; this is the set-theoretic fact needed to transport any upstream
dagger-exclusion hypothesis to the selected window. -/
theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_supported_ownerGap
    (S : Finset ℂ)
    (T₀ : Finset ℂ)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          ρ ∈ T₀ ∨ (ZetaCompletedZero ρ ∧ ρ ∉ S)) ∧
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε := by
  let β := {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}
  let envelopeβ : β → ℝ :=
    fun ρ =>
      A * zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), ρ.2.1⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))
  let base : Finset β :=
    T₀.preimage
      (fun ρ : β => (ρ : ℂ))
      (Subtype.val_injective.injOn)
  have htail_eventually :
      ∀ᶠ U in (atTop : Filter (Finset β)),
        (∑' ρ : {ρ : β // ρ ∉ U}, envelopeβ ρ) < ε :=
    (tendsto_tsum_compl_atTop_zero envelopeβ)
      (Iio ε)
      (Iio_mem_nhds hε)
  have hbase_eventually :
      ∀ᶠ U in (atTop : Filter (Finset β)), base ⊆ U :=
    eventually_ge_atTop base
  match (hbase_eventually.and htail_eventually).exists with
  | ⟨U, hUbase, hUtail⟩ =>
      let T : Finset ℂ := T₀ ∪ U.image
        (⟨(fun ρ : β => (ρ : ℂ)), Subtype.val_injective⟩ :
          β ↪ ℂ)
      have hT₀T : T₀ ⊆ T :=
        Finset.subset_union_left
      have hsupport :
          ∀ ρ : ℂ, ρ ∈ T →
            ρ ∈ T₀ ∨ (ZetaCompletedZero ρ ∧ ρ ∉ S) := by
        intro ρ hρT
        match Finset.mem_union.mp hρT with
        | Or.inl hρT₀ =>
            exact Or.inl hρT₀
        | Or.inr hρU =>
            match Finset.mem_image.mp hρU with
            | ⟨ρZero, hρZeroU, hρZero_eq⟩ =>
                exact Or.inr
                  (Eq.subst
                    (motive := fun z : ℂ => ZetaCompletedZero z ∧ z ∉ S)
                    hρZero_eq
                    ρZero.2)
      have htail_transport :
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
            ∑' ρ : {ρ : β // ρ ∉ U}, envelopeβ ρ := by
        let γ :=
          {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T}
        let δ := {ρ : β // ρ ∉ U}
        let tailEquiv : γ ≃ δ where
          toFun := fun ρ =>
            ⟨⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1⟩,
              fun hρU =>
                ρ.2.2.2
                  (Finset.mem_union.mpr
                    (Or.inr
                      (Finset.mem_image.mpr
                        ⟨⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1⟩,
                          hρU, rfl⟩)))⟩
          invFun := fun ρ =>
            ⟨(ρ : β),
              ρ.1.2.1,
              ρ.1.2.2,
              fun hρT =>
                match Finset.mem_union.mp hρT with
                | Or.inl hρT₀ =>
                    ρ.2
                      (hUbase
                        (Finset.mem_preimage.mpr hρT₀))
                | Or.inr hρImage =>
                    match Finset.mem_image.mp hρImage with
                    | ⟨ρU, hρU, hρ_eq⟩ =>
                        ρ.2
                          (Eq.subst
                            (motive := fun z : β => z ∈ U)
                            (Subtype.ext hρ_eq).symm
                            hρU)⟩
          left_inv := fun ρ => Subtype.ext rfl
          right_inv := fun ρ => Subtype.ext rfl
        have hraw :
            (∑' ρ : γ,
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
              ∑' ρ : δ,
                A * zetaCompletedZeroCenteredHeight
                  (⟨((tailEquiv.symm ρ : γ) : ℂ),
                    (tailEquiv.symm ρ : γ).2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
          (tailEquiv.symm.tsum_eq
            (fun ρ : γ =>
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))).symm
        have hterm :
            (fun ρ : δ =>
              A * zetaCompletedZeroCenteredHeight
                (⟨((tailEquiv.symm ρ : γ) : ℂ),
                  (tailEquiv.symm ρ : γ).2.1⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) =
              fun ρ : δ => envelopeβ ρ :=
          funext (fun _ρ => rfl)
        Eq.trans hraw
          (congrArg
            (fun F : δ → ℝ => ∑' ρ : δ, F ρ)
            hterm)
      have htail :
          (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
            A * zetaCompletedZeroCenteredHeight
              (⟨(ρ : ℂ), ρ.2.1⟩ :
                {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε :=
        Eq.subst
          (motive := fun x : ℝ => x < ε)
          htail_transport.symm
          hUtail
      exact ⟨T, hT₀T, hsupport, htail⟩

/-- A summable completed-zero polynomial envelope admits a dagger-disjoint finite
cutoff once completed zeros outside `S` have been separated from the dagger-closed
finite spectral constraints. -/
theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_awayFromDagger_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε := by
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_supported_ownerGap
        S T₀ ε hε A k hsum with
  | ⟨T, hT₀T, hsupport, htail⟩ =>
      have hT :
          ∀ ρ : ℂ, ρ ∈ T →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P := by
        intro ρ hρT
        match hsupport ρ hρT with
        | Or.inl hρT₀ =>
            exact hT₀ ρ hρT₀
        | Or.inr hρZeroOutside =>
            exact hdaggerExcluded ρ hρZeroOutside.1 hρZeroOutside.2
      exact ⟨T, hT₀T, hT, htail⟩

/-- A summable completed-zero polynomial envelope admits a finite killed window whose
complementary envelope tail has total mass below the chosen tolerance. -/
theorem exists_commonPolynomialEnvelope_completedZeroTailCutoff_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε := by
  exact
    exists_commonPolynomialEnvelope_completedZeroTailCutoff_awayFromDagger_ownerGap
      S P T₀ hT₀ hdaggerExcluded ε hε A k hsum

/-- The selected finite cutoff converts the complementary envelope bound into the
requested zero-tail norm estimate. -/
theorem zetaZeroTail_norm_lt_of_commonPolynomialEnvelope_tailCutoff_ownerGap
    (S : Finset ℂ)
    (T : Finset ℂ)
    (ε : ℝ)
    (hε : 0 < ε)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hzeroT :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S},
        (ρ : ℂ) ∈ T →
          zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f) = 0)
    (hbound :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ ≤
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (htail :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε := by
  exact
    lt_of_le_of_lt
      (zetaZeroTail_norm_le_commonPolynomialEnvelope_complement_tsum_ownerGap
        S T A k hA hsum f hzeroT hbound)
      htail

/-- Common-envelope zero-tail norm estimate after the selected interpolation window.

This is the complex norm form of the remaining summable-tail theorem.  It combines the
finite/complement excision of `zetaZeroTail`, vanishing on the selected window, forced
vanishing on dagger-constrained zeros, and summability of the polynomial envelope. -/
theorem zetaZeroTail_norm_lt_of_commonPolynomialEnvelope_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (htail :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε)
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henvT :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε := by
  exact
    zetaZeroTail_norm_lt_of_commonPolynomialEnvelope_tailCutoff_ownerGap
      S T ε hε A k hA hsum f
      (fun ρ hρT =>
        zetaZeroSideContribution_eq_zero_of_centeredZero_spectralEval_zero
          (convolutionAutocorrelation f) (ρ : ℂ) (hfT (ρ : ℂ) hρT))
      (fun ρ =>
        zetaZeroSideContribution_norm_le_commonPolynomialEnvelope_of_window
          S P f₀ T₀ T hT₀T A k hA henvT f hfFiber hfT
          (⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S}))
      htail

/-- Zero-tail control from a common polynomial envelope already transported to the
selected interpolation window.

This is the remaining analytic summability statement: after forced dagger-constrained
zeros have been removed and the selected finite window has been killed, the zero-side
tail is dominated by a summable polynomial height envelope. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_commonPolynomialEnvelope_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (htail :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε)
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henvT :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    autocorrelationZeroTailRealAbs S f < ε := by
  exact
    autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
      S f ε
      (zetaZeroTail_norm_lt_of_commonPolynomialEnvelope_ownerGap
        S P f₀ ε hε T₀ T hT₀T hT A k hA hsum htail hforced henvT
        f hfFiber hfT)

/-- A selected enlarged window controls the zero tail once the common polynomial
envelope is available on the base window.

This is the analytic tail-truncation step after the finite-window selection has already
been made: forced dagger-constrained zeros contribute zero, zeros in the selected window
are killed by interpolation, and the remaining completed zeros are dominated by the
common polynomial envelope. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_selectedPolynomialEnvelopeWindow_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (htail :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
        A * zetaCompletedZeroCenteredHeight
          (⟨(ρ : ℂ), ρ.2.1⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε)
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)))
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    autocorrelationZeroTailRealAbs S f < ε := by
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_commonPolynomialEnvelope_ownerGap
      S P f₀ ε hε T₀ T hT₀T hT A k hA hsum htail hforced
      (autocorrelationSpectralEvalFiber_envelope_of_enlargedWindowVanishes
        S P f₀ T₀ T hT₀T A k henv)
      f hfFiber hfT

/-- Finite selection of a dagger-disjoint window extending the base window.

The selected-window theorem owns only the finite dagger-disjoint enlargement.  The
conversion from that selected window and the common polynomial envelope to the actual
zero-tail estimate is handled by
`autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_selectedPolynomialEnvelopeWindow_ownerGap`. -/
theorem autocorrelationSpectralEvalFiber_selectedPolynomialEnvelopeTailWindow_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T},
          A * zetaCompletedZeroCenteredHeight
            (⟨(ρ : ℂ), ρ.2.1⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) < ε := by
  exact
    exists_commonPolynomialEnvelope_completedZeroTailCutoff_ownerGap
      S P T₀ hT₀ hdaggerExcluded ε hε A k hsum

/-- Finite-window enlargement for the polynomial-envelope zero-tail estimate.

This is the set-theoretic part of the tail truncation theorem.  Starting from a
dagger-disjoint finite window `T₀`, choose a larger finite completed-zero window which is
still dagger-disjoint and whose complement has sufficiently small polynomial envelope
mass after the forced dagger-constrained zeros are removed.  The conclusion is stated in
the exact tail-control form consumed by finite interpolation; the proof must combine the
summable polynomial envelope with the vanishing of the forced dagger-constrained
contributions. -/
theorem autocorrelationSpectralEvalFiber_polynomialEnvelopeTailWindow_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
          ∀ f : ZetaAdmissibleFunction,
            f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
              (∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval (convolutionAutocorrelation f)
                  (zetaCenteredZero ρ) = 0) →
                autocorrelationZeroTailRealAbs S f < ε := by
  match
      autocorrelationSpectralEvalFiber_selectedPolynomialEnvelopeTailWindow_ownerGap
        S P f₀ ε hε T₀ hT₀ hdaggerExcluded A k hA hsum hforced henv with
  | ⟨T, hT₀T, hT, htailSmall⟩ =>
      exact
        ⟨T, hT₀T, hT,
          fun f hfFiber hfT =>
            autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_selectedPolynomialEnvelopeWindow_ownerGap
              S P f₀ ε T₀ T hT₀T hT A k hA hsum htailSmall hforced henv
              f hfFiber hfT⟩

/-- Tail estimate after a dagger-disjoint polynomial-envelope window has been chosen.

This is only the projection from the selected-window package to the single-probe estimate
used by the descent argument. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_polynomialEnvelopeTailWindow_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T₀ T : Finset ℂ)
    (hT₀T : T₀ ⊆ T)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            autocorrelationZeroTailRealAbs S f < ε)
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaSpectralEval (convolutionAutocorrelation f)
          (zetaCenteredZero ρ) = 0) :
    autocorrelationZeroTailRealAbs S f < ε := by
  exact htail f hfFiber hfT

/-- The finite-window tail-control package obtained from a common polynomial envelope. -/
theorem autocorrelationSpectralEvalFiber_polynomialEnvelopeFiniteTailControl_ownerPackage
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
          ∀ f : ZetaAdmissibleFunction,
            f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
              (∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval (convolutionAutocorrelation f)
                  (zetaCenteredZero ρ) = 0) →
                autocorrelationZeroTailRealAbs S f < ε := by
  match
      autocorrelationSpectralEvalFiber_polynomialEnvelopeTailWindow_ownerGap
        S P f₀ ε hε T₀ hT₀ hdaggerExcluded A k hA hsum hforced henv with
  | ⟨T, hT₀T, hT, htail⟩ =>
      exact
        ⟨T, hT₀T, hT,
          fun f hfFiber hfT =>
            autocorrelationSpectralEvalFiber_zeroTailRealAbs_lt_of_polynomialEnvelopeTailWindow_ownerGap
              S P f₀ ε T₀ T hT₀T hT htail
              f hfFiber hfT⟩

/-- Polynomial-envelope truncation for the complementary completed-zero tail.

This is the exact summability step left after the finite interpolation and the forced
dagger-constrained zero obstruction have been separated.  The finite window may only be
enlarged by zeros whose centered samples are outside `daggerClosedSpectralSampleFinset P`;
zeros whose centered samples lie in that dagger-closed finite set are controlled by
`hforced`, while all other complementary zeros are controlled by the common polynomial
envelope `henv` and the completed-zero counting summability theorem. -/
theorem autocorrelationSpectralEvalFiber_polynomialEnvelopeFiniteTailControl_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
          ∀ f : ZetaAdmissibleFunction,
            f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
              (∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval (convolutionAutocorrelation f)
                  (zetaCenteredZero ρ) = 0) →
                autocorrelationZeroTailRealAbs S f < ε := by
  exact
    autocorrelationSpectralEvalFiber_polynomialEnvelopeFiniteTailControl_ownerPackage
      S P f₀ ε hε T₀ hT₀ hdaggerExcluded A k hA hsum hforced henv

/-- A common polynomial zero-side envelope has a finite complementary tail below the
requested tolerance after enlarging the finite zero window. -/
theorem autocorrelationSpectralEvalFiber_finiteWindowComplementSummability_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ)))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ,
            ZetaCompletedZero ρ →
              ρ ∉ S →
                zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                  zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ :
                    {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
          ∀ f : ZetaAdmissibleFunction,
            f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
              (∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval (convolutionAutocorrelation f)
                  (zetaCenteredZero ρ) = 0) →
                autocorrelationZeroTailRealAbs S f < ε := by
  exact
    autocorrelationSpectralEvalFiber_polynomialEnvelopeFiniteTailControl_ownerGap
      S P f₀ ε hε T₀ hT₀ hdaggerExcluded A k hA hsum hforced henv

/-- Completed zeros outside the excluded zero set are separated from the dagger-closed
finite spectral constraints.

This is the exact exclusion needed by the polynomial-envelope tail selector: forced
vanishing controls actual zero-side contributions at dagger-constrained zeros, but it
does not remove their positive envelope mass from a purely summable envelope tail. -/
theorem autocorrelationSpectralEvalFiber_completedZero_daggerExclusion_ownerGap
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P := by
  exact hdaggerExcluded

/-- Owner theorem: noncircular zero-tail closure density for autocorrelation spectral
fibers.

The proof surface is purely topological once the owner Runge/tomography theorem supplies
arbitrarily small attained zero-tail values in the fixed finite autocorrelation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerGap
    (hRunge : AutocorrelationSpectralEvalFiberZeroTailSmallValuesRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure
      (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
      S P f₀
      (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRungeCore
        hRunge S P f₀)

variable
  (hZeroTailSmallValuesOwnerRunge :
    ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε)

include hZeroTailSmallValuesOwnerRunge

/-- Nonlinear finite autocorrelation-cone density in the zero-tail quotient.

This is the actual Runge/GNS input for the positive cone.  The linear finite
sample surjectivity theorem supplies seed interpolation data, but the passage
to autocorrelation probes and then to the completed ordered-heart quotient is
nonlinear and is owned here rather than hidden in a downstream wrapper. -/
theorem autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) := by
  have hConcreteClosure :
      (0 : ℝ) ∈
        closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
      S P f₀
      (hZeroTailSmallValuesOwnerRunge S P f₀)
  have hConcrete_eq_quotient :
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ =
        autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀ :=
    Eq.trans
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
        S P f₀).symm
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
        S P f₀)
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      hConcrete_eq_quotient
      hConcreteClosure

/-- Positive-cone/GNS density at the quotient-level zero-tail functional.

This is the nonlinear transport from finite seed spectral interpolation to the
positive/autocorrelation cone density statement in the completed zero-tail ordered-heart
quotient.

This is the nonlinear positive-cone transport primitive: it is a theorem about the
autocorrelation cone image in the fixed finite spectral fiber, not about the raw linear
Laplace-evaluation map.  The linear surjectivity argument is retained in the signature
for compatibility with older callers, while the proof delegates to the nonlinear owner
Runge theorem above. -/
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
  exact
    autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_ownerRunge
      hZeroTailSmallValuesOwnerRunge
      S P f₀

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
      hZeroTailSmallValuesOwnerRunge
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
        hZeroTailSmallValuesOwnerRunge
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
        hZeroTailSmallValuesOwnerRunge
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
        hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
      S P f₀

/-- Compatibility name for the autocorrelation-cone Runge closure/radical condition. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
      hZeroTailSmallValuesOwnerRunge
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
  exact hZeroTailSmallValuesOwnerRunge S P f₀

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
        hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber, hfTail⟩

omit hZeroTailSmallValuesOwnerRunge

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

include hZeroTailSmallValuesOwnerRunge

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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
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
      hZeroTailSmallValuesOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
