import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralLinearity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZeroTailTomography.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleExponentialModulation

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
  map_add' := fun f g =>
    funext (fun z => zetaSpectralEval_add f g (z : ℂ))
  map_smul' := fun c f =>
    funext (fun z =>
      Eq.trans
        (zetaSpectralEval_smul c f (z : ℂ))
        (Eq.refl (c * zetaSpectralEval f (z : ℂ))))

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

/-- Equality with the source target makes the source difference a kernel element. -/
theorem zetaSpectralEvalPresentation_sourceDifference_mem_ker
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf : zetaSpectralEvalPresentationMap P f =
      zetaSpectralEvalPresentationTarget P f₀) :
    f - f₀ ∈ LinearMap.ker (zetaSpectralEvalPresentationMap P) :=
  let hsub :
      zetaSpectralEvalPresentationMap P (f - f₀) =
        zetaSpectralEvalPresentationMap P f -
          zetaSpectralEvalPresentationMap P f₀ :=
    LinearMap.map_sub (zetaSpectralEvalPresentationMap P) f f₀
  let htarget :
      zetaSpectralEvalPresentationTarget P f₀ =
        zetaSpectralEvalPresentationMap P f₀ :=
    Eq.refl (zetaSpectralEvalPresentationMap P f₀)
  Eq.trans
    hsub
    (Eq.trans
      (congrArg
        (fun value : P → ℂ => value - zetaSpectralEvalPresentationMap P f₀)
        hf)
      (Eq.trans
        (congrArg
          (fun value : P → ℂ => value - zetaSpectralEvalPresentationMap P f₀)
          htarget)
        (sub_self (zetaSpectralEvalPresentationMap P f₀))))

/-- Every source equals the base source plus its source difference. -/
theorem zetaSpectralEvalPresentation_eq_source_add_sourceDifference
    (f₀ f : ZetaAdmissibleFunction) :
    f = f₀ + (f - f₀) :=
  Eq.trans (sub_add_cancel f f₀).symm (add_comm (f - f₀) f₀)

/-- A kernel translate maps to the source presentation target. -/
theorem zetaSpectralEvalPresentation_eq_target_of_kernel_translate
    (P : Finset ℂ) (f₀ f k : ZetaAdmissibleFunction)
    (hk : k ∈ LinearMap.ker (zetaSpectralEvalPresentationMap P))
    (hkf : f = f₀ + k) :
    zetaSpectralEvalPresentationMap P f =
      zetaSpectralEvalPresentationTarget P f₀ :=
  Eq.trans
    (congrArg (zetaSpectralEvalPresentationMap P) hkf)
    (Eq.trans
      (LinearMap.map_add (zetaSpectralEvalPresentationMap P) f₀ k)
      (Eq.trans
        (congrArg
          (fun value : P → ℂ => zetaSpectralEvalPresentationMap P f₀ + value)
          hk)
        (add_zero (zetaSpectralEvalPresentationMap P f₀))))

/-- The raw finite spectral presentation fiber over a source target is the affine translate
of the kernel of the presentation map. -/
theorem zetaSpectralEvalPresentationFiber_eq_source_add_ker
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    ZetaSpectralEvalPresentationFiber P
        (zetaSpectralEvalPresentationTarget P f₀) =
      fun f : ZetaAdmissibleFunction =>
        ∃ k : ZetaAdmissibleFunction,
          k ∈ LinearMap.ker (zetaSpectralEvalPresentationMap P) ∧
            f = f₀ + k :=
  Set.ext (fun f =>
    Iff.intro
      (fun hf =>
        Exists.intro (f - f₀)
          (And.intro
            (zetaSpectralEvalPresentation_sourceDifference_mem_ker P f₀ f hf)
            (zetaSpectralEvalPresentation_eq_source_add_sourceDifference f₀ f)))
      (fun hf =>
        match hf with
        | ⟨k, hk, hkf⟩ =>
            zetaSpectralEvalPresentation_eq_target_of_kernel_translate
              P f₀ f k hk hkf))

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

def AutocorrelationSpectralEvalFiberOfShifted
    (P : Finset ℂ)
    (c : ℝ)
    (f₀ : ZetaAdmissibleFunction) : Set ZetaAdmissibleFunction :=
  fun f : ZetaAdmissibleFunction =>
    ∀ z : ℂ, z ∈ P →
      zetaSpectralEval (convolutionAutocorrelationShifted c f) z =
        zetaSpectralEval (convolutionAutocorrelationShifted c f₀) z

/-- The pointwise finite spectral-evaluation fiber is the presentation fiber over the
source target. -/
theorem AutocorrelationSpectralEvalFiberOf_eq_presentationFiber
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    AutocorrelationSpectralEvalFiberOf P f₀ =
      AutocorrelationSpectralEvalPresentationFiber P
        (autocorrelationSpectralEvalPresentationTarget P f₀) :=
  Set.ext (fun f =>
    Iff.intro
      (fun hf => funext (fun z => hf (z : ℂ) z.property))
      (fun hf z hz => congrFun hf ⟨z, hz⟩))

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
      completedBoundaryHilbertSourceZeroTailRealAbs S Y :=
  hXY S

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
      completedBoundaryHilbertSourceZeroTailRealAbs S X :=
  Eq.refl
    (completedBoundaryOrderedHeartZeroTailRealAbs S
      (completedBoundaryZeroTailOrderedHeartClass X))

/-- Spectral tomography identifies the quotient zero-tail scalar. -/
theorem completedBoundaryOrderedHeartZeroTailRealAbs_eq_of_spectralTomography
    (S : Finset ℂ)
    {X Y : CompletedBoundaryHilbertSource}
    (hXY :
      CompletedBoundaryHilbertSource.SpectrallyTomographicallyEquivalent X Y) :
    completedBoundaryOrderedHeartZeroTailRealAbs S
        (completedBoundaryZeroTailOrderedHeartClass X) =
      completedBoundaryOrderedHeartZeroTailRealAbs S
        (completedBoundaryZeroTailOrderedHeartClass Y) :=
  congrArg (completedBoundaryOrderedHeartZeroTailRealAbs S)
    (completedBoundaryZeroTailOrderedHeartClass_eq_of_spectralTomography hXY)

/-- The quotient zero-tail absolute-value functional is nonnegative. -/
theorem completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative
    (S : Finset ℂ) (C : CompletedBoundaryZeroTailOrderedHeartClass) :
    0 ≤ completedBoundaryOrderedHeartZeroTailRealAbs S C :=
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
    0 ≤ r :=
  match hr with
  | ⟨C, hClassEvidence, hrC⟩ =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hrC.symm
        (completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative S C)

/-- The quotient-level zero-tail value set is the image of the fixed finite
autocorrelation cone fiber in the zero-tail ordered-heart quotient under the quotient
zero-tail functional. -/
theorem autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_eq_image
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues S P f₀ =
      (completedBoundaryOrderedHeartZeroTailRealAbs S) ''
        autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀ :=
  Set.ext (fun r =>
    Iff.intro
      (fun hr =>
        match hr with
        | ⟨C, hC, hrC⟩ => ⟨C, hC, hrC.symm⟩)
      (fun hr =>
        match hr with
        | ⟨C, hC, hCr⟩ => ⟨C, hC, hCr.symm⟩))

/-- The absolute real completed zero-tail functional for an autocorrelation probe. -/
def autocorrelationZeroTailRealAbs
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) : ℝ :=
  |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))|

/-- The absolute real zero-tail is controlled by the complex norm of the zero-tail. -/
theorem autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
    (S : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (ε : ℝ)
    (htail :
      ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    autocorrelationZeroTailRealAbs S f < ε :=
  let hrealNorm :
      autocorrelationZeroTailRealAbs S f ≤
        ‖zetaZeroTail S (convolutionAutocorrelation f)‖ :=
    RCLike.abs_re_le_norm
      (zetaZeroTail S (convolutionAutocorrelation f))
  lt_of_le_of_lt hrealNorm htail

/-- The named autocorrelation zero-tail absolute value is the absolute value of the real
part of the completed zero tail. -/
theorem autocorrelationZeroTailRealAbs_eq
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    autocorrelationZeroTailRealAbs S f =
      |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))| :=
  Eq.refl (autocorrelationZeroTailRealAbs S f)

/-- The autocorrelation zero-tail value is the Hilbert-source zero-tail value. -/
theorem autocorrelationZeroTailRealAbs_eq_hilbertSourceZeroTailRealAbs
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    autocorrelationZeroTailRealAbs S f =
      completedBoundaryHilbertSourceZeroTailRealAbs S
        (completedBoundaryHilbertSource (convolutionAutocorrelation f)) :=
  Eq.refl (autocorrelationZeroTailRealAbs S f)

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
        autocorrelationSpectralFiniteSample P f₀ :=
  Iff.intro
    (fun equality => equality)
    (fun equality => equality)

/-- Finite autocorrelation sample equality gives membership in the source fiber. -/
theorem mem_autocorrelationSampleFiberOf_of_spectralFiniteSample_eq
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf :
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteSample P f₀) :
    f ∈ AutocorrelationSampleFiberOf P f₀ :=
  hf

/-- Membership in the source fiber gives finite autocorrelation sample equality. -/
theorem spectralFiniteSample_eq_of_mem_autocorrelationSampleFiberOf
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf : f ∈ AutocorrelationSampleFiberOf P f₀) :
    autocorrelationSpectralFiniteSample P f =
      autocorrelationSpectralFiniteSample P f₀ :=
  hf

/-- Membership in the pointwise finite spectral-evaluation fiber is exactly pointwise
preservation on the finite sample set. -/
theorem mem_autocorrelationSpectralEvalFiberOf_iff
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ↔
      ∀ z : ℂ, z ∈ P →
        zetaSpectralEval (convolutionAutocorrelation f) z =
          zetaSpectralEval (convolutionAutocorrelation f₀) z :=
  Iff.intro
    (fun equality => equality)
    (fun equality => equality)

/-- Pointwise preservation gives membership in the finite spectral-evaluation fiber. -/
theorem mem_autocorrelationSpectralEvalFiberOf_of_spectralEval_eq_on_finset
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf :
      ∀ z : ℂ, z ∈ P →
        zetaSpectralEval (convolutionAutocorrelation f) z =
          zetaSpectralEval (convolutionAutocorrelation f₀) z) :
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
  hf

/-- Membership in the finite spectral-evaluation fiber gives pointwise preservation on
the finite sample set. -/
theorem spectralEval_eq_on_finset_of_mem_autocorrelationSpectralEvalFiberOf
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hf : f ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    ∀ z : ℂ, z ∈ P →
      zetaSpectralEval (convolutionAutocorrelation f) z =
        zetaSpectralEval (convolutionAutocorrelation f₀) z :=
  hf

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
        (completedBoundaryHilbertSource (convolutionAutocorrelation g)) :=
  completedBoundaryZeroTailOrderedHeartClass_eq_of_contourChannelTomography
    (X := completedBoundaryHilbertSource (convolutionAutocorrelation f))
    (Y := completedBoundaryHilbertSource (convolutionAutocorrelation g))
    hfg

/-- The named real-absolute tail bound is the unnamed zero-tail real-absolute bound. -/
theorem zeroTailRealAbs_lt_of_autocorrelationZeroTailRealAbs_lt
    (S : Finset ℂ) (f : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hf : autocorrelationZeroTailRealAbs S f < ε) :
    |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))| < ε :=
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
      autocorrelationSpectralFiniteSample P g :=
  funext (fun z => hP (z : ℂ) z.property)

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
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ :=
  Set.ext (fun r =>
    Iff.intro
      (fun hr =>
        match hr with
        | ⟨C, hImageEvidence, f, hfFiber, hClassEvidence, hrValue⟩ =>
            ⟨f, hfFiber, hrValue⟩)
      (fun hr =>
        match hr with
        | ⟨f, hfFiber, hrValue⟩ =>
            let C : CompletedBoundaryOrderedHeartClass :=
              completedBoundaryOrderedHeartClass
                (completedBoundaryHilbertSource (convolutionAutocorrelation f))
            let hC :
                C ∈ autocorrelationConeSpectralEvalFiberOrderedHeartImage P f₀ :=
              ⟨f, hfFiber, Eq.refl C⟩
            ⟨C, hC, f, hfFiber, Eq.refl C, hrValue⟩))

/-- The representative-recognized ordered-heart zero-tail value set is the quotient-level
zero-tail value set on the positive/autocorrelation cone image. -/
theorem autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_to_quotient
    (S P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) (r : ℝ)
    (hr : r ∈ autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀) :
    r ∈ autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues S P f₀ :=
  match hr with
  | ⟨classValue, hClassEvidence, f, hfFiber, hClassEqualityEvidence, hrValue⟩ =>
      let Ctail : CompletedBoundaryZeroTailOrderedHeartClass :=
        completedBoundaryZeroTailOrderedHeartClass
          (completedBoundaryHilbertSource (convolutionAutocorrelation f))
      let hCtail :
          Ctail ∈ autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀ :=
        ⟨f, hfFiber, Eq.refl Ctail⟩
      let hvalue :
          r = completedBoundaryOrderedHeartZeroTailRealAbs S Ctail :=
        Eq.trans hrValue
          (Eq.trans
            (autocorrelationZeroTailRealAbs_eq_hilbertSourceZeroTailRealAbs S f)
            (completedBoundaryOrderedHeartZeroTailRealAbs_mk
              S
              (completedBoundaryHilbertSource (convolutionAutocorrelation f))).symm)
      ⟨Ctail, hCtail, hvalue⟩

/-- A quotient zero-tail value has a representative-recognized witness. -/
theorem autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_of_quotient
    (S P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) (r : ℝ)
    (hr : r ∈
      autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues S P f₀) :
    r ∈ autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀ :=
  match hr with
  | ⟨Ctail, hCtail, hrValue⟩ =>
      match hCtail with
      | ⟨f, hfFiber, hCtailEquality⟩ =>
          let C : CompletedBoundaryOrderedHeartClass :=
            completedBoundaryOrderedHeartClass
              (completedBoundaryHilbertSource (convolutionAutocorrelation f))
          let hC :
              C ∈ autocorrelationConeSpectralEvalFiberOrderedHeartImage P f₀ :=
            ⟨f, hfFiber, Eq.refl C⟩
          let hvalue : r = autocorrelationZeroTailRealAbs S f :=
            Eq.trans hrValue
              (Eq.trans
                (congrArg (completedBoundaryOrderedHeartZeroTailRealAbs S) hCtailEquality)
                (Eq.trans
                  (completedBoundaryOrderedHeartZeroTailRealAbs_mk
                    S
                    (completedBoundaryHilbertSource (convolutionAutocorrelation f)))
                  (autocorrelationZeroTailRealAbs_eq_hilbertSourceZeroTailRealAbs S f).symm))
          ⟨C, hC, f, hfFiber, Eq.refl C, hvalue⟩

theorem autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀ =
      autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues S P f₀ :=
  Set.ext (fun r =>
    Iff.intro
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_to_quotient
        S P f₀ r)
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_of_quotient
        S P f₀ r))


end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
