import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.Presentation

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

def AutocorrelationSpectralEvalFiberFiniteWindowTailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T →
    ρ ∉ daggerClosedSpectralSampleFinset P) ∧
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        (∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0) →
          autocorrelationZeroTailRealAbs S f < ε

/-- Complex norm form of a finite completed-zero tomography window.

The window is explicitly a finite set of completed zeros outside the excluded finite set
`S`, disjoint from the dagger-closed fixed spectral constraints, and killing it forces
the completed zero-tail norm below the tolerance. -/
def AutocorrelationSpectralEvalFiberFiniteWindowNormTailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ) ∧
    (∀ ρ : ℂ, ρ ∈ T → ρ ∉ S) ∧
      (∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
              ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε

/-- The finite-window norm-tail package is exactly its four named fields. -/
theorem autocorrelationSpectralEvalFiberFiniteWindowNormTailControl.elim
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      AutocorrelationSpectralEvalFiberFiniteWindowNormTailControl S P f₀ ε T) :
    (∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ) ∧
      (∀ ρ : ℂ, ρ ∈ T → ρ ∉ S) ∧
        (∀ ρ : ℂ, ρ ∈ T →
          ρ ∉ daggerClosedSpectralSampleFinset P) ∧
          ∀ f : ZetaAdmissibleFunction,
            f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
              (∀ ρ : ℂ, ρ ∈ T →
                zetaSpectralEval (convolutionAutocorrelation f)
                  ρ = 0) →
                ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε :=
  hT

/-- Constructor for the finite-window norm-tail package from its named fields. -/
theorem autocorrelationSpectralEvalFiberFiniteWindowNormTailControl_intro
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hTzero : ∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ)
    (hTS : ∀ ρ : ℂ, ρ ∈ T → ρ ∉ S)
    (hTdagger :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    AutocorrelationSpectralEvalFiberFiniteWindowNormTailControl S P f₀ ε T :=
  ⟨hTzero, hTS, hTdagger, htail⟩

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
      ρ ∉ daggerClosedSpectralSampleFinset P) ∧
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε :=
  hT

/-- Constructor for the finite-window tail-control package from its two named fields. -/
theorem autocorrelationSpectralEvalFiberFiniteWindowTailControl_intro
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε) :
    AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T :=
  ⟨hT, htail⟩

/-- The canonical finite non-dagger completed-zero height window.

This is the explicit window suggested by the zero-counting owner: take completed zeros in
the centered-height ball of radius `R`, discard the excluded zeros `S`, discard zeros
whose centered sample is already in the dagger-closed finite fiber constraints, and view
the remaining completed-zero subtype values as complex zeros. -/
def autocorrelationSpectralEvalFiberNonDaggerHeightWindow
    (S : Finset ℂ)
    (P : Finset ℂ)
    (R : ℝ) :
    Finset ℂ :=
  (((finite_completedZerosInCenteredHeightBall R).toFinset.filter
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        (ρ : ℂ) ∉ S ∧
          (ρ : ℂ) ∉ daggerClosedSpectralSampleFinset P)).image
    (⟨(fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (ρ : ℂ)),
      Subtype.val_injective⟩ :
      {ρ : ℂ // ZetaCompletedZero ρ} ↪ ℂ))

theorem completedZerosInCenteredHeightBall_mono
    {R R' : ℝ}
    (hRR' : R ≤ R') :
    completedZerosInCenteredHeightBall R ⊆
      completedZerosInCenteredHeightBall R' :=
  fun ρ hρ => le_trans hρ hRR'

theorem autocorrelationSpectralEvalFiberNonDaggerHeightWindow_mono
    (S : Finset ℂ)
    (P : Finset ℂ)
    {R R' : ℝ}
    (hRR' : R ≤ R') :
    autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R ⊆
      autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R' :=
  fun ρ hρ =>
    match Finset.mem_image.mp hρ with
  | ⟨ρZero, hρZero, hρ_eq⟩ =>
      let hfilter :
          ρZero ∈ (finite_completedZerosInCenteredHeightBall R).toFinset ∧
            ((ρZero : ℂ) ∉ S ∧
              (ρZero : ℂ) ∉ daggerClosedSpectralSampleFinset P) :=
        Finset.mem_filter.mp hρZero
      let hheightR :
            ρZero ∈ completedZerosInCenteredHeightBall R :=
          (finite_completedZerosInCenteredHeightBall R).mem_toFinset.mp hfilter.1
      let hheight :
          ρZero ∈ completedZerosInCenteredHeightBall R' :=
        completedZerosInCenteredHeightBall_mono hRR' hheightR
      let hball :
          ρZero ∈ (finite_completedZerosInCenteredHeightBall R').toFinset :=
        (finite_completedZerosInCenteredHeightBall R').mem_toFinset.mpr hheight
      let hfilter' :
          ρZero ∈ (finite_completedZerosInCenteredHeightBall R').toFinset.filter
            (fun zero : {ρ : ℂ // ZetaCompletedZero ρ} =>
              (zero : ℂ) ∉ S ∧
                (zero : ℂ) ∉ daggerClosedSpectralSampleFinset P) :=
        Finset.mem_filter.mpr ⟨hball, hfilter.2⟩
      Finset.mem_image.mpr ⟨ρZero, hfilter', hρ_eq⟩

/-- Every zero in the canonical non-dagger height window is outside the dagger-closed
finite spectral constraints. -/
theorem autocorrelationSpectralEvalFiberNonDaggerHeightWindow_daggerDisjoint
    (S : Finset ℂ)
    (P : Finset ℂ)
    (R : ℝ) :
    ∀ ρ : ℂ, ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
      ρ ∉ daggerClosedSpectralSampleFinset P :=
  fun ρ hρ =>
    match Finset.mem_image.mp hρ with
  | ⟨ρZero, hρZero, hρ_eq⟩ =>
      let hfilter :
          (ρZero : ℂ) ∉ S ∧
            (ρZero : ℂ) ∉ daggerClosedSpectralSampleFinset P :=
        (Finset.mem_filter.mp hρZero).2
      Eq.subst
        (motive := fun z : ℂ =>
          z ∉ daggerClosedSpectralSampleFinset P)
        hρ_eq
        hfilter.2

/-- Membership in the canonical non-dagger height window comes from a completed zero in
the centered-height ball, outside the excluded finite zero set. -/
theorem autocorrelationSpectralEvalFiberNonDaggerHeightWindow_mem_data
    (S : Finset ℂ)
    (P : Finset ℂ)
    (R : ℝ)
    {ρ : ℂ}
    (hρ : ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R) :
    ∃ ρZero : {ρ : ℂ // ZetaCompletedZero ρ},
      ρ = (ρZero : ℂ) ∧
        ρZero ∈ completedZerosInCenteredHeightBall R ∧
          (ρZero : ℂ) ∉ S ∧
            (ρZero : ℂ) ∉ daggerClosedSpectralSampleFinset P :=
  match Finset.mem_image.mp hρ with
  | ⟨ρZero, hρZero, hρ_eq⟩ =>
      let hfilter :
          ρZero ∈ (finite_completedZerosInCenteredHeightBall R).toFinset ∧
            ((ρZero : ℂ) ∉ S ∧
              (ρZero : ℂ) ∉ daggerClosedSpectralSampleFinset P) :=
        Finset.mem_filter.mp hρZero
      let hheight :
          ρZero ∈ completedZerosInCenteredHeightBall R :=
        (finite_completedZerosInCenteredHeightBall R).mem_toFinset.mp hfilter.1
      ⟨ρZero, hρ_eq.symm, hheight, hfilter.2.1, hfilter.2.2⟩

/-- A finite set of completed zeros has a centered-height radius containing all of its
members. -/
theorem exists_centeredHeightBall_cover_finite_completedZeros
    (T : Finset ℂ)
    (hTzero : ∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ) :
    ∃ R : ℝ,
      ∀ ρ : ℂ, ∀ hρ : ρ ∈ T,
        zetaCompletedZeroCenteredHeight
          (⟨ρ, hTzero ρ hρ⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ≤ R :=
  let R : ℝ :=
    ∑ ρ in T.attach,
      zetaCompletedZeroCenteredHeight
        (⟨(ρ : ℂ), hTzero (ρ : ℂ) ρ.2⟩ :
          {ρ : ℂ // ZetaCompletedZero ρ})
  let hcover :
      ∀ ρ : ℂ, ∀ hρ : ρ ∈ T,
        zetaCompletedZeroCenteredHeight
          (⟨ρ, hTzero ρ hρ⟩ :
            {ρ : ℂ // ZetaCompletedZero ρ}) ≤ R :=
    fun ρ hρ =>
    let hnonneg :
        ∀ η : {η : ℂ // η ∈ T},
          η ∈ T.attach →
            0 ≤
              zetaCompletedZeroCenteredHeight
                (⟨(η : ℂ), hTzero (η : ℂ) η.2⟩ :
                  {ρ : ℂ // ZetaCompletedZero ρ}) :=
      fun η hηAttach =>
        le_trans zero_le_one
          (zetaCompletedZeroCenteredHeight_ge_one
            (⟨(η : ℂ), hTzero (η : ℂ) η.2⟩ :
              {ρ : ℂ // ZetaCompletedZero ρ}))
    let η : {η : ℂ // η ∈ T} := ⟨ρ, hρ⟩
    let ηZero : {η : ℂ // ZetaCompletedZero η} :=
      ⟨(η : ℂ), hTzero (η : ℂ) η.2⟩
    let ρZero : {η : ℂ // ZetaCompletedZero η} :=
      ⟨ρ, hTzero ρ hρ⟩
    let hterm_le :
        zetaCompletedZeroCenteredHeight ηZero ≤ R :=
      Finset.single_le_sum hnonneg
        (Finset.mem_attach T η)
    let hzero_eq : ηZero = ρZero :=
      Subtype.ext (Eq.refl ρ)
    Eq.subst
      (motive := fun zero : {η : ℂ // ZetaCompletedZero η} =>
        zetaCompletedZeroCenteredHeight zero ≤ R)
      hzero_eq
      hterm_le
  Exists.intro R hcover

/-- A finite dagger-disjoint completed-zero window outside `S` is contained in some
canonical non-dagger height window. -/
theorem exists_nonDaggerHeightWindow_cover_finite_completedZeros
    (S : Finset ℂ)
    (P : Finset ℂ)
    (T : Finset ℂ)
    (hTzero : ∀ ρ : ℂ, ρ ∈ T → ZetaCompletedZero ρ)
    (hTS : ∀ ρ : ℂ, ρ ∈ T → ρ ∉ S)
    (hTdagger :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∃ R : ℝ,
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R :=
  match exists_centeredHeightBall_cover_finite_completedZeros T hTzero with
  | ⟨R, hR⟩ =>
      let hcover :
          ∀ ρ : ℂ, ρ ∈ T →
            ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R :=
        fun ρ hρ =>
        let ρZero : {ρ : ℂ // ZetaCompletedZero ρ} :=
          ⟨ρ, hTzero ρ hρ⟩
        let hheight :
            ρZero ∈ completedZerosInCenteredHeightBall R :=
          hR ρ hρ
        let htoFinset :
            ρZero ∈ (finite_completedZerosInCenteredHeightBall R).toFinset :=
          (finite_completedZerosInCenteredHeightBall R).mem_toFinset.mpr hheight
        let hfilter :
            ρZero ∈
              (finite_completedZerosInCenteredHeightBall R).toFinset.filter
                (fun η : {ρ : ℂ // ZetaCompletedZero ρ} =>
                  (η : ℂ) ∉ S ∧
                    (η : ℂ) ∉
                      daggerClosedSpectralSampleFinset P) :=
          Finset.mem_filter.mpr
            ⟨htoFinset, hTS ρ hρ, hTdagger ρ hρ⟩
        Finset.mem_image.mpr
          ⟨ρZero, hfilter, Eq.refl (ρZero : ℂ)⟩
      ⟨R, hcover⟩

/-- The finite spectral sample used by the selected tomographic interpolant at height
`R`: the dagger-closed fixed-fiber constraints together with the centered samples of the
finite non-dagger completed-zero height window. -/
def autocorrelationSpectralEvalFiberFiniteTomographySampleSet
    (S : Finset ℂ)
    (P : Finset ℂ)
    (R : ℝ) :
    Finset ℂ :=
  daggerClosedSpectralSampleFinset P ∪
    autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R

/-- Every fixed finite tomography sample set has a Paley-Wiener cardinal family. -/
theorem exists_autocorrelationSpectralEvalFiberFiniteTomographyCardinalFamily
    (S : Finset ℂ)
    (P : Finset ℂ)
    (R : ℝ) :
    ∃ F : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction,
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0 :=
  exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener
    (autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R)

/-- The finite tomography target vector on the explicit finite sample set. -/
def autocorrelationSpectralEvalFiberFiniteTomographyTarget
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ) :
    autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R → ℂ :=
  fun z =>
    finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ (z : ℂ)

/-- The concrete finite tomographic interpolant built from a cardinal family.

For the finite tomography sample set `U`, the object is the explicit Paley-Wiener
linear combination
`∑ z : U, target z • F z`, where `F` is a cardinal family for `U`. -/
def autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction :=
  ∑ z : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
    autocorrelationSpectralEvalFiberFiniteTomographyTarget S P f₀ R z • F z

/-- The concrete finite tomographic cardinal interpolant realizes the finite annihilation
target on the whole finite tomography sample set. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_spec
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ z : ℂ,
      z ∈ autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        zetaSpectralEval
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F) z =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z :=
  fun z hz =>
  let U : Finset ℂ :=
    autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R
  let aU : U → ℂ :=
    autocorrelationSpectralEvalFiberFiniteTomographyTarget S P f₀ R
  let hsample :
      zetaLaplaceTransformFiniteSample U
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F) =
        aU :=
    zetaLaplaceTransformFiniteSample_linearCombination_cardinalFamily
      U aU F hF
  let hcoord :
      zetaLaplaceTransformFiniteSample U
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F) ⟨z, hz⟩ =
        aU ⟨z, hz⟩ :=
    congrFun hsample ⟨z, hz⟩
  let hspectralLaplace :
      zetaSpectralEval
        (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
          S P f₀ R F) z =
        Boundary.zetaLaplaceTransform
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F).toZetaTestFunction' z :=
    zetaSpectralEval_eq_laplace
      (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
        S P f₀ R F) z
  let hlaplaceSample :
      Boundary.zetaLaplaceTransform
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F).toZetaTestFunction' z =
        zetaLaplaceTransformFiniteSample U
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F) ⟨z, hz⟩ :=
    Eq.refl
      (Boundary.zetaLaplaceTransform
        (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
          S P f₀ R F).toZetaTestFunction' z)
  let htarget :
      aU ⟨z, hz⟩ =
        finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z :=
    Eq.refl (finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z)
  Eq.trans hspectralLaplace
    (Eq.trans hlaplaceSample (Eq.trans hcoord htarget))

/-- On dagger-closed finite fiber samples, the concrete finite tomographic cardinal
interpolant realizes the finite annihilation target. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_dagger_spec
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ z : ℂ,
      z ∈ daggerClosedSpectralSampleFinset P →
        zetaSpectralEval
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F) z =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z :=
  fun z hz =>
    autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_spec
      S P f₀ R F hF z
      (Finset.mem_union.mpr (Or.inl hz))

/-- The concrete finite tomographic cardinal interpolant belongs to the fixed finite
autocorrelation spectral fiber. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_mem_fiber
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant S P f₀ R F ∈
      AutocorrelationSpectralEvalFiberOf P f₀ :=
  mem_autocorrelationSpectralEvalFiberOf_of_seed_finiteAnnihilationTarget
    P f₀
    (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
      S P f₀ R F)
    (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_dagger_spec
      S P f₀ R F hF)

/-- The concrete finite tomographic cardinal interpolant kills the autocorrelation
spectral values on the finite non-dagger completed-zero height window. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_window_zero
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ ρ : ℂ,
      ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
        zetaSpectralEval
          (convolutionAutocorrelation
            (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
              S P f₀ R F))
          ρ = 0 :=
  fun ρ hρ =>
  let hcenter :
      zetaSpectralEval
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F)
          ρ =
        finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ ρ :=
    autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_spec
      S P f₀ R F hF ρ
      (Finset.mem_union.mpr (Or.inr hρ))
  let hseedZero :
      zetaSpectralEval
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F)
          ρ = 0 :=
    Eq.trans hcenter
      (finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_zero_of_not_mem_daggerClosed
        P f₀
        (autocorrelationSpectralEvalFiberNonDaggerHeightWindow_daggerDisjoint
          S P R ρ hρ))
  autocorrelationSpectralEval_eq_zero_of_seed_eval_eq_zero
    (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
      S P f₀ R F)
    ρ hseedZero

/-- If a finite completed-zero window is covered by the non-dagger height window, the
concrete finite tomographic cardinal interpolant kills that finite window. -/
theorem autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_zero_on_covered_window
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ)
    (T : Finset ℂ)
    (hTsub :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R)
    (F :
      autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R →
        ZetaAdmissibleFunction)
    (hF :
      ∀ z w : autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R,
        Boundary.zetaLaplaceTransform (F z).toZetaTestFunction' (w : ℂ) =
          if w = z then 1 else 0) :
    ∀ ρ : ℂ, ρ ∈ T →
      zetaSpectralEval
        (convolutionAutocorrelation
          (autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
            S P f₀ R F))
        ρ = 0 :=
  fun ρ hρT =>
    autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_window_zero
      S P f₀ R F hF ρ
      (hTsub ρ hρT)

/-- Constructive finite Paley-Wiener interpolation constructs the concrete finite
tomographic cardinal interpolant at height `R`.

The witness is not an opaque choice: after the constructive cardinal-family theorem
returns `F`, the interpolant is the explicit finite sum over that `F`. -/
theorem exists_autocorrelationSpectralEvalFiberFiniteTomographicInterpolant
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (R : ℝ) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        ∀ ρ : ℂ,
          ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0 :=
  match
      exists_zetaLaplaceTransformCardinalFamily_constructive_ownerPaleyWiener
        (autocorrelationSpectralEvalFiberFiniteTomographySampleSet S P R) with
  | ⟨F, hF⟩ =>
      ⟨autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant
          S P f₀ R F,
        autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_mem_fiber
          S P f₀ R F hF,
        autocorrelationSpectralEvalFiberFiniteTomographicCardinalInterpolant_window_zero
          S P f₀ R F hF⟩

/-- A fixed-fiber representative with small zero-tail norm and vanishing on the canonical
height window gives the existential height-window reconstruction package. -/
theorem autocorrelationSpectralEvalFiber_nonDaggerHeightWindow_normSmallRepresentative_exists_of_witness
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (R : ℝ)
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfWindow :
      ∀ ρ : ℂ,
        ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
          zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0)
    (hfNorm :
      ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    ∃ R : ℝ, ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        (∀ ρ : ℂ,
          ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
            zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0) ∧
          ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε :=
  ⟨R, f, hfFiber, hfWindow, hfNorm⟩

/-- A constructively returned finite tomographic interpolant with small completed
zero-tail norm supplies the existential height-window reconstruction package. -/
theorem autocorrelationSpectralEvalFiber_nonDaggerHeightWindow_normSmallRepresentative_exists_of_finiteTomographicWitness_norm
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (R : ℝ)
    (f : ZetaAdmissibleFunction)
    (hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀)
    (hfWindow :
      ∀ ρ : ℂ,
        ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
          zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0)
    (hNorm :
      ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε) :
    ∃ R : ℝ, ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        (∀ ρ : ℂ,
          ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) ∧
          ‖zetaZeroTail S (convolutionAutocorrelation f)‖ < ε :=
  autocorrelationSpectralEvalFiber_nonDaggerHeightWindow_normSmallRepresentative_exists_of_witness
    S P f₀ ε R f hfFiber hfWindow hNorm

/-- Tail forcing for a concrete non-dagger height window packages as finite-window
tail control. -/
theorem autocorrelationSpectralEvalFiberFiniteWindowTailControl_of_nonDaggerHeightWindowTailForcing
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (R : ℝ)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ,
            ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
              zetaSpectralEval (convolutionAutocorrelation f)
                ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε) :
    AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε
      (autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R) :=
  autocorrelationSpectralEvalFiberFiniteWindowTailControl_intro
    S P f₀ ε
    (autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R)
    (autocorrelationSpectralEvalFiberNonDaggerHeightWindow_daggerDisjoint
      S P R)
    htail

/-- Existence of a height radius with tail forcing gives the finite-window package
needed by interpolation. -/
theorem autocorrelationSpectralEvalFiber_finiteWindowTailControl_exists_of_nonDaggerHeightRadius
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hR :
      ∃ R : ℝ,
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ,
              ρ ∈ autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R →
                zetaSpectralEval (convolutionAutocorrelation f)
                  ρ = 0) →
              autocorrelationZeroTailRealAbs S f < ε) :
    ∃ T : Finset ℂ,
      AutocorrelationSpectralEvalFiberFiniteWindowTailControl S P f₀ ε T :=
  match hR with
  | ⟨R, htail⟩ =>
      ⟨autocorrelationSpectralEvalFiberNonDaggerHeightWindow S P R,
        autocorrelationSpectralEvalFiberFiniteWindowTailControl_of_nonDaggerHeightWindowTailForcing
          S P f₀ ε R htail⟩


end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
