import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissibleInterpolation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core

/-!
# Admissible spectral interpolation

This file owns finite interpolation for spectral evaluations of completed
autocorrelation probes.  It sits above the physical interpolation package and
the zero-side spectral-evaluation definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A finite spectral sample vector indexed by a finite sample set. -/
abbrev SpectralSampleVector
    (S : Finset ℂ) : Type :=
  S → ℂ

/-- Dagger reflection of a finite spectral sample set. -/
def daggerReflectedSpectralSampleFinset
    (S : Finset ℂ) : Finset ℂ :=
  S.image (fun z : ℂ => -star z)

/-- The spectral sample set enlarged by its dagger-reflected sample set. -/
def daggerClosedSpectralSampleFinset
    (S : Finset ℂ) : Finset ℂ :=
  S ∪ daggerReflectedSpectralSampleFinset S

/-- A sample belongs to its dagger-closed finite spectral sample set. -/
theorem mem_daggerClosedSpectralSampleFinset_self
    (S : Finset ℂ) (z : ℂ) (hz : z ∈ S) :
    z ∈ daggerClosedSpectralSampleFinset S := by
  exact Finset.mem_union.mpr (Or.inl hz)

/-- The dagger-reflection of a sample belongs to the dagger-closed finite spectral sample
set. -/
theorem mem_daggerClosedSpectralSampleFinset_reflection
    (S : Finset ℂ) (z : ℂ) (hz : z ∈ S) :
    -star z ∈ daggerClosedSpectralSampleFinset S := by
  exact Finset.mem_union.mpr
    (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))

/-- Dagger reflection is an involution on spectral coordinates. -/
theorem daggerReflection_involutive
    (z : ℂ) :
    -star (-star z) = z := by
  calc
    -star (-star z) = -(-star (star z)) :=
      congrArg Neg.neg (star_neg (star z))
    _ = star (star z) := neg_neg (star (star z))
    _ = z := star_star z

/-- A dagger-closed finite spectral sample set is closed under dagger reflection. -/
theorem mem_daggerClosedSpectralSampleFinset_reflection_of_mem
    (S : Finset ℂ) (z : ℂ)
    (hz : z ∈ daggerClosedSpectralSampleFinset S) :
    -star z ∈ daggerClosedSpectralSampleFinset S := by
  change z ∈ S ∪ daggerReflectedSpectralSampleFinset S at hz
  change -star z ∈ S ∪ daggerReflectedSpectralSampleFinset S
  match Finset.mem_union.mp hz with
  | Or.inl hzBase =>
      exact
        Finset.mem_union.mpr
          (Or.inr (Finset.mem_image.mpr ⟨z, hzBase, rfl⟩))
  | Or.inr hzReflected =>
      match Finset.mem_image.mp hzReflected with
      | ⟨w, hw, hwEq⟩ =>
          have hreflection : -star z = w :=
            calc
              -star z = -star (-star w) := congrArg (fun u : ℂ => -star u) hwEq.symm
              _ = w := daggerReflection_involutive w
          exact
            Eq.mp
              (congrArg
                (fun u : ℂ => u ∈ S ∪ daggerReflectedSpectralSampleFinset S)
                hreflection.symm)
              (Finset.mem_union.mpr (Or.inl hw))

/-- A point in the reflected image of the dagger closure already belongs to
the dagger closure. -/
theorem mem_daggerClosedSpectralSampleFinset_of_mem_reflected_daggerClosure
    (S : Finset ℂ) (z : ℂ)
    (hz :
      z ∈ daggerReflectedSpectralSampleFinset
        (daggerClosedSpectralSampleFinset S)) :
    z ∈ daggerClosedSpectralSampleFinset S :=
  match Finset.mem_image.mp hz with
  | ⟨w, hw, hwEq⟩ =>
      let hreflection : -star w = z := hwEq
      let hclosed :
          -star w ∈ daggerClosedSpectralSampleFinset S :=
        mem_daggerClosedSpectralSampleFinset_reflection_of_mem S w hw
      Eq.subst
        (motive := fun value : ℂ =>
          value ∈ daggerClosedSpectralSampleFinset S)
        hreflection
        hclosed

/-- The dagger closure is contained in its second dagger closure. -/
theorem daggerClosedSpectralSampleFinset_subset_secondClosure
    (S : Finset ℂ) (z : ℂ)
    (hz : z ∈ daggerClosedSpectralSampleFinset S) :
    z ∈ daggerClosedSpectralSampleFinset
      (daggerClosedSpectralSampleFinset S) :=
  mem_daggerClosedSpectralSampleFinset_self
    (daggerClosedSpectralSampleFinset S)
    z
    hz

/-- The second dagger closure is contained in the first dagger closure. -/
theorem daggerClosedSpectralSampleFinset_secondClosure_subset
    (S : Finset ℂ) (z : ℂ)
    (hz :
      z ∈ daggerClosedSpectralSampleFinset
        (daggerClosedSpectralSampleFinset S)) :
    z ∈ daggerClosedSpectralSampleFinset S :=
  match Finset.mem_union.mp hz with
  | Or.inl hzBase => hzBase
  | Or.inr hzReflected =>
      mem_daggerClosedSpectralSampleFinset_of_mem_reflected_daggerClosure
        S z hzReflected

/-- Closing a finite spectral sample set under dagger reflection is idempotent. -/
theorem daggerClosedSpectralSampleFinset_idempotent
    (S : Finset ℂ) :
    daggerClosedSpectralSampleFinset (daggerClosedSpectralSampleFinset S) =
      daggerClosedSpectralSampleFinset S :=
  Finset.ext
    (fun z : ℂ =>
      Iff.intro
        (fun hz =>
          daggerClosedSpectralSampleFinset_secondClosure_subset S z hz)
        (fun hz =>
          daggerClosedSpectralSampleFinset_subset_secondClosure S z hz))

/-- The completed zeros lying in the dagger closure of a finite spectral sample set. -/
def completedZeroDaggerClosureFinset
    (S : Finset ℂ) : Finset ℂ :=
  (daggerClosedSpectralSampleFinset S).filter ZetaCompletedZero

/-- Every member of the completed-zero dagger closure is a completed zero. -/
theorem completedZeroDaggerClosureFinset_mem_completedZero
    (S : Finset ℂ) (z : ℂ)
    (hz : z ∈ completedZeroDaggerClosureFinset S) :
    ZetaCompletedZero z := by
  exact (Finset.mem_filter.mp hz).2

/-- Every member of the completed-zero dagger closure lies in the dagger closure. -/
theorem mem_daggerClosedSpectralSampleFinset_of_mem_completedZeroDaggerClosureFinset
    (S : Finset ℂ) (z : ℂ)
    (hz : z ∈ completedZeroDaggerClosureFinset S) :
    z ∈ daggerClosedSpectralSampleFinset S := by
  exact (Finset.mem_filter.mp hz).1

/-- A completed zero outside the finite completed-zero dagger closure is disjoint from the
dagger closure itself. -/
theorem completedZero_not_mem_daggerClosedSpectralSampleFinset_of_not_mem_completedZeroDaggerClosure
    (S : Finset ℂ) (z : ℂ)
    (hz : ZetaCompletedZero z)
    (hnot : z ∉ completedZeroDaggerClosureFinset S) :
    z ∉ daggerClosedSpectralSampleFinset S := by
  intro hmem
  exact hnot (Finset.mem_filter.mpr ⟨hmem, hz⟩)

/-- Spectral evaluation commutes with finite sums of admissible probes. -/
theorem zetaSpectralEval_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (F : α → ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (∑ x in s, F x) z =
      ∑ x in s, zetaSpectralEval (F x) z := by
  have hforget :
      zetaSpectralTransform
          (∑ x in s, F x).toZetaTestFunction' z =
        zetaSpectralTransform
          (∑ x in s, (F x).toZetaTestFunction') z := by
    change
      Boundary.zetaLaplaceTransform
          (∑ x in s, F x).toZetaTestFunction' z =
        Boundary.zetaLaplaceTransform
          (∑ x in s, (F x).toZetaTestFunction') z
    exact congrFun
      (Boundary.zetaLaplaceTransform_congr
        (fun t : ℝ =>
          calc
            (∑ x in s, F x).toZetaTestFunction' t =
                (∑ x in s, F x) t := by
              rfl
            _ = ∑ x in s, F x t := by
              exact ZetaAdmissibleFunction.sum_apply s F t
            _ = (∑ x in s, (F x).toZetaTestFunction') t := by
              exact
                (Boundary.zetaLaplaceTransform_sum_apply
                  (s := s)
                  (f := fun x : α => (F x).toZetaTestFunction')
                  t).symm))
      z
  have hsum :
      zetaSpectralTransform
          (∑ x in s, (F x).toZetaTestFunction') z =
        ∑ x in s,
          zetaSpectralTransform (F x).toZetaTestFunction' z := by
    exact zetaSpectralTransform_sum
      s
      (fun x : α => (F x).toZetaTestFunction')
      z
      (fun x _hx => integrable_laplaceKernel_at (F x) z)
  exact hforget.trans hsum

/-- The finite seed spectral-evaluation vector of an admissible function. -/
def seedSpectralEvalFiniteSample
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) :
    SpectralSampleVector S :=
  fun z : S => zetaSpectralEval f (z : ℂ)

/-- The finite target vector induced by a function on the ambient spectral plane. -/
def seedSpectralEvalFiniteTarget
    (S : Finset ℂ) (a : ℂ → ℂ) :
    SpectralSampleVector S :=
  fun z : S => a (z : ℂ)

/-- A seed realizes a finite spectral sample vector. -/
def RealizesSeedSpectralSamples
    (f : ZetaAdmissibleFunction) (S : Finset ℂ)
    (aS : SpectralSampleVector S) : Prop :=
  seedSpectralEvalFiniteSample S f = aS

/-- A finite Laplace-transform sample equality gives the corresponding seed
spectral-evaluation sample equality. -/
theorem seedSpectralEvalFiniteSample_eq_of_zetaLaplaceTransformFiniteSample_eq
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) (aS : SpectralSampleVector S)
    (hf : zetaLaplaceTransformFiniteSample S f = aS) :
    seedSpectralEvalFiniteSample S f = aS :=
  funext
    (fun z : S =>
      calc
        seedSpectralEvalFiniteSample S f z =
            zetaSpectralEval f (z : ℂ) := by
          rfl
        _ = Boundary.zetaLaplaceTransform f.toZetaTestFunction' (z : ℂ) := by
          exact zetaSpectralEval_eq_laplace f (z : ℂ)
        _ = zetaLaplaceTransformFiniteSample S f z := by
          rfl
        _ = aS z := by
          exact congrFun hf z)

/-- Finite Paley-Wiener interpolation in realization-predicate form. -/
theorem exists_realizesSeedSpectralSamples_ownerPaleyWiener
    (S : Finset ℂ) (aS : SpectralSampleVector S) :
    ∃ f : ZetaAdmissibleFunction,
      RealizesSeedSpectralSamples f S aS :=
  match exists_zetaLaplaceTransformFiniteSample_eq_ownerPaleyWiener S aS with
  | ⟨f, hf⟩ =>
      Exists.intro f
        (seedSpectralEvalFiniteSample_eq_of_zetaLaplaceTransformFiniteSample_eq
          S f aS hf)

/-- Finite Paley-Wiener interpolation for seed spectral-evaluation vectors. -/
theorem exists_seedSpectralEvalFiniteSample_eq_ownerPaleyWiener
    (S : Finset ℂ) (aS : SpectralSampleVector S) :
    ∃ f : ZetaAdmissibleFunction,
      seedSpectralEvalFiniteSample S f = aS := by
  exact exists_realizesSeedSpectralSamples_ownerPaleyWiener S aS

/-- Finite Paley-Wiener interpolation says the finite seed spectral-sample map is
surjective. -/
theorem seedSpectralEvalFiniteSample_surjective_ownerPaleyWiener
    (S : Finset ℂ) :
    Function.Surjective (seedSpectralEvalFiniteSample S) := by
  exact fun aS : S → ℂ =>
    exists_seedSpectralEvalFiniteSample_eq_ownerPaleyWiener S aS

/-- Finite Paley-Wiener interpolation for seed spectral evaluations on a finite spectral
sample set.

This is the analytic spectral-interpolation owner input: admissible Paley-Wiener probes
can realize arbitrary prescribed values on a finite set of spectral parameters. -/
theorem exists_seed_spectralEval_sample_on_finset_ownerPaleyWiener
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S → zetaSpectralEval f z = a z := by
  rcases exists_seedSpectralEvalFiniteSample_eq_ownerPaleyWiener
      S (seedSpectralEvalFiniteTarget S a) with
    ⟨f, hf⟩
  exact ⟨f, fun z hz =>
    congrFun hf ⟨z, hz⟩⟩

/-- Finite Paley-Wiener interpolation for seed spectral evaluations on a finite spectral
sample set. -/
theorem exists_seed_spectralEval_sample_on_finset
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S → zetaSpectralEval f z = a z := by
  exact exists_seed_spectralEval_sample_on_finset_ownerPaleyWiener S a

/-- Finite Paley-Wiener interpolation at the unit value on a finite spectral sample set. -/
theorem exists_seed_spectralEval_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S → zetaSpectralEval f z = 1 := by
  exact exists_seed_spectralEval_sample_on_finset
    S (fun _z : ℂ => 1)

/-- Spectral evaluation of a completed convolution-autocorrelation probe factors through the
seed transform and its dagger-reflected transform. -/
theorem zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (convolutionAutocorrelation f) z =
      zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) := by
  change
    Boundary.zetaLaplaceTransform
        (convolutionAutocorrelation f).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z *
        star (Boundary.zetaLaplaceTransform f.toZetaTestFunction' (-star z))
  exact Boundary.zetaLaplaceTransform_convolutionAutocorrelation f z

/-- A finite set of spectral points admits a seed whose spectral transform is `1` both on
the sample set and on its dagger-reflected sample set.

This is the genuine finite Paley-Wiener interpolation input for the unit autocorrelation
probe.  The autocorrelation statement below is only algebra after this seed-level theorem. -/
theorem exists_seed_spectralEval_one_on_finset_and_reflection
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ z : ℂ, z ∈ S → zetaSpectralEval f z = 1) ∧
        (∀ z : ℂ, z ∈ S → zetaSpectralEval f (-star z) = 1) := by
  rcases exists_seed_spectralEval_one_on_finset
      (daggerClosedSpectralSampleFinset S) with
    ⟨f, hf⟩
  exact ⟨f,
    fun z hz => hf z (mem_daggerClosedSpectralSampleFinset_self S z hz),
    fun z hz => hf (-star z)
      (mem_daggerClosedSpectralSampleFinset_reflection S z hz)⟩

/-- Unit seed values at a sample and its dagger-reflected sample give a unit dagger product
at the original sample. -/
theorem zetaSpectralEval_daggerProduct_eq_one_of_seed_and_reflection_one
    (f : ZetaAdmissibleFunction) (z : ℂ)
    (hleft : zetaSpectralEval f z = 1)
    (hright : zetaSpectralEval f (-star z) = 1) :
    zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) = 1 := by
  calc
    zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) =
        1 * star (zetaSpectralEval f (-star z)) := by
      exact congrArg
        (fun w : ℂ => w * star (zetaSpectralEval f (-star z)))
        hleft
    _ = 1 * star 1 := by
      exact congrArg
        (fun w : ℂ => 1 * star w)
        hright
    _ = 1 * 1 := by
      exact congrArg (fun w : ℂ => 1 * w) (star_one (R := ℂ))
    _ = 1 := by
      exact one_mul 1

/-- A finite set of spectral points admits a seed whose dagger-product spectral samples are
unit on that finite set. -/
theorem exists_seed_spectralEval_daggerProduct_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) = 1 := by
  rcases exists_seed_spectralEval_one_on_finset_and_reflection S with
    ⟨f, hleft, hright⟩
  exact ⟨f, fun z hz =>
    zetaSpectralEval_daggerProduct_eq_one_of_seed_and_reflection_one
      f z (hleft z hz) (hright z hz)⟩

/-- A finite set of spectral points admits a completed convolution-autocorrelation probe
with unit spectral samples on that finite set. -/
theorem exists_autocorrelation_spectralEval_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval (convolutionAutocorrelation f) z = 1 := by
  rcases exists_seed_spectralEval_daggerProduct_one_on_finset S with
    ⟨f, hf⟩
  exact ⟨f, fun z hz =>
    (zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
      f z).trans
      (hf z hz)⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
