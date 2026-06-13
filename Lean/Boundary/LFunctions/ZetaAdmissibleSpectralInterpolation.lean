import Boundary.LFunctions.ZetaAdmissibleInterpolation
import Boundary.LFunctions.ZetaAdmissiblePaleyWiener
import Boundary.LFunctions.ZetaZeroSideDefinitions

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
  unfold daggerClosedSpectralSampleFinset
  exact Finset.mem_union.mpr (Or.inl hz)

/-- The dagger-reflection of a sample belongs to the dagger-closed finite spectral sample
set. -/
theorem mem_daggerClosedSpectralSampleFinset_reflection
    (S : Finset ℂ) (z : ℂ) (hz : z ∈ S) :
    -star z ∈ daggerClosedSpectralSampleFinset S := by
  unfold daggerClosedSpectralSampleFinset
  unfold daggerReflectedSpectralSampleFinset
  exact Finset.mem_union.mpr
    (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))

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

/-- Finite Paley-Wiener interpolation for seed spectral evaluations on a finite spectral
sample set.

This is the analytic spectral-interpolation owner input: admissible Paley-Wiener probes
can realize arbitrary prescribed values on a finite set of spectral parameters. -/
theorem exists_seed_spectralEval_sample_on_finset_ownerPaleyWiener
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S → zetaSpectralEval f z = a z := by
  sorry

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
      exact congrArg (fun w : ℂ => 1 * w) star_one
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
