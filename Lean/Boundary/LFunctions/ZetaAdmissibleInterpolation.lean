import Boundary.LFunctions.ZetaAdmissibleProbe
import Boundary.LFunctions.ZetaAdmissibleTransform
import Boundary.LFunctions.ZetaAdmissibleFiniteInterpolation
import Boundary.LFunctions.ZetaAdmissibleSpectralModel

/-!
# Boundary admissible interpolation

This file names the admissible-side interpolation surface available at the
moment: the explicit-formula transform and the separating probe.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The admissible spectral model is the explicit-formula transform. -/
abbrev spectralModel (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.explicitFormulaLinearDefectPackage :=
  toZetaExplicitFormulaLinearTransform f

/-- The admissible interpolation surface is the pair of spectral model and probe. -/
def interpolationSurface (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.explicitFormulaLinearDefectPackage × ZetaTestFunction :=
  (spectralModel f, separatingProbe f)

/-- The interpolation surface is the spectral transform together with the
separating probe. -/
theorem interpolationSurface_eq_spectralModel_separatingProbe (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The interpolation surface has the admissible spectral model as first component. -/
theorem interpolationSurface_fst (f : ZetaAdmissibleFunction) :
    (interpolationSurface f).1 = spectralModel f := by
  rfl

/-- The interpolation surface has the admissible probe as second component. -/
theorem interpolationSurface_snd (f : ZetaAdmissibleFunction) :
    (interpolationSurface f).2 = separatingProbe f := by
  rfl

/-- The interpolation surface is built from the spectral model and probe. -/
theorem interpolationSurface_eq (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The admissible interpolation surface is the spectral model/probe pair. -/
theorem interpolationSurface_pair (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The admissible interpolation surface is exactly the model/probe pair. -/
theorem interpolationSurface_components (f : ZetaAdmissibleFunction) :
    interpolationSurface f = (spectralModel f, separatingProbe f) := by
  rfl

/-- The spectral-model component of a finite sum is the finite sum of spectral models. -/
theorem interpolationSurface_fst_sum {α : Type*} (s : Finset α) (f : α → ZetaAdmissibleFunction) :
    (interpolationSurface (∑ a in s, f a)).1 = ∑ a in s, spectralModel (f a) := by
  rw [interpolationSurface_fst, toZetaExplicitFormulaLinearTransform_sum]

/-- A finite sample can be realized by an admissible interpolation surface with compact support. -/
theorem exists_interpolationSurface_eval_sample_with_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ i, f (S.x i) = a i) ∧
      HasCompactSupport f ∧
      (interpolationSurface f).1 = spectralModel f ∧
      (interpolationSurface f).2 = separatingProbe f := by
  rcases exists_admissible_eval_sample_with_support S a with ⟨f, hf, hfc⟩
  exact ⟨f, hf, hfc, interpolationSurface_fst f, interpolationSurface_snd f⟩

/-- A finite sample can be realized by an interpolation surface whose delta basis has controlled
support. -/
theorem exists_interpolationSurface_eval_sample_with_basis_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, HasCompactSupport (F i)) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (S.x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Set.iUnion fun i => Function.support (F i) ∧
        (interpolationSurface f).1 = spectralModel f ∧
        (interpolationSurface f).2 = separatingProbe f := by
  rcases exists_admissible_eval_sample_with_basis_support S a with
    ⟨F, hF1, hF0, hFc, f, hf, hfc, hfs⟩
  exact ⟨F, hF1, hF0, hFc, f, hf, hfc, hfs,
    interpolationSurface_fst f, interpolationSurface_snd f⟩

/-- A finite sample can be realized by an interpolation surface whose delta basis is controlled by
closed balls. -/
theorem exists_interpolationSurface_eval_sample_with_basis_closedBall_support
    (S : ZetaAdmissibleFunction.FiniteSample) (a : Fin S.n → ℂ) :
    ∃ F : ∀ _i, ZetaAdmissibleFunction,
      (∀ i, F i (S.x i) = (1 : ℂ)) ∧
      (∀ i j, j ≠ i → F i (S.x j) = 0) ∧
      (∀ i, ∃ rOut : ℝ, 0 < rOut ∧
        Function.support (F i) ⊆ Metric.closedBall (S.x i) rOut) ∧
      ∃ f : ZetaAdmissibleFunction,
        (∀ i, f (S.x i) = a i) ∧
        HasCompactSupport f ∧
        Function.support f ⊆ Set.iUnion fun i => Function.support (F i) ∧
        (interpolationSurface f).1 = spectralModel f ∧
        (interpolationSurface f).2 = separatingProbe f := by
  rcases exists_admissible_eval_sample_with_basis_closedBall_support S a with
    ⟨F, hF1, hF0, hFr, f, hf, hfc, hfs⟩
  exact ⟨F, hF1, hF0, hFr, f, hf, hfc, hfs,
    interpolationSurface_fst f, interpolationSurface_snd f⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
