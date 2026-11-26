/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Liouville
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.Diffeomorph.Cotangent
public import TauCeti.Geometry.Symplectic.Manifold.SymplecticMap
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Lift

/-!
# Weinstein charts of a map into a manifold with a two-form

Let `T*L = TauCeti.CotangentBundle J L` carry its canonical symplectic form `ω`
(`TauCeti.CotangentBundle.symplecticForm`), let `M` carry a two-form `σ`, and let `f : L → M`.
A neighbourhood of a Lagrangian embedding `f` is usually described by a diffeomorphism `ι` from
an open set `U` of `T*L` onto an open set `V` of `M` that is symplectic, here for the form `-ω`
(which is `dλ` for the Liouville form `λ`), and that restricts to `f` on the zero section. This
file names these two conditions together. The first is Tau Ceti's
`TauCeti.SmoothTwoForm.IsSymplectomorphism`, from the restriction of `-ω` to `U` to the
restriction of `σ` to `V`; theorems that need only it take that hypothesis.

## Main definitions

* `SymplecticGeometry.CotangentBundle.AgreesOnZeroSection f ι`: for each `q ∈ L`, the zero
  covector `0_q` lies in `U` and `ι 0_q = f q`.
* `SymplecticGeometry.CotangentBundle.IsWeinsteinChart σ f ι`: `ι` agrees with `f` on the zero
  section and is a symplectomorphism from the restriction of `-ω` to `U` to that of `σ` to `V`.

## Main results

* `SymplecticGeometry.CotangentBundle.AgreesOnZeroSection.cotangent_subtype_trans`: precomposing
  `ι` with the restriction of the cotangent lift of a diffeomorphism `a` of `L` gives a map that
  agrees with `f ∘ a` on the zero section.
* `SymplecticGeometry.CotangentBundle.IsWeinsteinChart.cotangent_subtype_trans`: the same
  precomposition gives a Weinstein chart of `f ∘ a`, as cotangent lifts preserve `ω` (Tau Ceti's
  `Diffeomorph.mpullback_cotangent_symplecticForm`).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
-/

public section

open Set Bundle TopologicalSpace TauCeti TauCeti.CotangentBundle
open scoped Manifold ContDiff

namespace SymplecticGeometry.CotangentBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {L : Type*} [TopologicalSpace L] [ChartedSpace H L]
  [IsManifold J ∞ L]
  {F HM : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ F HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {U U' : Opens (CotangentBundle J L)} {V : Opens M}

section ZeroSection

/-- A map `ι` from an open set `U` of `T*L` onto an open set `V` of `M` *agrees with `f : L → M`
on the zero section* if, for each `q ∈ L`, the zero covector `0_q` lies in `U` and `ι` sends it
to `f q`. -/
structure AgreesOnZeroSection (f : L → M) (ι : U ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V) : Prop where
  /-- Each zero covector `0_q` lies in `U`, and `ι` sends it to `f q`. -/
  exists_apply_eq : ∀ q, ∃ h : zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) q ∈ U,
    (ι ⟨_, h⟩ : M) = f q

variable {f : L → M} {ι : U ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V}

/-- The zero section lies in the domain of a map that agrees with `f` on it. -/
theorem AgreesOnZeroSection.range_zeroSection_subset (hι : AgreesOnZeroSection f ι) :
    range (zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ)) ⊆ U :=
  range_subset_iff.2 fun q ↦ (hι.exists_apply_eq q).1

/-- **Precomposing with a cotangent lift.** If `ι : U ≃ V` agrees with `f` on the zero section,
`a` is a diffeomorphism of `L` and the cotangent lift of `a` maps `U'` onto `U`, then `ι`
precomposed with the restriction of that lift to `U'` agrees with `f ∘ a` on the zero section. -/
theorem AgreesOnZeroSection.cotangent_subtype_trans (hι : AgreesOnZeroSection f ι)
    {a : L ≃ₘ⟮J, J⟯ L} (hUU' : ∀ z, z ∈ U' ↔ a.cotangent z ∈ U) :
    AgreesOnZeroSection (f ∘ a) ((a.cotangent.subtype hUU').trans ι) := by
  refine ⟨fun q ↦ ?_⟩
  obtain ⟨h, hq⟩ := hι.exists_apply_eq (a q)
  have hc := Diffeomorph.cotangent_zeroSection a q
  refine ⟨(hUU' _).2 (by rwa [hc]), ?_⟩
  rw [Diffeomorph.coe_trans, Function.comp_apply, Function.comp_apply, ← hq]
  exact congrArg (fun w ↦ (ι w : M)) (Subtype.ext ((a.cotangent.subtype_apply_coe hUU' _).trans hc))

end ZeroSection

section Weinstein

variable [IsManifold I ∞ M]

/-- A diffeomorphism `ι` from an open set `U` of `T*L` onto an open set `V` of `M` is a
*Weinstein chart* of `f : L → M` for a two-form `σ` on `M` if it sends the zero covector at each
`q ∈ L` to `f q` (`AgreesOnZeroSection`) and is a symplectomorphism from the restriction to `U`
of `-ω`, the opposite of the canonical symplectic form of `T*L`, to the restriction of `σ` to `V`.
As `ω = -dλ` for the Liouville form `λ`, the second condition says that `ι` is symplectic for the
form `dλ`. -/
structure IsWeinsteinChart (σ : SmoothTwoForm I M) (f : L → M)
    (ι : U ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V) : Prop extends AgreesOnZeroSection f ι where
  /-- `ι` is a symplectomorphism from the restriction of `-ω` to that of `σ`. -/
  isSymplectomorphism : SmoothTwoForm.IsSymplectomorphism
    (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (-symplecticForm J L))
    (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal σ) ι

/-- **Precomposing a Weinstein chart with a cotangent lift.** If `ι : U ≃ V` is a Weinstein chart
of `f`, `a` is a diffeomorphism of `L` and the cotangent lift of `a` maps `U'` onto `U`, then `ι`
precomposed with the restriction of that lift to `U'` is a Weinstein chart of `f ∘ a`. -/
theorem IsWeinsteinChart.cotangent_subtype_trans {σ : SmoothTwoForm I M} {f : L → M}
    {ι : U ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V} (hι : IsWeinsteinChart σ f ι) {a : L ≃ₘ⟮J, J⟯ L}
    (hUU' : ∀ z, z ∈ U' ↔ a.cotangent z ∈ U) :
    IsWeinsteinChart σ (f ∘ a) ((a.cotangent.subtype hUU').trans ι) where
  toAgreesOnZeroSection := hι.toAgreesOnZeroSection.cotangent_subtype_trans hUU'
  isSymplectomorphism :=
    ((SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.2 (by
      rw [map_neg, Diffeomorph.mpullback_cotangent_symplecticForm])).subtype hUU').trans
      hι.isSymplectomorphism (by simp)

end Weinstein

end SymplecticGeometry.CotangentBundle

end
