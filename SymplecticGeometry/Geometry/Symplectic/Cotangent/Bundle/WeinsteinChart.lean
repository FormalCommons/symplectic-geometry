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
public import TauCeti.Geometry.Manifold.VectorBundle.FiberScaling
import SymplecticGeometry.Geometry.Symplectic.Manifold.SymplecticMap
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.VectorBundlePoincare
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Graph
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
* `SymplecticGeometry.CotangentBundle.AgreesOnZeroSection.contMDiff`: a map that agrees with `ι`
  on the zero section is smooth, being `ι` composed with the zero section.
* `SymplecticGeometry.CotangentBundle.IsWeinsteinChart.exists_contMDiff_mextDeriv_ofFunction_eq`:
  if `θ` is a primitive of `σ` (`dθ = σ`) and `f^*θ = dh`, then `ι^*θ - λ`, for the Liouville form
  `λ`, has a smooth primitive on every set `W` that contains the zero section, has closure in `U`
  and is stable under fibre scaling by `t ∈ [0, 1]`. The form `ι^*θ - λ` is closed on `U`, as
  `ι^*σ = -ω = dλ`, and pulls back to `f^*θ = dh` along the zero section, where `λ` vanishes; the
  relative Poincaré lemma `TauCeti.exists_contMDiff_mextDeriv_ofFunction_eq_of_mextDerivₗ_eq_zero`
  then gives the primitive.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §3.4.
* [P. Seidel, *A long exact sequence for symplectic Floer cohomology*][Seidel2003], the paragraph
  before Proposition 1.11 (arXiv version 2).
* [A. Cannas da Silva, *Lectures on Symplectic Geometry*][CannasdaSilva2001Lectures], §6.2.
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

/-- The zero section of `T*L`, as a map into the domain `U` of a map that agrees with `f` on it,
is smooth. -/
theorem AgreesOnZeroSection.contMDiff_zeroSection (hι : AgreesOnZeroSection f ι) :
    ContMDiff J (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (fun q ↦ (⟨_, (hι.exists_apply_eq q).1⟩ : U)) :=
  (ContMDiff.subtypeVal_comp_iff U _).1 (Bundle.contMDiff_zeroSection ℝ _)

/-- Composing `ι` with the zero section, as a map into `U`, gives `f`. -/
theorem AgreesOnZeroSection.subtypeVal_comp_comp_eq (hι : AgreesOnZeroSection f ι) :
    Subtype.val ∘ ι ∘ (fun q ↦ (⟨_, (hι.exists_apply_eq q).1⟩ : U)) = f :=
  funext fun q ↦ (hι.exists_apply_eq q).2

/-- A map that agrees on the zero section with a diffeomorphism `ι` from an open set of `T*L` is
smooth. -/
theorem AgreesOnZeroSection.contMDiff (hι : AgreesOnZeroSection f ι) : ContMDiff J I ∞ f :=
  hι.subtypeVal_comp_comp_eq ▸
    contMDiff_subtypeVal.comp (ι.contMDiff.comp hι.contMDiff_zeroSection)

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

/-- **A primitive of `ι^*θ - λ` near the zero section.** Let `ι : U ≃ V` be a Weinstein chart of
`f : L → M` for `σ`, on a finite-dimensional Hausdorff σ-compact manifold `L`. Let `θ` be a
one-form on `M` with `dθ = σ` whose pullback along `f` is `dh` for a smooth function `h` on `L`,
and let `λ` be the Liouville form of `T*L`. For every set `W` of `T*L` that contains the zero
section, has closure in `U` and is mapped into itself by the fibre scaling by each `t ∈ [0, 1]`,
there is a smooth function `g` on `T*L` with `dg = ι^*θ - λ` at each point of `W`. -/
theorem IsWeinsteinChart.exists_contMDiff_mextDeriv_ofFunction_eq [FiniteDimensional ℝ E]
    [T2Space L] [SigmaCompactSpace L] {σ : SmoothTwoForm I M} {f : L → M}
    {ι : U ≃ₘ⟮J.prod 𝓘(ℝ, E →L[ℝ] ℝ), I⟯ V} (hι : IsWeinsteinChart σ f ι)
    {θ : SmoothForm I M ℝ 1} (hθ : mextDerivₗ I 1 θ = σ) {h : L → ℝ}
    (hh : ContMDiff J 𝓘(ℝ) ∞ h) (hθh : mpullback J I f θ.val = mextDeriv (RoughForm.ofFunction J h))
    {W : Set (CotangentBundle J L)}
    (hW : ∀ z ∈ W, ∀ t, vectorBundleFiberScaling (E →L[ℝ] ℝ)
      (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) (z, t) ∈ W)
    (hWU : closure W ⊆ U) (h0 : ∀ q, zeroSection (E →L[ℝ] ℝ)
      (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) q ∈ W) :
    ∃ g : CotangentBundle J L → ℝ, ContMDiff (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞ g ∧
      ∀ z (hz : z ∈ W), mextDeriv (RoughForm.ofFunction (J.prod 𝓘(ℝ, E →L[ℝ] ℝ)) g) z =
        (SmoothForm.mpullback ι ι.contMDiff
            (SmoothForm.mpullback Subtype.val contMDiff_subtypeVal θ) -
          SmoothForm.mpullback Subtype.val contMDiff_subtypeVal (liouvilleForm J L)).val
          ⟨z, hWU (subset_closure hz)⟩ := by
  refine exists_contMDiff_mextDeriv_ofFunction_eq_of_mextDerivₗ_eq_zero hW hWU h0 ?_ hh ?_
  · -- `d (ι^*θ - λ) = ι^*σ - dλ = ι^*σ + ω`, which vanishes as `ι` is a Weinstein chart.
    have hs := SmoothTwoForm.isSymplectomorphism_iff_mpullback_eq.1 hι.isSymplectomorphism
    rw [map_sub, SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback,
      SmoothForm.mextDerivₗ_mpullback, hθ, hs, symplecticForm_eq_neg_mextDerivₗ, neg_neg, sub_self]
  · -- Along the zero section, `ι^*θ` pulls back to `f^*θ = dh` and `λ` to `0`.
    rw [← SmoothForm.coe_mpullback _ hι.contMDiff_zeroSection, map_sub,
      SmoothForm.mpullback_mpullback, SmoothForm.mpullback_mpullback,
      SmoothForm.mpullback_mpullback, Submodule.coe_sub, SmoothForm.coe_mpullback,
      SmoothForm.coe_mpullback, hι.subtypeVal_comp_comp_eq, hθh]
    -- The zero section, as a map into `U`, followed by the inclusion of `U` is the zero section.
    have hzs : (Subtype.val ∘ fun q ↦ (⟨_, (hι.exists_apply_eq q).1⟩ : U)) =
        zeroSection (E →L[ℝ] ℝ) (fun x : L ↦ TangentSpace J x →L[ℝ] ℝ) := rfl
    have hzero := (isExactLagrangianMap_zeroSection (I := J) (M := L)).mpullback_eq
    rw [mextDeriv_ofFunction_zero] at hzero
    rw [hzs]
    exact sub_eq_self.2 hzero

end Weinstein

end SymplecticGeometry.CotangentBundle

end
