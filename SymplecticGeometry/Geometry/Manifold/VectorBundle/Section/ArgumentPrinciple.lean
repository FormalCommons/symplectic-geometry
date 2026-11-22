/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import SymplecticGeometry.Geometry.Manifold.RegularValue.FiniteZeros
public import SymplecticGeometry.Geometry.Manifold.RegularValue.LevelCollar
public import SymplecticGeometry.Topology.Algebra.Module.Equiv.Basic
public import SymplecticGeometry.Topology.VectorBundle.Orientation.ArgumentPrinciple
public import TauCeti.Topology.VectorBundle.Hom

/-!
# The argument principle on a split closed surface

Let `M` be a closed smooth surface with a homological orientation `oM`, and let `g : M → ℝ` be a
smooth function with regular value `0`. It splits `M` into `Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`,
which meet along the level set `C = g⁻¹(0)`. By `SymplecticGeometry.isCollared_inclusion_levelSet`,
`Σ₁` is a compact surface whose boundary `C` is collared and whose interior is the open set
`{g < 0}`, oriented by the restriction of `oM`: this is the setting of the boundary degree
(`TauCeti.HomologicalOrientation.boundaryDegree`).

Let `L` be an oriented real plane bundle over `M`, `τ` a frame of `L` over `Σ₁` (linear
isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space, carrying the orientation of `L` to
`Complex.orientation`), and `s` a nowhere-zero continuous section of `L` over `Σ₂`. Then the Euler
number of `L` is the boundary degree on `Σ₁` of `τ s / |τ s|` on `C`
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`).

## Proof

Read in the frame, `s` is a nowhere-zero map `C → ℂ`. Extend it to `M` by Tietze's theorem, and
modify the extension away from `C` so that it has finitely many zeros, none of them on `C`
(`SymplecticGeometry.exists_eq_on_levelSet_finite_zeros`, in
`SymplecticGeometry/Geometry/Manifold/RegularValue/FiniteZeros.lean`: a smooth approximation minus
a small regular value given by Sard's theorem). Pulled back through the frame over `Σ₁` and glued
with `s` along `C`, this gives a continuous section `t` of `L` over `M` with finitely many zeros,
all in `{g < 0}` (`SymplecticGeometry.exists_section_eq_finite_setOf_eq_zero`).

Adding up the local indices of `t` at its zeros gives the Euler number
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`). The
argument principle on `Σ₁`
(`TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`) identifies the sum of the
local indices of `t` restricted to `{g < 0}` with the boundary degree, and the local indices on
`{g < 0}` and on `M` agree
(`TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`).

## Main results

* `SymplecticGeometry.exists_section_eq_finite_setOf_eq_zero`: on a compact manifold, a
  nowhere-zero section over `{g ≥ 0}` of a vector bundle of rank the dimension of the base extends,
  through a frame over `{g ≤ 0}`, to a section over `M` with finitely many zeros, all in `{g < 0}`.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`: the Euler
  number is the boundary degree of the section over `Σ₂` read in the frame over `Σ₁`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7: the
  first Chern number of a bundle over a closed surface computed from frames over the two sides of
  a splitting.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §11: the Euler class evaluated through the zeros of a section.
-/

public section

open Bundle Module Set Topology
open scoped Manifold ContDiff

namespace SymplecticGeometry

section Section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {L : M → Type*}
  [TopologicalSpace (TotalSpace F L)] [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle F L] [VectorBundle ℝ F L] {g : M → ℝ}

/-- On a compact smooth boundaryless manifold modelled on `E`, let `g : M → ℝ` be continuous, `τ`
a frame of a real vector bundle `L` over `{g ≤ 0}` (linear isomorphisms `τ x : L_x ≃ V`, where
`dim V = dim E`, continuous on the total space of the restriction of `L`), and `s` a nowhere-zero
continuous section of `L` over `{g ≥ 0}`. Then `s` extends to a continuous section of `L` over `M`
with finitely many zeros, all in `{g < 0}`. -/
theorem exists_section_eq_finite_setOf_eq_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hn : finrank ℝ E = finrank ℝ V) (hg : Continuous g)
    {τ : ∀ x : g ⁻¹' Iic 0, L x ≃L[ℝ] V}
    (hτ : Continuous fun v : TotalSpace F
      ((⇑(⟨Subtype.val, continuous_subtypeVal⟩ : C(g ⁻¹' Iic 0, M))) *ᵖ L) ↦ τ v.proj v.snd)
    {s : ∀ x : g ⁻¹' Ici 0, L x}
    (hs : Continuous fun x : g ⁻¹' Ici 0 ↦ TotalSpace.mk' F (x : M) (s x)) (hs0 : ∀ x, s x ≠ 0) :
    ∃ t : ∀ x, L x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      (∀ x : g ⁻¹' Ici 0, t x = s x) ∧ {x | t x = 0}.Finite ∧ ∀ x, t x = 0 → g x < 0 := by
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- `s` read in the frame `τ` on the level set `g⁻¹(0)`.
  have hc₀ : Continuous fun y : g ⁻¹' {0} ↦ TotalSpace.mk' F (E := (⇑i₁) *ᵖ L)
      (⟨y, (y.property : g y = 0).le⟩ : g ⁻¹' Iic 0) (s ⟨y, (y.property : g y = 0).ge⟩) :=
    Pullback.continuous_iff.2 ⟨continuous_subtypeVal.subtype_mk _,
      hs.comp (continuous_subtypeVal.subtype_mk _)⟩
  -- Extend it to `M` (Tietze), then change it off the level set to have finitely many zeros.
  obtain ⟨h₀, hh₀⟩ := (⟨_, hτ.comp hc₀⟩ : C(g ⁻¹' {0}, V)).exists_extension'
    (isClosed_singleton.preimage hg).isClosedEmbedding_subtypeVal
  have hh₀C (x : M) (hx : g x = 0) : h₀ x = τ ⟨x, hx.le⟩ (s ⟨x, hx.ge⟩) :=
    congrFun hh₀ ⟨x, hx⟩
  obtain ⟨h, hhC, hhfin, hhne⟩ := exists_eq_on_levelSet_finite_zeros hn hg h₀ fun x hx ↦ by
      rw [hh₀C x hx]
      exact fun h ↦ hs0 _ ((τ _).map_eq_zero_iff.1 h)
  -- The section: `τ⁻¹ h` on `{g ≤ 0}` and `s` on `{g > 0}`.
  let t : ∀ x, L x := fun x ↦
    if hx : g x ≤ 0 then (τ ⟨x, hx⟩).symm (h x) else s ⟨x, (not_le.1 hx).le⟩
  have ht₁ (x : g ⁻¹' Iic 0) : t x = (τ x).symm (h x) := dite_eq_left x.property
  have ht₂ (x : g ⁻¹' Ici 0) : t x = s x := by
    by_cases hx : g x ≤ 0
    · have hx0 : g x = 0 := le_antisymm hx x.property
      simp only [t, dite_eq_left hx, hhC x hx0, hh₀C x hx0]
      exact (τ _).symm_apply_apply _
    · exact dite_eq_right hx
  have hZt (x : M) : t x = 0 ↔ g x ≤ 0 ∧ h x = 0 := by
    by_cases hx : g x ≤ 0
    · rw [ht₁ ⟨x, hx⟩, (τ _).symm.map_eq_zero_iff]
      exact ⟨fun h0 ↦ ⟨hx, h0⟩, And.right⟩
    · rw [ht₂ ⟨x, (not_le.1 hx).le⟩]
      exact ⟨fun h0 ↦ absurd h0 (hs0 _), fun h0 ↦ absurd h0.1 hx⟩
  refine ⟨t, ?_, ht₂, hhfin.subset fun x hx ↦ ((hZt x).1 hx).2, fun x hx ↦
    lt_of_le_of_ne ((hZt x).1 hx).1 (hhne x ((hZt x).1 hx).2)⟩
  -- `τ⁻¹ h` is continuous on `{g ≤ 0}`, as the inverse of a frame is continuous.
  have hτ' : Continuous fun v : TotalSpace F ((⇑i₁) *ᵖ L) ↦
      TotalSpace.mk' V (E := Bundle.Trivial (g ⁻¹' Iic 0) V) v.proj (τ v.proj v.snd) :=
    (Bundle.Trivial.isInducing_toProd _ V).continuous_iff.2
      ((Pullback.continuous_proj F L i₁).prodMk hτ)
  have hh : Continuous fun x : g ⁻¹' Iic 0 ↦
      TotalSpace.mk' V (E := Bundle.Trivial (g ⁻¹' Iic 0) V) x (h x) :=
    (Bundle.Trivial.isInducing_toProd _ V).continuous_iff.2
      (continuous_id.prodMk (h.continuous.comp continuous_subtypeVal))
  have hτs : Continuous fun x : g ⁻¹' Iic 0 ↦
      TotalSpace.mk' F (E := (⇑i₁) *ᵖ L) x ((τ x).symm (h x)) :=
    (TauCeti.continuous_bundle_symm (F₁ := F) (E₁ := (⇑i₁) *ᵖ L) (F₂ := V)
      (E₂ := Bundle.Trivial (g ⁻¹' Iic 0) V) τ hτ').comp hh
  -- The section is continuous on the closed sets `{g ≤ 0}` and `{g ≥ 0}`, which cover `M`.
  refine continuousOn_univ.1 ?_
  rw [← show g ⁻¹' Iic 0 ∪ g ⁻¹' Ici 0 = univ from
    eq_univ_of_forall fun x ↦ (le_total (g x) 0).imp id id]
  refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_Iic.preimage hg)
    (isClosed_Ici.preimage hg) <;> rw [continuousOn_iff_continuous_domRestrict]
  · convert (Pullback.continuous_lift F L i₁).comp hτs using 1
    funext x
    simp only [domRestrict_apply, Function.comp_apply, ht₁ x, Pullback.lift_mk, i₁,
      ContinuousMap.coe_mk]
  · convert hs using 1
    funext x
    simp only [domRestrict_apply, ht₂ x]

end Section

end SymplecticGeometry

namespace TauCeti.VectorBundleOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : M → Type}
  [TopologicalSpace (TotalSpace F L)] [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle F L] [VectorBundle ℝ F L] {g : M → ℝ}

/-- **The argument principle on a split closed surface.** Let `M` be a closed smooth surface
oriented by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into
`Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. Let `L` be a real plane bundle over `M`, oriented by `oL`, `τ`
a frame of `L` over `Σ₁` (linear isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space, that
carry `oL` to `Complex.orientation`), and `s` a nowhere-zero continuous section of `L` over `Σ₂`.
Then the Euler number of `L` is the boundary degree on `Σ₁`, whose interior `{g < 0}` carries the
orientation restricted from `oM`, of any continuous `u` from the boundary `Σ₁ ∖ {g < 0}` of `Σ₁`
to the circle equal to `τ s / |τ s|` there. -/
theorem evalFundamentalClass_eulerClass_eq_boundaryDegree
    (oL : VectorBundleOrientation F L (Fin 2)) (hF : finrank ℝ F = 2)
    (oM : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) g 0)
    {τ : ∀ x : g ⁻¹' Iic 0, L x ≃L[ℝ] ℂ}
    (hτ : Continuous fun v : TotalSpace F
      ((⇑(⟨Subtype.val, continuous_subtypeVal⟩ : C(g ⁻¹' Iic 0, M))) *ᵖ L) ↦ τ v.proj v.snd)
    (hτo : ∀ x, Orientation.map (Fin 2) (τ x).toLinearEquiv (oL x) = Complex.orientation)
    {s : ∀ x : g ⁻¹' Ici 0, L x}
    (hs : Continuous fun x : g ⁻¹' Ici 0 ↦ TotalSpace.mk' F (x : M) (s x)) (hs0 : ∀ x, s x ≠ 0)
    {u : C(↥(range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
      TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self)))ᶜ, Circle)}
    (hu : ∀ z hz, (u z : ℂ) = ‖τ z (s ⟨z, hz⟩)‖⁻¹ • τ z (s ⟨z, hz⟩)) :
    haveI : CompactSpace (g ⁻¹' Iic 0) :=
      isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
    (oM.evalFundamentalClass hn (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (oL.eulerClass hF)).down =
      (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)).boundaryDegree hn
        (IsOpenEmbedding.inclusion _
          ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
        ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
        (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 u := by
  have : CompactSpace (g ⁻¹' Iic 0) :=
    isCompact_iff_compactSpace.1 (isClosed_Iic.preimage hg.continuous).isCompact
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- A section `t` extending `s`, with finitely many zeros, all in `{g < 0}`.
  obtain ⟨t, ht, ht₂, hZ, hZneg⟩ :=
    SymplecticGeometry.exists_section_eq_finite_setOf_eq_zero
      (hn.trans Complex.finrank_real_complex.symm) hg.continuous hτ hs hs0
  -- Adding up the local indices of `t` at its zeros gives the Euler number.
  rw [evalFundamentalClass_eulerClass_eq_sum_sectionIndex oL hF oM ht hn hZ]
  -- The argument principle on `{g ≤ 0}`, for the frame `τ` and the restriction of `t`.
  have hτo' (x : g ⁻¹' Iic 0) :
      Orientation.map (Fin 2) (τ x).toLinearEquiv ((oL.pullback i₁) x) = Complex.orientation := by
    rw [pullback_apply]
    exact hτo x
  have ht' : Continuous fun x : g ⁻¹' Iic 0 ↦ TotalSpace.mk' F (E := (⇑i₁) *ᵖ L) x (t x) :=
    Pullback.continuous_iff.2 ⟨continuous_id, ht.comp continuous_subtypeVal⟩
  -- A point of `{g ≤ 0}` off the interior `{g < 0}` lies in `{g ≥ 0}`.
  have hlt (x : g ⁻¹' Iic 0)
      (hx : x ∉ range (inclusion (s := ((⟨g ⁻¹' Iio 0, isOpen_Iio.preimage hg.continuous⟩ :
        TopologicalSpace.Opens M) : Set M)) (preimage_mono Iio_subset_Iic_self))) :
      (x : M) ∈ g ⁻¹' Ici 0 :=
    mem_preimage.2 (mem_Ici.2 (not_lt.1 fun h' ↦ hx ⟨⟨x, h'⟩, rfl⟩))
  refine Eq.trans ?_ (sum_sectionIndex_eq_boundaryDegree (oL.pullback i₁) hF
    (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)) hn
    (IsOpenEmbedding.inclusion _
      ((isOpen_Iio.preimage hg.continuous).preimage continuous_subtypeVal))
    ((range_inclusion _).trans (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).2.symm)
    (SymplecticGeometry.isCollared_inclusion_levelSet hg h0).1 hτ hτo'
    (t := fun x ↦ t x) ht' (hZ.preimage Subtype.val_injective.injOn)
    (fun x hx ↦ ⟨⟨x, hZneg x hx⟩, rfl⟩) (u := u)
    (fun z ↦ by rw [ht₂ ⟨z, hlt z z.property⟩]; exact hu z _))
  -- Each local index on `{g < 0}` is the local index on `M` at the same point.
  symm
  -- The zeros of `t` on `{g < 0}` are its zeros on `M`, read in the fibres of a pull-back: the
  -- membership is stated through `have` since `rw` does not see the two fibres as equal.
  refine Finset.sum_nbij (fun y ↦ (y : M))
    (fun y hy ↦ hZ.mem_toFinset.2 (by have := (Set.Finite.mem_toFinset _).1 hy; exact this))
    Subtype.val_injective.injOn (fun z hz ↦ ?_) (fun y _ ↦ ?_)
  · have hz' : t z = 0 := (Set.Finite.mem_toFinset _).1 hz
    exact ⟨⟨z, hZneg z hz'⟩, (Set.Finite.mem_toFinset _).2 hz', rfl⟩
  refine sectionIndex_comap_eq_of_fiberwise oL hF oM _ hF
    (j := ⟨Subtype.val, continuous_subtypeVal⟩) _
    (φ := fun x ↦ ContinuousLinearEquiv.refl ℝ (L x)) ?_ (fun x ↦ ?_) _ ht (fun _ ↦ rfl) y
  · exact (Pullback.continuous_lift F L i₁).comp (Pullback.continuous_lift F _ _)
  · rw [pullback_apply, pullback_apply, ContinuousLinearEquiv.toLinearEquiv_refl]
    exact Equiv.congr_fun (Orientation.map_refl _) _

end TauCeti.VectorBundleOrientation

end
