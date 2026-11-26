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
public import SymplecticGeometry.Topology.VectorBundle.Orientation.Complex.LineBundle
public import SymplecticGeometry.Topology.VectorBundle.Section
public import TauCeti.Topology.VectorBundle.Hom
public import TauCeti.Topology.VectorBundle.Orientation.Complex.EulerClass
public import SymplecticGeometry.Topology.VectorBundle.Complex.RestrictScalars

/-!
# The argument principle on a split closed surface

Let `M` be a closed smooth surface with a homological orientation `oM`, and let `g : M → ℝ` be a
smooth function with regular value `0`. It splits `M` into `Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`,
which meet along the level set `C = g⁻¹(0)`. By `SymplecticGeometry.isCollared_inclusion_levelSet`,
`Σ₁` is a compact surface whose boundary `C` is collared, and its interior is the open set
`{g < 0}` (`SymplecticGeometry.range_inclusion_preimage_Iio`), oriented by the restriction of
`oM`: this is the setting of the boundary degree (`TauCeti.HomologicalOrientation.boundaryDegree`),
which on `Σ₁` is `TauCeti.HomologicalOrientation.sublevelBoundaryDegree`.

Let `L` be an oriented real plane bundle over `M`, `τ` a frame of `L` over `Σ₁` (linear
isomorphisms `τ x : L_x ≃ ℂ`, continuous on the total space, carrying the orientation of `L` to
`Complex.orientation`), and `s` a nowhere-zero continuous section of `L` over `Σ₂`. Then the Euler
number of `L` is the boundary degree on `Σ₁` of `τ s / |τ s|` on `C`
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`).

For a complex line bundle `L`, with the orientation of a complex line, the frame may be replaced
by a nowhere-zero section `σ` over `Σ₁`: if `s = c • σ` on `C`, the Euler number of `L` is the
boundary degree of `c / |c|`
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_complexEulerClass_eq_boundaryDegree`). The
frame is `τ x = (c ↦ c • σ x)⁻¹`, continuous by `Continuous.smul_totalSpace_trivial`, which
carries the orientation of `L` to that of `ℂ` since it is complex-linear
(`TauCeti.VectorBundleOrientation.map_toSpanSingletonEquiv`).

For the trivial line bundle, whose Euler class vanishes (`TauCeti.complexEulerClass_trivial`), with
the section `1` over `Σ₁`, this says that a circle map on `C` that extends continuously over `Σ₂`
has boundary degree `0` on `Σ₁`
(`TauCeti.HomologicalOrientation.sublevelBoundaryDegree_eq_zero_of_extend_Ici`).

## Proof

Read in the frame, `s` is a nowhere-zero map `C → ℂ`. Extend it to `M` by Tietze's theorem, and
modify the extension away from `C` so that it has finitely many zeros, none of them on `C`
(`SymplecticGeometry.exists_eq_on_levelSet_finite_zeros`, in
`SymplecticGeometry/Geometry/Manifold/RegularValue/FiniteZeros.lean`: a smooth approximation minus
a small regular value given by Sard's theorem). Pulled back through the frame over `Σ₁` and glued
with `s` along `C`, this gives a continuous section `t` of `L` over `M` with finitely many zeros,
all in `{g < 0}` (`SymplecticGeometry.exists_section_eq_finite_setOfPred_eq_zero`).

Adding up the local indices of `t` at its zeros gives the Euler number
(`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`). The
argument principle on `Σ₁`
(`TauCeti.VectorBundleOrientation.sum_sectionIndex_eq_boundaryDegree`) identifies the sum of the
local indices of `t` restricted to `{g < 0}` with the boundary degree, and the local indices on
`{g < 0}` and on `M` agree
(`TauCeti.VectorBundleOrientation.sectionIndex_comap_eq_of_fiberwise`).

## Main results

* `SymplecticGeometry.exists_section_eq_finite_setOfPred_eq_zero`: on a compact manifold, a
  nowhere-zero section over `{g ≥ 0}` of a vector bundle of rank the dimension of the base extends,
  through a frame over `{g ≤ 0}`, to a section over `M` with finitely many zeros, all in `{g < 0}`.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_boundaryDegree`: the Euler
  number is the boundary degree of the section over `Σ₂` read in the frame over `Σ₁`.
* `TauCeti.VectorBundleOrientation.evalFundamentalClass_complexEulerClass_eq_boundaryDegree`: for a
  complex line bundle, the same with a nowhere-zero section over `Σ₁` in place of the frame.
* `TauCeti.HomologicalOrientation.sublevelBoundaryDegree_eq_zero_of_extend_Ici`: a circle map on `C`
  that extends continuously over `Σ₂` has boundary degree `0` on `Σ₁`.

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
theorem exists_section_eq_finite_setOfPred_eq_zero {V : Type*} [NormedAddCommGroup V]
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
  [IsManifold 𝓘(ℝ, E) ∞ M] {g : M → ℝ}

section Real

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {L : M → Type}
  [TopologicalSpace (TotalSpace F L)] [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle F L] [VectorBundle ℝ F L]

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
    {u : C(↥(SymplecticGeometry.sublevelBoundary hg.continuous), Circle)}
    (hu : ∀ z hz, (u z : ℂ) = ‖τ z (s ⟨z, hz⟩)‖⁻¹ • τ z (s ⟨z, hz⟩)) :
    (oM.evalFundamentalClass hn (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (oL.eulerClass hF)).down =
      oM.sublevelBoundaryDegree hn hg h0 u := by
  rw [HomologicalOrientation.sublevelBoundaryDegree_def]
  have := SymplecticGeometry.compactSpace_preimage_Iic hg.continuous
  have : FiniteDimensional ℝ F := Module.finite_of_finrank_eq_succ hF
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  -- A section `t` extending `s`, with finitely many zeros, all in `{g < 0}`.
  obtain ⟨t, ht, ht₂, hZ, hZneg⟩ :=
    SymplecticGeometry.exists_section_eq_finite_setOfPred_eq_zero
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
  refine Eq.trans ?_ (sum_sectionIndex_eq_boundaryDegree (oL.pullback i₁) hF
    (oM.comap (TopologicalSpace.Opens.isOpenEmbedding' _)) hn
    (SymplecticGeometry.isOpenEmbedding_inclusion_preimage_Iio hg.continuous)
    (SymplecticGeometry.range_inclusion_preimage_Iio hg.continuous)
    (SymplecticGeometry.isCollared_inclusion_levelSet hg h0) hτ hτo'
    (t := fun x ↦ t x) ht' (hZ.preimage Subtype.val_injective.injOn)
    (fun x hx ↦ ⟨⟨x, hZneg x hx⟩, rfl⟩) (u := u)
    (fun z ↦ by
      rw [ht₂ ⟨z, SymplecticGeometry.mem_preimage_Ici_of_mem_sublevelBoundary
        (hg := hg.continuous) z.property⟩]
      exact hu z _))
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

end Real

section Complex

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace ℂ G]
  [IsScalarTower ℝ ℂ G] [FiniteDimensional ℂ G]
  {L : M → Type} [TopologicalSpace (TotalSpace G L)] [∀ x, AddCommGroup (L x)]
  [∀ x, Module ℝ (L x)] [∀ x, Module ℂ (L x)] [∀ x, IsScalarTower ℝ ℂ (L x)]
  [∀ x, TopologicalSpace (L x)] [FiberBundle G L] [VectorBundle ℂ G L]

open scoped VectorBundle.ComplexToReal

/-- **The argument principle on a split closed surface, for a complex line bundle.** Let `M` be a
closed smooth surface oriented by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting
`M` into `Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. Let `L` be a complex line bundle over `M`, `σ` a
nowhere-zero continuous section of `L` over `Σ₁`, and `s` one over `Σ₂`. Let `c` be a function on
the boundary `Σ₁ ∖ {g < 0}` of `Σ₁` with `s = c • σ` there. Then the Euler number of `L`, for the
orientation of `L` as a complex line, is the boundary degree on `Σ₁`, whose interior `{g < 0}`
carries the orientation restricted from `oM`, of any continuous `u` from the boundary to the
circle equal to `c / |c|`. -/
theorem evalFundamentalClass_complexEulerClass_eq_boundaryDegree (hG : finrank ℂ G = 0 + 1)
    (oM : HomologicalOrientation M E 2) (hn : finrank ℝ E = 2)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g) (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) g 0)
    {σ : ∀ x : g ⁻¹' Iic 0, L x}
    (hσ : Continuous fun x : g ⁻¹' Iic 0 ↦ TotalSpace.mk' G (x : M) (σ x)) (hσ0 : ∀ x, σ x ≠ 0)
    {s : ∀ x : g ⁻¹' Ici 0, L x}
    (hs : Continuous fun x : g ⁻¹' Ici 0 ↦ TotalSpace.mk' G (x : M) (s x)) (hs0 : ∀ x, s x ≠ 0)
    {c : ↥(SymplecticGeometry.sublevelBoundary hg.continuous) → ℂ}
    (hsc : ∀ (z : ↥(SymplecticGeometry.sublevelBoundary hg.continuous))
      (hz : ((z : g ⁻¹' Iic 0) : M) ∈ g ⁻¹' Ici 0), s ⟨_, hz⟩ = c z • σ z)
    {u : C(↥(SymplecticGeometry.sublevelBoundary hg.continuous), Circle)}
    (hu : ∀ z, (u z : ℂ) = c z / ‖c z‖) :
    (oM.evalFundamentalClass hn (ModuleCat.of ℤ (ULift.{0} ℤ)) (ContinuousMap.id M)
      (complexEulerClass (r := 0) G L hG)).down =
      oM.sublevelBoundaryDegree hn hg h0 u := by
  have hG1 : finrank ℂ G = 1 := hG
  let i₁ : C(g ⁻¹' Iic 0, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  have hσ₁ : Continuous fun x : g ⁻¹' Iic 0 ↦ TotalSpace.mk' G (E := (⇑i₁) *ᵖ L) x (σ x) :=
    Pullback.continuous_iff.2 ⟨continuous_id, hσ⟩
  -- The frame `c ↦ c • σ x` of `L` over `{g ≤ 0}`, and its inverse `τ`.
  let Φ : ∀ x : g ⁻¹' Iic 0, ℂ ≃L[ℝ] L x := fun x ↦
    (VectorBundle.toSpanSingletonEquiv G hG1 (σ x) (hσ0 x)).restrictScalars' ℝ
  have hΦ : ∀ x c, Φ x c = c • σ x := fun x c ↦
    (congrFun (ContinuousLinearEquiv.coe_restrictScalars' ℝ _) c).trans
      (VectorBundle.toSpanSingletonEquiv_apply G hG1 _ _ c)
  have hΦc : Continuous fun v : TotalSpace ℂ (Bundle.Trivial (g ⁻¹' Iic 0) ℂ) ↦
      TotalSpace.mk' G (E := (⇑i₁) *ᵖ L) v.proj (Φ v.proj v.snd) := by
    simp only [hΦ]
    -- The frame lives over the base itself, so the base map is `id`.
    exact hσ₁.smul_totalSpace_trivial (f := id)
  have hτ := (continuous_snd.comp (Bundle.Trivial.isInducing_toProd _ ℂ).continuous).comp
    (TauCeti.continuous_bundle_symm (F₁ := ℂ) (E₁ := Bundle.Trivial (g ⁻¹' Iic 0) ℂ) (F₂ := G)
      (E₂ := (⇑i₁) *ᵖ L) Φ hΦc)
  have ho : ∀ x, Orientation.map (Fin 2) (Φ x).toLinearEquiv Complex.orientation =
      VectorBundleOrientation.reindex (finCongr (by rw [hG]))
        (VectorBundleOrientation.complex G L) x := fun x ↦
    map_toSpanSingletonEquiv hG1 (σ x) (hσ0 x)
  rw [complexEulerClass_def]
  refine evalFundamentalClass_eulerClass_eq_boundaryDegree _
    (by rw [finrank_real_eq_two_mul_finrank_complex, hG]) oM hn hg h0
    (τ := fun x ↦ (Φ x).symm) hτ (fun x ↦ ?_) hs hs0 fun z hz ↦ ?_
  · rw [ContinuousLinearEquiv.toLinearEquiv_symm, ← ho, ← Orientation.map_symm,
      Equiv.symm_apply_apply]
  · rw [hsc z hz, ← hΦ, ContinuousLinearEquiv.symm_apply_apply, hu, div_eq_inv_mul,
      Complex.real_smul, Complex.ofReal_inv]

end Complex

end TauCeti.VectorBundleOrientation

namespace TauCeti.HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {g : M → ℝ}

/-- **Circle maps defined on the other side have boundary degree `0`.** Let `M` be a closed
smooth surface oriented by `oM`, and `g : M → ℝ` smooth with regular value `0`, splitting `M` into
`Σ₁ = {g ≤ 0}` and `Σ₂ = {g ≥ 0}`. A continuous `u` from the boundary of `Σ₁` to the circle that
is the restriction of a continuous map `v : Σ₂ → S¹` has boundary degree `0` on `Σ₁`, whose
interior `{g < 0}` carries the orientation restricted from `oM`. -/
theorem sublevelBoundaryDegree_eq_zero_of_extend_Ici (oM : HomologicalOrientation M E 2)
    (hn : finrank ℝ E = 2) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g)
    (h0 : IsRegularValue 𝓘(ℝ, E) 𝓘(ℝ) g 0) (v : C(g ⁻¹' Ici 0, Circle))
    {u : C(↥(SymplecticGeometry.sublevelBoundary hg.continuous), Circle)}
    (hu : ∀ z, u z =
      v ⟨_, SymplecticGeometry.mem_preimage_Ici_of_mem_sublevelBoundary z.property⟩) :
    oM.sublevelBoundaryDegree hn hg h0 u = 0 := by
  -- The argument principle for the trivial line bundle, with the section `1` over `{g ≤ 0}` and
  -- the section `v` over `{g ≥ 0}`; the Euler class of the trivial bundle vanishes.
  have h := VectorBundleOrientation.evalFundamentalClass_complexEulerClass_eq_boundaryDegree
    (G := ℂ) (L := Bundle.Trivial M ℂ) (by simp) oM hn hg h0
    (σ := fun _ ↦ (1 : ℂ))
    ((Bundle.Trivial.homeomorphProd M ℂ).symm.continuous.comp
      (continuous_subtypeVal.prodMk continuous_const)) (fun _ ↦ one_ne_zero)
    (s := fun x ↦ (v x : ℂ))
    ((Bundle.Trivial.homeomorphProd M ℂ).symm.continuous.comp
      (continuous_subtypeVal.prodMk (continuous_subtypeVal.comp v.continuous)))
    (fun x ↦ Circle.coe_ne_zero _)
    (c := fun z ↦
      (v ⟨_, SymplecticGeometry.mem_preimage_Ici_of_mem_sublevelBoundary z.property⟩ : ℂ))
    (fun z hz ↦ by simp) (u := u) fun z ↦ by
      rw [Circle.norm_coe, Complex.ofReal_one, div_one, hu z]
  rw [complexEulerClass_trivial, map_zero] at h
  exact h.symm

end TauCeti.HomologicalOrientation

end
