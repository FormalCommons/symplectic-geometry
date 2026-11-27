/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DeRham.Basic
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.RealChernClass
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Pullback
public import TauCeti.AlgebraicTopology.Singular.SurfaceGenus
public import TauCeti.Geometry.Symplectic.Manifold.Volume
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.Integration.Positivity
import SymplecticGeometry.Geometry.Manifold.VectorBundle.ChernNumber.Axioms
import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Classification
import SymplecticGeometry.Geometry.Symplectic.Manifold.Volume
import SymplecticGeometry.Geometry.Manifold.DeRham.Integration.Bijective

/-!
# Real first Chern classes of symplectic vector bundles

A nondegenerate smooth two-form `τ` on a smooth real vector bundle `V` tames smooth complex
structures, for instance the polar complex structure `h.polarComplexStructure g` of a bundle
metric `g`, and any two of them give isomorphic complex bundles
(`SymplecticGeometry.Bundle.ContMDiffTwoForm.Tames.exists_complex_bundleEquiv`). So all of them
have the same real first Chern class
`SymplecticGeometry.Bundle.ContMDiffComplexStructure.realFirstChernClass`, a class in de Rham
cohomology of the base. This file defines it as the real first Chern class of `τ`, the de Rham
counterpart of the integral class
`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernClass` and of the integral
`SymplecticGeometry.Bundle.symplecticChernNumber`.

## Main definitions

* `SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.realFirstChernClass G h`: the de
  Rham first Chern class of a vector bundle with a nondegenerate two-form, computed with the
  complex model `G`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass G h`: the de Rham first Chern class
  of a manifold with a nondegenerate two-form, that of the corresponding form on the tangent
  bundle.
* `Module.fact_finrank_fin_fun`: the instance `Fact (finrank R (Fin n → R) = m)` from
  `Fact (n = m)`, the rank hypothesis of the class for a bundle with model fibre `Fin n → ℝ`.

## Main results

* `ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_eq_of_tames`: every smooth complex
  structure tamed by `τ` has the real first Chern class of `τ`.
* `ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_pullback`: the class of the pull-back of
  `τ` along a smooth map `f` is the pull-back along `f` of the class of `τ`.
* `ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_pushforward`: an isomorphism of bundles
  that carries one form to another does not change the class.
* `ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_congr_model` and
  `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass_congr_model`: the class does not
  depend on the complex model `G`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass_eq_of_tames`: on a manifold, every
  smooth almost complex structure tamed by `σ` gives the class of `σ`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.realFirstChernClass_mpullback`: a smooth local
  diffeomorphism `φ` with `φ^* σ' = σ` carries the class of `σ'` to that of `σ`.
* `SymplecticGeometry.realFirstChernClass_tangent_eq_of_surface`: on a closed connected surface
  `S` of genus `g`, for a symplectic form `σ` whose orientation is `o`,
  `c₁(σ) = ((2 - 2 g) / ∫_S σ) • [σ]`.

## Proofs

For `realFirstChernClass_mpullback`, the derivatives of the local diffeomorphism `φ`, each a
linear isomorphism (`IsLocalDiffeomorph.mfderivToContinuousLinearEquiv`), form an isomorphism
from `TM` to the pull-back `φ *ᵖ TM'`, smooth on total spaces
(`Bundle.Pullback.contMDiff_totalSpace_mfderiv`), which carries the pull-back of the form of
`σ'` to the form of `σ` (`ContMDiffTwoForm.tangentEquiv_compMFDeriv_pullback`); so the result
follows from `realFirstChernClass_pushforward` and `realFirstChernClass_pullback`.

For the surface formula, integration on the top de Rham cohomology of a closed connected oriented
surface is injective (`TauCeti.deRhamCohomology.injective_integral`, from Tau Ceti's
`TauCeti.compactlySupportedDeRhamCohomology.injective_integral`). Both sides integrate
to `2 - 2 g`: the left side to the first Chern number of the tangent bundle
(`ContMDiffComplexStructure.integral_realFirstChernClass`), which is `2 - 2 g`
(`Bundle.symplecticChernNumber_tangent`), and the right side because the integral of `σ` is
positive for the orientation of `σ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7 and
  §6.2.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §14.
-/

public section

noncomputable section

open _root_.Bundle Module
open TauCeti (deRhamCohomology integralTopForm surfaceGenus SmoothTwoForm SmoothForm)
open scoped Manifold ContDiff

/-- The space `Fin n → R` has rank `m` whenever `n = m`, the equation given by a `Fact`. This
gives the rank hypothesis of the real first Chern class of a bundle with model fibre `Fin n → ℝ`
from one about `n` alone. -/
instance Module.fact_finrank_fin_fun {R : Type*} [Semiring R] [StrongRankCondition R] {n m : ℕ}
    [h : Fact (n = m)] : Fact (finrank R (Fin n → R) = m) :=
  ⟨(finrank_fin_fun R).trans h.out⟩

namespace SymplecticGeometry.Bundle.ContMDiffTwoForm

variable {EB HB M : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace HB M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)]

/-- The **real first Chern class** of a nondegenerate smooth two-form `τ` on a smooth real vector
bundle `V`, with complex model `G`: the real first Chern class of the complex bundle given by the
polar complex structure of `τ` for some bundle metric. Every smooth complex structure tamed by
`τ` gives this class (`IsNondegenerate.realFirstChernClass_eq_of_tames`). -/
def IsNondegenerate.realFirstChernClass {τ : ContMDiffTwoForm I ⊤ F V}
    (h : τ.IsNondegenerate) : deRhamCohomology I M 2 :=
  ContMDiffComplexStructure.realFirstChernClass G (h.polarComplexStructure
    (TauCeti.nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := F) (E := V)).some)

theorem IsNondegenerate.realFirstChernClass_def {τ : ContMDiffTwoForm I ⊤ F V}
    (h : τ.IsNondegenerate) :
    h.realFirstChernClass G = ContMDiffComplexStructure.realFirstChernClass G
      (h.polarComplexStructure
        (TauCeti.nonempty_contMDiffRiemannianMetric (IB := I) (n := ⊤) (F := F) (E := V)).some) :=
  (rfl)

/-- **The real first Chern class of a two-form is that of any tamed complex structure.** If a
nondegenerate two-form `τ` tames a smooth complex structure `J`, the real first Chern class of `τ`
is that of `J`. -/
theorem IsNondegenerate.realFirstChernClass_eq_of_tames {τ : ContMDiffTwoForm I ⊤ F V}
    (h : τ.IsNondegenerate) {J : ContMDiffComplexStructure I ⊤ F V} (hJ : τ.Tames J) :
    h.realFirstChernClass G = J.realFirstChernClass G := by
  rw [realFirstChernClass_def]
  obtain ⟨Ψ, hΨ, hΨJ⟩ := (h.compatible_polarComplexStructure _).tames.exists_complex_bundleEquiv hJ
  exact ContMDiffComplexStructure.realFirstChernClass_pushforward G G _ J Ψ hΨ hΨJ

section Pullback

variable {EN HN N : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {I' : ModelWithCorners ℝ EN HN} [I'.Boundaryless] [TopologicalSpace N]
  [ChartedSpace HN N] [IsManifold I' ∞ N] [T2Space N] [SigmaCompactSpace N]
  {K : Type*} [FunLike K N M] [ContinuousMapClass K N M]

/-- **The real first Chern class of a two-form is natural under pull-back.** For a nondegenerate
two-form `τ` on `V` and a smooth map `f : N → M`, the real first Chern class of the pull-back
`τ.pullback f hf`, a form on `f *ᵖ V`, is the pull-back along `f` of the real first Chern class
of `τ`. -/
theorem IsNondegenerate.realFirstChernClass_pullback {τ : ContMDiffTwoForm I ⊤ F V}
    (h : τ.IsNondegenerate) (f : K) (hf : ContMDiff I' I ∞ f) :
    haveI := Pullback.contMDiffVectorBundle (F := F) (E := V) hf
    (h.pullback f hf).realFirstChernClass G =
      deRhamCohomology.map f hf 2 (h.realFirstChernClass G) := by
  have := Pullback.contMDiffVectorBundle (F := F) (E := V) hf
  rw [realFirstChernClass_def G h, ← ContMDiffComplexStructure.realFirstChernClass_pullback]
  exact (h.pullback f hf).realFirstChernClass_eq_of_tames G
    ((h.compatible_polarComplexStructure _).tames.pullback f hf)

end Pullback

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)]
  [∀ x, TopologicalSpace (V' x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)] [TopologicalSpace (TotalSpace F' V')]
  [FiberBundle F' V'] [VectorBundle ℝ F' V'] [ContMDiffVectorBundle ∞ F' V' I]
  (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  [Fact (finrank ℝ F' = 2 * finrank ℂ G')]

/-- **A symplectic isomorphism of bundles does not change the real first Chern class.** If
fibrewise linear equivalences `Φ x : V x ≃ V' x`, smooth on total spaces, carry a nondegenerate
two-form `τ` to a nondegenerate two-form `τ'`, that is `τ' (Φ v, Φ w) = τ (v, w)`, then `τ` and
`τ'` have the same real first Chern class, each computed with its own complex model. -/
theorem IsNondegenerate.realFirstChernClass_pushforward {τ : ContMDiffTwoForm I ⊤ F V}
    {τ' : ContMDiffTwoForm I ⊤ F' V'} (h : τ.IsNondegenerate) (h' : τ'.IsNondegenerate)
    (Φ : ∀ x, V x ≃L[ℝ] V' x)
    (hΦ : ContMDiff (I.prod 𝓘(ℝ, F)) (I.prod 𝓘(ℝ, F')) ∞
      (fun p : TotalSpace F V ↦ TotalSpace.mk' F' p.proj (Φ p.proj p.snd)))
    (hΦτ : ∀ x v w, τ'.bilinFormAt x (Φ x v) (Φ x w) = τ.bilinFormAt x v w) :
    h'.realFirstChernClass G' = h.realFirstChernClass G := by
  obtain ⟨J, hJ⟩ := h.exists_compatible
  -- `τ'` tames the transport of `J` along `Φ`, which `Φ` intertwines with `J`.
  have ht : τ'.Tames (J.pushforward Φ hΦ) :=
    (pushforward_eq_iff Φ hΦ).2 hΦτ ▸ hJ.tames.pushforward Φ hΦ hΦ
  rw [h'.realFirstChernClass_eq_of_tames G' ht, h.realFirstChernClass_eq_of_tames G hJ.tames]
  exact (ContMDiffComplexStructure.realFirstChernClass_pushforward G G' J _ Φ hΦ
    fun x v ↦ by simp).symm

/-- **The real first Chern class of a two-form does not depend on the complex model** `G` used to
compute it. -/
theorem IsNondegenerate.realFirstChernClass_congr_model
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ F = 2 * finrank ℂ G')] {τ : ContMDiffTwoForm I ⊤ F V}
    (h : τ.IsNondegenerate) :
    h.realFirstChernClass G' = h.realFirstChernClass G :=
  h.realFirstChernClass_pushforward G G' h (fun x ↦ ContinuousLinearEquiv.refl ℝ (V x))
    contMDiff_id fun _ _ _ ↦ rfl

end SymplecticGeometry.Bundle.ContMDiffTwoForm

/-! ### The tangent bundle -/

namespace TauCeti.SmoothTwoForm

open SymplecticGeometry.Bundle

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)]

/-- The **real first Chern class** of a nondegenerate smooth two-form `σ` on a manifold `M`, with
complex model `G`: the real first Chern class of the corresponding two-form on the tangent
bundle. It is the real first Chern class of `(TM, J)` for every smooth almost complex structure
`J` tamed by `σ` (`IsNondegenerate.realFirstChernClass_eq_of_tames`). -/
def IsNondegenerate.realFirstChernClass {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) :
    deRhamCohomology I M 2 :=
  (ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 h).realFirstChernClass G

theorem IsNondegenerate.realFirstChernClass_def {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) :
    h.realFirstChernClass G =
      (ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 h).realFirstChernClass G :=
  (rfl)

/-- **Tamed almost complex structures compute the real first Chern class.** If a nondegenerate
two-form `σ` tames a smooth almost complex structure `J`, the real first Chern class of
`σ` is that of the complex tangent bundle `(TM, J)`. -/
theorem IsNondegenerate.realFirstChernClass_eq_of_tames {σ : SmoothTwoForm I M}
    (h : σ.IsNondegenerate) {J : SmoothAlmostComplexStructure I M} (hJ : σ.Tames J) :
    h.realFirstChernClass G = ContMDiffComplexStructure.realFirstChernClass G
      (ContMDiffComplexStructure.tangentEquiv.symm (J.toContMDiff ⊤)) := by
  exact ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_eq_of_tames G _
    (ContMDiffTwoForm.tames_tangentEquiv_symm_iff.2 hJ)

/-- **On a manifold, the real first Chern class of a nondegenerate `σ` does not depend on the
complex model** `G` used to compute it. -/
theorem IsNondegenerate.realFirstChernClass_congr_model
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ E = 2 * finrank ℂ G')] {σ : SmoothTwoForm I M} (h : σ.IsNondegenerate) :
    h.realFirstChernClass G' = h.realFirstChernClass G := by
  rw [realFirstChernClass_def, realFirstChernClass_def]
  exact ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_congr_model G G' _

variable {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless] [TopologicalSpace M']
  [ChartedSpace H' M'] [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M']
  (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
  [Fact (finrank ℝ E' = 2 * finrank ℂ G')]

/-- **Naturality of the real first Chern class under local diffeomorphisms.** If a smooth local
diffeomorphism `φ : M → M'`, such as a diffeomorphism or a smooth covering map, pulls a
nondegenerate two-form `σ'` on `M'` back to `σ`, then the real first Chern class of `σ` is the
pull-back along `φ` of that of `σ'`. -/
theorem IsNondegenerate.realFirstChernClass_mpullback {σ : SmoothTwoForm I M}
    {σ' : SmoothTwoForm I' M'} (h : σ.IsNondegenerate) (h' : σ'.IsNondegenerate)
    {φ : M → M'} (hφ : IsLocalDiffeomorph I I' ∞ φ)
    (hσ : SmoothForm.mpullback φ hφ.contMDiff σ' = σ) :
    h.realFirstChernClass G =
      deRhamCohomology.map φ hφ.contMDiff 2 (h'.realFirstChernClass G') := by
  -- The pull-back bundle `φ *ᵖ TM'` is defined for bundled continuous maps.
  obtain ⟨φ, rfl⟩ : ∃ f : C(M, M'), ⇑f = φ :=
    ⟨⟨φ, hφ.contMDiff.continuous⟩, ContinuousMap.coe_mk _ _⟩
  set τ' := ContMDiffTwoForm.tangentEquiv.symm σ'
  have hτ' : τ'.IsNondegenerate := ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 h'
  have := Pullback.contMDiffVectorBundle (F := E') (E := TangentSpace I' (M := M')) hφ.contMDiff
  -- The derivatives of `φ`, an isomorphism from `TM` to `φ *ᵖ TM'`, carry the pull-back of `τ'`
  -- to the form of `σ`.
  let Φ (x : M) : TangentSpace I x ≃L[ℝ] ((φ : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x :=
    hφ.mfderivToContinuousLinearEquiv (by simp) x
  have hcoe (x : M) (v : TangentSpace I x) : Φ x v = mfderiv I I' φ x v :=
    congr($(hφ.mfderivToContinuousLinearEquiv_coe (by simp) x) v)
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, E)) (I.prod 𝓘(ℝ, E')) ∞
      (fun p : TangentBundle I M ↦ TotalSpace.mk' E' p.proj (Φ p.proj p.snd)) :=
    (Pullback.contMDiff_totalSpace_mfderiv φ hφ.contMDiff).congr fun p ↦ by rw [hcoe]
  have hσ' : ContMDiffTwoForm.tangentEquiv.symm σ =
      (τ'.pullback φ hφ.contMDiff).compMFDeriv φ hφ.contMDiff := by
    rw [LinearEquiv.symm_apply_eq, ContMDiffTwoForm.tangentEquiv_compMFDeriv_pullback,
      LinearEquiv.apply_symm_apply, hσ]
  rw [IsNondegenerate.realFirstChernClass_def, IsNondegenerate.realFirstChernClass_def,
    ← ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_pullback G' hτ',
    ContMDiffTwoForm.IsNondegenerate.realFirstChernClass_pushforward G G'
      (ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 h) (hτ'.pullback _ _) Φ hΦ
      fun x v w ↦ by rw [hσ', ContMDiffTwoForm.bilinFormAt_compMFDeriv, hcoe, hcoe]]

end TauCeti.SmoothTwoForm

/-! ### Closed surfaces -/

namespace SymplecticGeometry

open SymplecticGeometry.Bundle

variable {S : Type} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S] [ConnectedSpace S]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * finrank ℂ G)]

/-- **The real first Chern class of a closed surface.** Let `S` be a compact connected Hausdorff
smooth surface of genus `g = TauCeti.surfaceGenus S` with an orientation `o`, and `σ` a symplectic
form on `S` whose symplectic orientation is `o`. Then the real first Chern class of `σ` is
`(2 - 2 g) / ∫_S σ` times the de Rham class of `σ`. -/
theorem realFirstChernClass_tangent_eq_of_surface
    (o : TauCeti.Manifold.Orientation (𝓡 2) S (Fin 2))
    {σ : SmoothTwoForm (𝓡 2) S} (hσ : σ.IsSymplectic)
    (ho : hσ.isNondegenerate.volumeOrientation (n := 1) finrank_euclideanSpace_fin = o) :
    hσ.isNondegenerate.realFirstChernClass G =
      ((2 - 2 * surfaceGenus S : ℝ) / integralTopForm o σ.val) •
        deRhamCohomology.mk (𝓡 2) 2 ⟨σ, hσ.isClosed.mem_closedForms⟩ := by
  have hpos : 0 < integralTopForm o σ.val := by
    have hp := hσ.isNondegenerate.isPositive_volumeForm (n := 1) finrank_euclideanSpace_fin
    rw [SmoothTwoForm.volumeForm_one, ho] at hp
    exact hp.integralTopForm_pos (σ.isSmoothForm.of_le bot_le)
      (isClosed_tsupport _).isCompact
  refine TauCeti.deRhamCohomology.injective_integral o ?_
  have hn := ContMDiffTwoForm.isNondegenerate_tangentEquiv_symm_iff.2 hσ.isNondegenerate
  obtain ⟨J, hJ⟩ := hn.exists_compatible
  rw [map_smul, deRhamCohomology.integral_mk, smul_eq_mul, div_mul_cancel₀ _ hpos.ne',
    SmoothTwoForm.IsNondegenerate.realFirstChernClass_def,
    hn.realFirstChernClass_eq_of_tames G hJ.tames,
    ContMDiffComplexStructure.integral_realFirstChernClass,
    ← symplecticChernNumber_eq_chernNumber _ _ G hJ.tames,
    symplecticChernNumber_tangent finrank_euclideanSpace_fin o G hσ.isNondegenerate ho]
  push_cast
  ring

end SymplecticGeometry

end
