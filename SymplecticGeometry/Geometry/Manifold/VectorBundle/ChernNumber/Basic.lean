/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Classification
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.FirstChernClass
public import SymplecticGeometry.Geometry.Manifold.VectorBundle.Symplectic.Pullback
public import SymplecticGeometry.Topology.VectorBundle.Complex.FirstChernClass
public import TauCeti.Geometry.Manifold.Degree.Homological

/-!
# First Chern numbers of symplectic bundles on surfaces

The first Chern number `chernNumber` of a complex vector bundle over a compact oriented surface
(`SymplecticGeometry/Topology/VectorBundle/Complex/FirstChernClass.lean`) is here related to smooth
data:

* `chernNumber_pullback_eq_degree_mul`: along a `C¹` map of closed oriented surfaces, the number
  of the pull-back is the mapping degree `TauCeti.degree` times the number;
* `symplecticChernNumber o hn G ω`: the first Chern number of a symplectic vector bundle `(V, ω)`,
  the number of the complex bundle `(V, J)` for a complex structure `J` tamed by `ω`;
* `symplecticChernNumber_eq_chernNumber`: every complex structure tamed by `ω`, in particular
  every compatible one, gives the same number;
* `symplecticChernNumber_congr_model`: the number does not depend on the complex model `G`;
* `symplecticChernNumber_neg`: `(V, -ω)` has the opposite number;
* `symplecticChernNumber_pullback` and `symplecticChernNumber_congr`: behaviour under pull-backs
  and invariance under isomorphisms of symplectic bundles.

## Implementation notes

The complex bundle of a continuous complex structure `J` needs a complex model `G`, with
`Fact (finrank ℝ F = 2 * finrank ℂ G)`; it is a parameter of `symplecticChernNumber`, on which the
number does not depend (`symplecticChernNumber_congr_model`). The number is defined
through a choice of a continuous complex structure tamed by `ω`, and is `0` if there is none; over
a Hausdorff σ-compact base every nondegenerate form tames some complex structure
(`SymplecticGeometry.Bundle.ContMDiffTwoForm.IsNondegenerate.exists_compatible`). Two tamed
complex structures give isomorphic complex bundles
(`SymplecticGeometry.Bundle.ContMDiffTwoForm.Tames.exists_complex_bundleEquiv`), so the choice does
not matter.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.7
  (Theorem 2.7.1).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14.
-/

public section

open Bundle Module TauCeti
open scoped Manifold

namespace SymplecticGeometry

namespace Bundle

/-! ### The smooth degree formula -/

section Degree

variable {M M' EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace M] [ChartedSpace EM M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, EM) 1 M]
  [TopologicalSpace M'] [ChartedSpace EM M'] [T2Space M'] [CompactSpace M']
  [IsManifold 𝓘(ℝ, EM) 1 M'] (hn : finrank ℝ EM = 2)
  (o : Manifold.Orientation 𝓘(ℝ, EM) M (Fin 2)) (o' : Manifold.Orientation 𝓘(ℝ, EM) M' (Fin 2))
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  (E : M → Type*) [∀ x, AddCommMonoid (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]

/-- **The degree formula for the first Chern number.** For a `C¹` map `φ : M' → M` of closed
oriented surfaces, `M` connected, and a complex vector bundle `E` over `M`, the first Chern number
of the pull-back `φ* E` is the mapping degree of `φ` (the signed count of the preimages of a
regular value) times the first Chern number of `E`. -/
theorem chernNumber_pullback_eq_degree_mul [PreconnectedSpace M] {φ : C(M', M)}
    (hφ : ContMDiff 𝓘(ℝ, EM) 𝓘(ℝ, EM) 1 φ) :
    chernNumber (o'.toHomologicalOrientation hn) hn G ((⇑φ) *ᵖ E) =
      degree o' o φ * chernNumber (o.toHomologicalOrientation hn) hn G E := by
  rw [chernNumber_pullback (o.toHomologicalOrientation hn) hn G E
      (o'.toHomologicalOrientation hn) hn,
    Manifold.Orientation.degree_toHomologicalOrientation_eq_degree hn o' o hφ
      φ.continuous.isProperMap]

end Degree

/-! ### The first Chern number of a symplectic vector bundle -/

section Symplectic

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [ChartedSpace EM M] (o : HomologicalOrientation M EM 2) (hn : finrank ℝ EM = 2)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ F = 2 * finrank ℂ G)] {n m : ℕ∞}

open Classical in
/-- The **first Chern number of a symplectic vector bundle** `(V, ω)` over a compact surface with
homological orientation `o`: the first Chern number of the complex vector bundle `(V, J)`, with
model `G`, for a continuous complex structure `J` tamed by `ω`, and `0` if there is none. By
`symplecticChernNumber_eq_chernNumber` every complex structure tamed by `ω` gives this value. -/
noncomputable def symplecticChernNumber (ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V) : ℤ :=
  if h : ∃ J : ContMDiffComplexStructure 𝓘(ℝ, EM) 0 F V, ω.Tames J then
    chernNumber o hn G h.choose.toContinuousComplexStructure.Fiber
  else 0

open Classical in
theorem symplecticChernNumber_def (ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V) :
    symplecticChernNumber o hn G ω =
      if h : ∃ J : ContMDiffComplexStructure 𝓘(ℝ, EM) 0 F V, ω.Tames J then
        chernNumber o hn G h.choose.toContinuousComplexStructure.Fiber
      else 0 := (rfl)

/-- Two complex structures tamed by the same form, of any regularities, give complex bundles with
the same first Chern number. -/
theorem ContMDiffTwoForm.Tames.chernNumber_eq {m' : ℕ∞}
    {ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V} {J : ContMDiffComplexStructure 𝓘(ℝ, EM) m F V}
    {J' : ContMDiffComplexStructure 𝓘(ℝ, EM) m' F V} (h : ω.Tames J) (h' : ω.Tames J') :
    chernNumber o hn G J'.toContinuousComplexStructure.Fiber =
      chernNumber o hn G J.toContinuousComplexStructure.Fiber := by
  rw [chernNumber_def, chernNumber_def, h.firstChernClass_eq G h']

/-- **The first Chern number of a symplectic bundle is that of any tamed complex structure.** If
`ω` tames a complex structure `J`, of any regularity, then the first Chern number of `(V, ω)` is
that of the complex bundle `(V, J)`. This applies in particular to a complex structure compatible
with `ω`. -/
theorem symplecticChernNumber_eq_chernNumber {ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V}
    {J : ContMDiffComplexStructure 𝓘(ℝ, EM) m F V} (h : ω.Tames J) :
    symplecticChernNumber o hn G ω = chernNumber o hn G J.toContinuousComplexStructure.Fiber := by
  have hex : ∃ J : ContMDiffComplexStructure 𝓘(ℝ, EM) 0 F V, ω.Tames J :=
    ⟨J.ofLE zero_le, (ContMDiffTwoForm.tames_ofLE_iff zero_le).2 h⟩
  rw [symplecticChernNumber_def, dite_eq_left_of_eq_true (eq_true hex)]
  exact h.chernNumber_eq o hn G hex.choose_spec

/-- **The first Chern number of a symplectic bundle does not depend on the complex model** `G`
of the complex bundles it is computed from. -/
theorem symplecticChernNumber_congr_model
    (G' : Type*) [NormedAddCommGroup G'] [NormedSpace ℂ G'] [FiniteDimensional ℂ G']
    [Fact (finrank ℝ F = 2 * finrank ℂ G')] (ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V) :
    symplecticChernNumber o hn G' ω = symplecticChernNumber o hn G ω := by
  by_cases hex : ∃ J : ContMDiffComplexStructure 𝓘(ℝ, EM) 0 F V, ω.Tames J
  · obtain ⟨J, hJ⟩ := hex
    rw [symplecticChernNumber_eq_chernNumber o hn G hJ,
      symplecticChernNumber_eq_chernNumber o hn G' hJ, chernNumber_def, chernNumber_def,
      J.toContinuousComplexStructure.firstChernClass_congr_model G G']
  · rw [symplecticChernNumber_def, symplecticChernNumber_def,
      dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex)]

/-- **Reversing the form negates the first Chern number**: `(V, -ω)` has the opposite number,
since `-ω` tames `-J` when `ω` tames `J`, and `(V, -J)` is the conjugate of `(V, J)`. -/
@[simp]
theorem symplecticChernNumber_neg (ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V) :
    symplecticChernNumber o hn G (-ω) = -symplecticChernNumber o hn G ω := by
  by_cases hex : ∃ J : ContMDiffComplexStructure 𝓘(ℝ, EM) 0 F V, ω.Tames J
  · obtain ⟨J, hJ⟩ := hex
    have hJ' : (-ω).Tames (-J) := ContMDiffTwoForm.neg_tames_neg_iff.2 hJ
    rw [symplecticChernNumber_eq_chernNumber o hn G hJ,
      symplecticChernNumber_eq_chernNumber o hn G hJ',
      chernNumber_def, chernNumber_def, J.firstChernClass_neg G, map_neg, ULift.neg_down]
  · have hex' : ¬∃ J : ContMDiffComplexStructure 𝓘(ℝ, EM) 0 F V, (-ω).Tames J := by
      rintro ⟨J, hJ⟩
      exact hex ⟨-J, ContMDiffTwoForm.neg_tames_neg_iff.1
        (by rwa [ContMDiffComplexStructure.neg_neg])⟩
    rw [symplecticChernNumber_def, symplecticChernNumber_def,
      dite_eq_right_of_eq_false (eq_false hex), dite_eq_right_of_eq_false (eq_false hex'),
      neg_zero]

variable [IsManifold 𝓘(ℝ, EM) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [ContMDiffVectorBundle n F V 𝓘(ℝ, EM)]

/-- **Invariance under isomorphisms of symplectic bundles.** If fibrewise linear equivalences
`Φ : V₁ ≃ V₂`, whose map of total spaces is `Cⁿ`, carry a nondegenerate form `ω₁` to `ω₂`, then
`(V₁, ω₁)` and `(V₂, ω₂)` have the same first Chern number; each may be computed with its own
complex model. -/
theorem symplecticChernNumber_congr
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {V₂ : M → Type*} [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
    [∀ x, TopologicalSpace (V₂ x)] [∀ x, IsTopologicalAddGroup (V₂ x)]
    [∀ x, ContinuousSMul ℝ (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
    [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
    (G₂ : Type*) [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    [Fact (finrank ℝ F₂ = 2 * finrank ℂ G₂)]
    {ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V} {ω₂ : ContMDiffTwoForm 𝓘(ℝ, EM) n F₂ V₂}
    (hω : ω.IsNondegenerate) (Φ : ∀ x, V x ≃L[ℝ] V₂ x)
    (hΦ : ContMDiff (𝓘(ℝ, EM).prod 𝓘(ℝ, F)) (𝓘(ℝ, EM).prod 𝓘(ℝ, F₂)) n
      (fun v : TotalSpace F V ↦ TotalSpace.mk' F₂ v.proj (Φ v.proj v.snd)))
    (hΦω : ∀ x v w, ω₂.bilinFormAt x (Φ x v) (Φ x w) = ω.bilinFormAt x v w) :
    symplecticChernNumber o hn G₂ ω₂ = symplecticChernNumber o hn G ω := by
  obtain ⟨J, hJ⟩ := hω.exists_compatible
  -- `ω₂` tames the transport of `J` along `Φ`, which `Φ` intertwines with `J`.
  have ht : ω₂.Tames (J.pushforward Φ hΦ) :=
    (ContMDiffTwoForm.pushforward_eq_iff Φ hΦ).2 hΦω ▸ hJ.tames.pushforward Φ hΦ hΦ
  rw [symplecticChernNumber_eq_chernNumber o hn G₂ ht,
    symplecticChernNumber_eq_chernNumber o hn G hJ.tames, chernNumber_def, chernNumber_def,
    J.firstChernClass_pushforward G G₂ Φ hΦ]

/-- **The first Chern number of a pull-back.** For a nondegenerate form `ω` on `V` over a
connected closed surface `M` and a `Cⁿ` map `f : M' → M` from a compact oriented surface, the
first Chern number of the pull-back `(f* V, f* ω)` is the degree of `f` times the first Chern
number of `(V, ω)`. -/
theorem symplecticChernNumber_pullback [PreconnectedSpace M]
    {M' : Type} [TopologicalSpace M'] [T2Space M'] [CompactSpace M']
    {EM' : Type} [NormedAddCommGroup EM'] [NormedSpace ℝ EM'] [FiniteDimensional ℝ EM']
    [ChartedSpace EM' M'] (o' : HomologicalOrientation M' EM' 2) (hn' : finrank ℝ EM' = 2)
    {ω : ContMDiffTwoForm 𝓘(ℝ, EM) n F V} (hω : ω.IsNondegenerate)
    (f : C^n⟮𝓘(ℝ, EM'), M'; 𝓘(ℝ, EM), M⟯) :
    symplecticChernNumber o' hn' G (ω.pullback f f.contMDiff) =
      o'.degree o hn' (f : C(M', M)) * symplecticChernNumber o hn G ω := by
  obtain ⟨J, hJ⟩ := hω.exists_compatible
  rw [symplecticChernNumber_eq_chernNumber o' hn' G (hJ.tames.pullback f f.contMDiff),
    symplecticChernNumber_eq_chernNumber o hn G hJ.tames,
    ← chernNumber_pullback o hn G J.toContinuousComplexStructure.Fiber o' hn' (f : C(M', M)),
    chernNumber_def, chernNumber_def, J.firstChernClass_pullback G f f.contMDiff,
    SymplecticGeometry.Bundle.firstChernClass_pullback]

end Symplectic

end Bundle

end SymplecticGeometry
