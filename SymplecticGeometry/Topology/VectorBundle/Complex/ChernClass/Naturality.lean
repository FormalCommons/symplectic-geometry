/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Point
public import SymplecticGeometry.Topology.VectorBundle.Complex.ChernClass.Basic
import SymplecticGeometry.Topology.VectorBundle.ModelEquiv
import SymplecticGeometry.AlgebraicTopology.Cohomology.Empty

/-!
# Naturality of the Chern classes

Over compact bases, the Chern classes of complex vector bundles are natural: the classes of a
pull-back `f *ᵖ E` are the pull-backs along `f` of the classes of `E`, isomorphic bundles have the
same classes, and the classes of a trivial bundle vanish in positive degree.

All three come from one statement, `chernClass_eq_singularCohomologyMap_of_projectiveBundle`: a
map `g : P(E') → P(E)` of projective bundles over a map `h : B' → B` of bases, between bundles
of the same rank, that pulls the tautological class of `E` back to that of `E'`, carries the
defining relation of the Chern classes of `E` to a relation of the same form on `P(E')`, whose
coefficients are the pull-backs along `h`
(`evenIntegralCohomologyMap_sum_mul_projectiveBundleClass_pow`, for bundles of any ranks); by
uniqueness these are the Chern classes of `E'`. The
tautological class is pulled back to the tautological class whenever the tautological lines are
(`singularCohomologyMap_projectiveBundleClass_of_fiberwise`, from the naturality of the Euler
class `TauCeti.complexEulerClass_eq_singularCohomologyMap_of_fiberwise`), which holds for
`ProjectiveBundle.pullbackMap f`, for `ProjectiveBundle.map φ hφ`, and for the embeddings
`ProjectiveBundle.inl` and `ProjectiveBundle.inr` of the summands of a direct sum. The trivial
bundle over `B` is the pull-back of the trivial bundle over a point, whose cohomology vanishes in
positive degree.

## Main results

* `singularCohomologyMap_inl_projectiveBundleClass`,
  `singularCohomologyMap_inr_projectiveBundleClass`: `inl` and `inr` pull the tautological class
  of `E₁ ⊕ E₂` back to those of `E₁` and `E₂`.
* `evenIntegralCohomologyMap_sum_mul_projectiveBundleClass_pow`: a map of projective bundles
  that preserves the tautological class carries a relation of the form of the defining relation
  of the Chern classes to one of the same form, with coefficients pulled back to the new base.
* `chernClass_pullback`, `totalChernClass_pullback`: `c_k(f *ᵖ E) = f^* c_k(E)` and
  `c(f *ᵖ E) = f^* c(E)`, for `f : C(B', B)` between compact spaces.
* `chernClass_congr`, `totalChernClass_congr`: a complex-linear fibrewise isomorphism, continuous
  on total spaces, preserves the Chern classes; the two models may differ.
* `chernClass_trivial`, `totalChernClass_trivial`: the Chern classes of `Bundle.Trivial B G`
  vanish in positive degree, and its total Chern class is `1`.

## References

* [R. Bott, L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §20 (the
  naturality of the Chern classes, from that of the tautological class and the uniqueness of the
  coefficients of the relation).
* A. Hatcher, *Vector Bundles and K-Theory*, §3.1 (the proof of Theorem 3.2: naturality from
  the pull-back of the projective bundle).
-/

public section

noncomputable section

open Bundle Module TauCeti CategoryTheory

namespace SymplecticGeometry.Bundle

variable {B : Type} [TopologicalSpace B]
  {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G]
  {E : B → Type} [∀ b, AddCommGroup (E b)] [∀ b, Module ℂ (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsScalarTower ℝ ℂ (E b)] [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace G E)]
  [FiberBundle G E] [VectorBundle ℂ G E]
  {B' : Type} [TopologicalSpace B']
  {G' : Type} [NormedAddCommGroup G'] [NormedSpace ℂ G']
  {E' : B' → Type} [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, Module ℝ (E' b)]
  [∀ b, IsScalarTower ℝ ℂ (E' b)] [∀ b, TopologicalSpace (E' b)]
  [TopologicalSpace (TotalSpace G' E')] [FiberBundle G' E'] [VectorBundle ℂ G' E']

/-! ### The tautological class under maps of projective bundles -/

/-- A continuous map `g : P(E') → P(E)` of projective bundles pulls the tautological class of `E`
back to that of `E'` when the tautological line of `E'` is isomorphic to the pull-back along `g`
of that of `E`, by a fibrewise complex-linear isomorphism continuous on total spaces. -/
theorem singularCohomologyMap_projectiveBundleClass_of_fiberwise
    {g : C(ProjectiveBundle ℂ G' E', ProjectiveBundle ℂ G E)}
    {φ : ∀ p, ProjectiveBundle.Tautological ℂ G' E' p ≃L[ℂ]
      ProjectiveBundle.Tautological ℂ G E (g p)}
    (hφ : Continuous fun v : TotalSpace ℂ (ProjectiveBundle.Tautological ℂ G' E') ↦
      TotalSpace.mk' ℂ (E := ProjectiveBundle.Tautological ℂ G E) (g v.proj)
        (φ v.proj v.snd)) :
    TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (projectiveBundleClass G E) =
      projectiveBundleClass G' E' := by
  rw [projectiveBundleClass_def, projectiveBundleClass_def, map_neg,
    complexEulerClass_eq_singularCohomologyMap_of_fiberwise (r := 0) (finrank_self ℂ)
      (finrank_self ℂ) hφ]
  exact congrArg Neg.neg (TopCat.uliftIntegralCohomologyIso_naturality_apply _ 2 _).symm

/-- The map `ProjectiveBundle.pullbackMap f : P(f *ᵖ E) → P(E)` pulls the tautological class of
`E` back to that of `f *ᵖ E`. -/
theorem singularCohomologyMap_pullbackMap_projectiveBundleClass (f : C(B', B)) :
    TopCat.singularCohomologyMap (TopCat.ofHom (ProjectiveBundle.pullbackMap ℂ G E f)) 2
      (projectiveBundleClass G E) = projectiveBundleClass G (f *ᵖ E) :=
  singularCohomologyMap_projectiveBundleClass_of_fiberwise (φ := fun _ ↦ .refl ℂ _)
    (((Pullback.continuous_lift _ _ _).comp
      (ProjectiveBundle.tautologicalPullbackHomeomorph ℂ G E f).continuous).congr fun v ↦ by
        rw [Function.comp_apply, ProjectiveBundle.tautologicalPullbackHomeomorph_apply]
        -- The fibres of the tautological line of `f *ᵖ E` and of the pull-back along
        -- `pullbackMap` of that of `E` are the same lines, but in two families of types.
        rfl)

/-- The homeomorphism `ProjectiveBundle.map φ hφ : P(E) → P(E')` induced by a fibrewise
isomorphism `φ` pulls the tautological class of `E'` back to that of `E`. -/
theorem singularCohomologyMap_map_projectiveBundleClass [FiniteDimensional ℂ G]
    {E' : B → Type} [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, IsScalarTower ℝ ℂ (E' b)] [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace G' E')] [FiberBundle G' E'] [VectorBundle ℂ G' E']
    {φ : ∀ b, E b ≃L[ℂ] E' b}
    (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd)) :
    TopCat.singularCohomologyMap
        (TopCat.ofHom ((ProjectiveBundle.map φ hφ : _ ≃ₜ _) : C(_, ProjectiveBundle ℂ G' E')))
        2 (projectiveBundleClass G' E') = projectiveBundleClass G E :=
  singularCohomologyMap_projectiveBundleClass_of_fiberwise
    (φ := ProjectiveBundle.tautologicalMapEquiv hφ)
    ((Pullback.continuous_lift _ _ _).comp (ProjectiveBundle.continuous_tautologicalMapEquiv hφ))

section Sum

variable {G₁ : Type} [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
  {E₁ : B → Type} [∀ b, AddCommGroup (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, Module ℝ (E₁ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace G₁ E₁)] [FiberBundle G₁ E₁] [VectorBundle ℂ G₁ E₁]
  {G₂ : Type} [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
  {E₂ : B → Type} [∀ b, AddCommGroup (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, Module ℝ (E₂ b)]
  [∀ b, IsScalarTower ℝ ℂ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [TopologicalSpace (TotalSpace G₂ E₂)] [FiberBundle G₂ E₂] [VectorBundle ℂ G₂ E₂]

/-- The embedding `inl : P(E₁) → P(E₁ ⊕ E₂)` pulls the tautological class of `E₁ ⊕ E₂` back to
that of `E₁`. -/
theorem singularCohomologyMap_inl_projectiveBundleClass :
    TopCat.singularCohomologyMap
        (TopCat.ofHom (ProjectiveBundle.inl G₂ E₂ : C(ProjectiveBundle ℂ G₁ E₁, _))) 2
        (projectiveBundleClass (G₁ × G₂) (E₁ ×ᵇ E₂)) = projectiveBundleClass G₁ E₁ :=
  singularCohomologyMap_projectiveBundleClass_of_fiberwise
    (φ := ProjectiveBundle.tautologicalInlEquiv G₂ E₂)
    ((Pullback.continuous_lift _ _ _).comp ProjectiveBundle.continuous_tautologicalInlEquiv)

/-- The embedding `inr : P(E₂) → P(E₁ ⊕ E₂)` pulls the tautological class of `E₁ ⊕ E₂` back to
that of `E₂`. -/
theorem singularCohomologyMap_inr_projectiveBundleClass :
    TopCat.singularCohomologyMap
        (TopCat.ofHom (ProjectiveBundle.inr G₁ E₁ : C(ProjectiveBundle ℂ G₂ E₂, _))) 2
        (projectiveBundleClass (G₁ × G₂) (E₁ ×ᵇ E₂)) = projectiveBundleClass G₂ E₂ :=
  singularCohomologyMap_projectiveBundleClass_of_fiberwise
    (φ := ProjectiveBundle.tautologicalInrEquiv G₁ E₁)
    ((Pullback.continuous_lift _ _ _).comp ProjectiveBundle.continuous_tautologicalInrEquiv)

end Sum

/-! ### Chern classes under maps of projective bundles -/

/-- Let `g : P(E') → P(E)` be a map of projective bundles over `h : B' → B` that pulls the
tautological class `x` of `E` back to the tautological class `x'` of `E'`. For classes `aᵢ` of
degree `2i` on `B`, the ring map of `g` sends `∑_{i ≤ n} π^* aᵢ x^{n-i}` to
`∑_{i ≤ n} π'^* (h^* aᵢ) x'^{n-i}`. -/
theorem evenIntegralCohomologyMap_sum_mul_projectiveBundleClass_pow (h : C(B', B))
    (g : C(ProjectiveBundle ℂ G' E', ProjectiveBundle ℂ G E))
    (hπ : (ProjectiveBundle.projection ℂ G E).comp g =
      h.comp (ProjectiveBundle.projection ℂ G' E'))
    (hx : TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (projectiveBundleClass G E) =
      projectiveBundleClass G' E')
    (a : ∀ k : ℕ, (TopCat.of B).integralCohomology (2 * k)) (n : ℕ) :
    TopCat.evenIntegralCohomologyMap (TopCat.ofHom g)
        (∑ i ∈ Finset.range (n + 1),
          TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G E))
            ((TopCat.of B).evenIntegralCohomologyOf i (a i)) *
          (TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
            (projectiveBundleClass G E) ^ (n - i)) =
      ∑ i ∈ Finset.range (n + 1),
        TopCat.evenIntegralCohomologyMap (TopCat.ofHom (ProjectiveBundle.projection ℂ G' E'))
          ((TopCat.of B').evenIntegralCohomologyOf i
            (TopCat.singularCohomologyMap (TopCat.ofHom h) (2 * i) (a i))) *
        (TopCat.of (ProjectiveBundle ℂ G' E')).evenIntegralCohomologyOf 1
          (projectiveBundleClass G' E') ^ (n - i) := by
  have hx' : TopCat.evenIntegralCohomologyMap (TopCat.ofHom g)
      ((TopCat.of (ProjectiveBundle ℂ G E)).evenIntegralCohomologyOf 1
        (projectiveBundleClass G E)) =
      (TopCat.of (ProjectiveBundle ℂ G' E')).evenIntegralCohomologyOf 1
        (projectiveBundleClass G' E') := by
    rw [TopCat.evenIntegralCohomologyMap_of]
    -- `evenIntegralCohomologyMap_of` pulls back in degree `2 * 1`, which `hx` writes `2`.
    exact congrArg _ hx
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, hx', ← RingHom.comp_apply, ← TopCat.evenIntegralCohomologyMap_comp,
    ← TopCat.ofHom_comp, hπ, TopCat.ofHom_comp, TopCat.evenIntegralCohomologyMap_comp,
    RingHom.comp_apply, TopCat.evenIntegralCohomologyMap_of (TopCat.ofHom h)]

variable [FiniteDimensional ℂ G] [CompactSpace B] [FiniteDimensional ℂ G'] [CompactSpace B']

/-- **Chern classes under maps of projective bundles.** Let `E → B` and `E' → B'` be complex
vector bundles of the same rank over compact bases, `h : B' → B` a continuous map, and
`g : P(E') → P(E)` a map of projective bundles over `h` that pulls the tautological class of `E`
back to that of `E'`. Then `c_k(E') = h^* c_k(E)` for every `k`. -/
theorem chernClass_eq_singularCohomologyMap_of_projectiveBundle
    (hG : finrank ℂ G' = finrank ℂ G) (h : C(B', B))
    (g : C(ProjectiveBundle ℂ G' E', ProjectiveBundle ℂ G E))
    (hπ : (ProjectiveBundle.projection ℂ G E).comp g =
      h.comp (ProjectiveBundle.projection ℂ G' E'))
    (hx : TopCat.singularCohomologyMap (TopCat.ofHom g) 2 (projectiveBundleClass G E) =
      projectiveBundleClass G' E') (k : ℕ) :
    chernClass G' E' k =
      TopCat.singularCohomologyMap (TopCat.ofHom h) (2 * k) (chernClass G E k) := by
  rcases lt_or_ge (finrank ℂ G') k with hk | hk
  · rw [chernClass_eq_zero_of_finrank_lt G' E' hk, chernClass_eq_zero_of_finrank_lt G E (hG ▸ hk),
      map_zero]
  refine (chernClass_eq_of_sum_mul_pow_eq_zero G' E'
    (fun i ↦ TopCat.singularCohomologyMap (TopCat.ofHom h) (2 * i) (chernClass G E i))
    (by simp) ?_ hk).symm
  have hrel := congrArg (TopCat.evenIntegralCohomologyMap (TopCat.ofHom g))
    (sum_chernClass_mul_projectiveBundleClass_pow G E)
  rw [evenIntegralCohomologyMap_sum_mul_projectiveBundleClass_pow h g hπ hx, map_zero] at hrel
  rwa [hG]

/-! ### Pull-backs -/

/-- **Naturality of the Chern classes.** For a continuous map `f : B' → B` of compact spaces,
`c_k(f *ᵖ E) = f^* c_k(E)` for every `k`. -/
theorem chernClass_pullback (f : C(B', B)) (k : ℕ) :
    chernClass G (f *ᵖ E) k =
      TopCat.singularCohomologyMap (TopCat.ofHom f) (2 * k) (chernClass G E k) :=
  chernClass_eq_singularCohomologyMap_of_projectiveBundle rfl f
    (ProjectiveBundle.pullbackMap ℂ G E f) (ContinuousMap.ext fun _ ↦ rfl)
    (singularCohomologyMap_pullbackMap_projectiveBundleClass f) k

/-- **Naturality of the total Chern class.** For a continuous map `f : B' → B` of compact spaces,
`c(f *ᵖ E) = f^* c(E)` in the even integral cohomology ring. -/
theorem totalChernClass_pullback (f : C(B', B)) :
    totalChernClass G (f *ᵖ E) =
      TopCat.evenIntegralCohomologyMap (TopCat.ofHom f) (totalChernClass G E) :=
  DFinsupp.ext fun k ↦ by
    rw [totalChernClass_apply, TopCat.evenIntegralCohomologyMap_apply, totalChernClass_apply,
      chernClass_pullback]

/-! ### Isomorphic bundles -/

omit [FiniteDimensional ℂ G'] in
/-- **Isomorphic complex bundles have the same Chern classes.** The isomorphism is a family of
complex-linear equivalences of the fibres, continuous on total spaces; the two models may
differ. -/
theorem chernClass_congr
    {E' : B → Type} [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, IsScalarTower ℝ ℂ (E' b)] [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace G' E')] [FiberBundle G' E'] [VectorBundle ℂ G' E']
    (φ : ∀ b, E b ≃L[ℂ] E' b)
    (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd))
    (k : ℕ) : chernClass G E k = chernClass G' E' k := by
  rcases isEmpty_or_nonempty B with hB | hB
  · exact Subsingleton.elim _ _
  -- The fibres over any point identify the two models.
  have : FiniteDimensional ℂ G' :=
    (VectorBundle.modelEquiv G G' (Classical.arbitrary B) (φ _)).toLinearEquiv.finiteDimensional
  have hx := singularCohomologyMap_map_projectiveBundleClass (E := E) (E' := E') hφ
  have h := chernClass_eq_singularCohomologyMap_of_projectiveBundle (G := G') (E := E') (G' := G)
    (E' := E) (VectorBundle.finrank_model_eq φ).symm (ContinuousMap.id B) _
    (ContinuousMap.ext fun _ ↦ rfl) hx k
  rw [h, TopCat.ofHom_id, TopCat.singularCohomologyMap_id, ModuleCat.id_apply]

omit [FiniteDimensional ℂ G'] in
/-- **Isomorphic complex bundles have the same total Chern class.** The isomorphism is a family of
complex-linear equivalences of the fibres, continuous on total spaces; the two models may
differ. -/
theorem totalChernClass_congr
    {E' : B → Type} [∀ b, AddCommGroup (E' b)] [∀ b, Module ℂ (E' b)] [∀ b, Module ℝ (E' b)]
    [∀ b, IsScalarTower ℝ ℂ (E' b)] [∀ b, TopologicalSpace (E' b)]
    [TopologicalSpace (TotalSpace G' E')] [FiberBundle G' E'] [VectorBundle ℂ G' E']
    (φ : ∀ b, E b ≃L[ℂ] E' b)
    (hφ : Continuous fun v : TotalSpace G E ↦ TotalSpace.mk' G' v.proj (φ v.proj v.snd)) :
    totalChernClass G E = totalChernClass G' E' :=
  DFinsupp.ext fun k ↦ by
    rw [totalChernClass_apply, totalChernClass_apply, chernClass_congr φ hφ k]

/-! ### Trivial bundles -/

variable (B G) in
/-- **The Chern classes of a trivial bundle vanish in positive degree.** Over a compact base, the
trivial bundle `Bundle.Trivial B G` is the pull-back of the trivial bundle over a point, whose
cohomology vanishes in positive degree. -/
@[simp]
theorem chernClass_trivial {k : ℕ} (hk : k ≠ 0) : chernClass G (Bundle.Trivial B G) k = 0 := by
  let c : C(B, Unit) := ContinuousMap.const B ()
  have hc : Continuous fun v : TotalSpace G (Bundle.Trivial B G) ↦
      TotalSpace.mk' G (E := c *ᵖ (Bundle.Trivial Unit G)) v.proj
        (ContinuousLinearEquiv.refl ℂ G v.snd) :=
    Pullback.continuous_iff.2 ⟨FiberBundle.continuous_proj _ _,
      (Trivial.homeomorphProd Unit G).symm.continuous.comp
        (continuous_const.prodMk ((Trivial.homeomorphProd B G).continuous.snd))⟩
  have hz := ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_point
    (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ ℤ) (TopCat.of Unit)
    (n := 2 * k) (by omega))
  rw [chernClass_congr (E := Bundle.Trivial B G) (E' := c *ᵖ (Bundle.Trivial Unit G)) (G' := G)
      (fun _ ↦ .refl ℂ G) hc k, chernClass_pullback c k,
    Subsingleton.elim (chernClass G (Bundle.Trivial Unit G) k) 0, map_zero]

variable (B G) in
/-- **The total Chern class of a trivial bundle is `1`**, over a compact base. -/
@[simp]
theorem totalChernClass_trivial : totalChernClass G (Bundle.Trivial B G) = 1 :=
  DFinsupp.ext fun k ↦ by
    rw [totalChernClass_apply, ← TopCat.evenIntegralCohomologyOf_one]
    rcases eq_or_ne k 0 with rfl | hk
    · rw [chernClass_zero, DirectSum.of_eq_same]
    · rw [chernClass_trivial B G hk, DirectSum.of_eq_of_ne 0 k _ hk]

end SymplecticGeometry.Bundle

end
