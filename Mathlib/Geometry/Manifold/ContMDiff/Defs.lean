import Mathlib.Tactic.Have
/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.LocalInvariantProperties

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `ContMDiffWithinAt I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `ContMDiffAt I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `ContMDiffOn I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `ContMDiff I I' n f` states that the function `f` is `Cⁿ`.

We also give some basic properties of smooth functions between manifolds, following the API of
smooth functions between vector spaces.
See `Basic.lean` for further basic properties of smooth functions between smooth manifolds,
`NormedSpace.lean` for the equivalence of manifold-smoothness to usual smoothness,
`Product.lean` for smoothness results related to the product of manifolds and
`Atlas.lean` for smoothness of atlas members and local structomorphisms.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the smooth groupoid. We take advantage of the
general machinery developed in `LocalInvariantProperties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `liftPropWithinAt_indep_chart`.

For this to work, the definition of `ContMDiffWithinAt` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `contMDiffOn_iff` and `contMDiff_iff`.
-/


open Set Function Filter ChartedSpace SmoothManifoldWithCorners

open scoped Topology Manifold

/-! ### Definition of smooth functions between manifolds -/


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']
  -- declare a manifold `M''` over the pair `(E'', H'')`.
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a smooth manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [SmoothManifoldWithCorners J N]
  -- declare a smooth manifold `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  [SmoothManifoldWithCorners J' N']
  -- F₁, F₂, F₃, F₄ are normed spaces
  {F₁ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {F₂ : Type*} [NormedAddCommGroup F₂]
  [NormedSpace 𝕜 F₂] {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] {F₄ : Type*}
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]
  -- declare functions, sets, points and smoothness indices
  {e : PartialHomeomorph M H}
  {e' : PartialHomeomorph M' H'} {f f₁ : M → M'} {s s₁ t : Set M} {x : M} {m n : ℕ∞}

/-- Property in the model space of a model with corners of being `C^n` within at set at a point,
when read in the model vector space. This property will be lifted to manifolds to define smooth
functions between manifolds. -/
def ContDiffWithinAtProp (n : ℕ∞) (f : H → H') (s : Set H) (x : H) : Prop :=
  ContDiffWithinAt 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)

theorem contDiffWithinAtProp_self_source {f : E → H'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) I' n f s x ↔ ContDiffWithinAt 𝕜 n (I' ∘ f) s x := by
  simp_rw [ContDiffWithinAtProp, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, CompTriple.comp_eq, preimage_id_eq, id_eq]

theorem contDiffWithinAtProp_self {f : E → E'} {s : Set E} {x : E} :
    ContDiffWithinAtProp 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAtProp_self_source 𝓘(𝕜, E')

theorem contDiffWithinAtProp_self_target {f : H → E'} {s : Set H} {x : H} :
    ContDiffWithinAtProp I 𝓘(𝕜, E') n f s x ↔
      ContDiffWithinAt 𝕜 n (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
  Iff.rfl

/-- Being `Cⁿ` in the model space is a local property, invariant under smooth maps. Therefore,
it will lift nicely to manifolds. -/
theorem contDiffWithinAt_localInvariantProp (n : ℕ∞) :
    (contDiffGroupoid ∞ I).LocalInvariantProp (contDiffGroupoid ∞ I')
      (ContDiffWithinAtProp I I' n) where
  is_local {s x u f} u_open xu := by
    have : I.symm ⁻¹' (s ∩ u) ∩ range I = I.symm ⁻¹' s ∩ range I ∩ I.symm ⁻¹' u
    simp only [inter_right_comm, preimage_inter]
    rw [ContDiffWithinAtProp, ContDiffWithinAtProp, this]
    symm
    apply contDiffWithinAt_inter
    have : u ∈ 𝓝 (I.symm (I x))
    rw [ModelWithCorners.left_inv]
    exact u_open.mem_nhds xu
    apply ContinuousAt.preimage_mem_nhds I.continuous_symm.continuousAt this
  right_invariance' {s x f e} he hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x))
    simp only [hx, mfld_simps]
    rw [this] at h
    have : I (e x) ∈ I.symm ⁻¹' e.target ∩ range I
    simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he).2.contDiffWithinAt this
    convert (h.comp' _ (this.of_le le_top)).mono_of_mem _ using 1
    ext y; simp only [mfld_simps]
    refine mem_nhdsWithin.mpr
      ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm, by
        simp_rw [mem_preimage, I.left_inv, e.mapsTo hx], ?_⟩
    mfld_set_tac
  congr_of_forall {s x f g} h hx hf := by
    apply hf.congr
    intro y hy
    simp only [mfld_simps] at hy
    simp only [h, hy, mfld_simps]
    simp only [hx, mfld_simps]
  left_invariance' {s x f e'} he' hs hx h := by
    rw [ContDiffWithinAtProp] at h ⊢
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ I'.symm ⁻¹' e'.source ∩ range I'
    simp only [hx, mfld_simps]
    have := (mem_groupoid_of_pregroupoid.2 he').1.contDiffWithinAt A
    convert (this.of_le le_top).comp _ h _
    ext y; simp only [mfld_simps]
    intro y hy; simp only [mfld_simps] at hy; simpa only [hy, mfld_simps] using hs hy.1

theorem contDiffWithinAtProp_mono_of_mem (n : ℕ∞) ⦃s x t⦄ ⦃f : H → H'⦄ (hts : s ∈ 𝓝[t] x)
    (h : ContDiffWithinAtProp I I' n f s x) : ContDiffWithinAtProp I I' n f t x := by
  refine h.mono_of_mem ?_
  refine inter_mem ?_ (mem_of_superset self_mem_nhdsWithin inter_subset_right)
  rwa [← Filter.mem_map, ← I.image_eq, I.symm_map_nhdsWithin_image]

theorem contDiffWithinAtProp_id (x : H) : ContDiffWithinAtProp I I n id univ x := by
  simp only [ContDiffWithinAtProp, id_comp, preimage_univ, univ_inter]
  have : ContDiffWithinAt 𝕜 n id (range I) (I x) := contDiff_id.contDiffAt.contDiffWithinAt
  refine this.congr (fun y hy => ?_) ?_
  simp only [ModelWithCorners.right_inv I hy, mfld_simps]
  simp only [mfld_simps]

/-- A function is `n` times continuously differentiable within a set at a point in a manifold if
it is continuous and it is `n` times continuously differentiable in this set around this point, when
read in the preferred chart at this point. -/
def ContMDiffWithinAt (n : ℕ∞) (f : M → M') (s : Set M) (x : M) :=
  LiftPropWithinAt (ContDiffWithinAtProp I I' n) f s x

/-- Abbreviation for `ContMDiffWithinAt I I' ⊤ f s x`. See also documentation for `Smooth`.
-/
abbrev SmoothWithinAt (f : M → M') (s : Set M) (x : M) :=
  ContMDiffWithinAt I I' ⊤ f s x

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def ContMDiffAt (n : ℕ∞) (f : M → M') (x : M) :=
  ContMDiffWithinAt I I' n f univ x

theorem contMDiffAt_iff {n : ℕ∞} {f : M → M'} {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x) :=
  liftPropAt_iff.trans <| by rw [ContDiffWithinAtProp, preimage_univ, univ_inter]; rfl

/-- Abbreviation for `ContMDiffAt I I' ⊤ f x`. See also documentation for `Smooth`. -/
abbrev SmoothAt (f : M → M') (x : M) :=
  ContMDiffAt I I' ⊤ f x

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def ContMDiffOn (n : ℕ∞) (f : M → M') (s : Set M) :=
  ∀ x ∈ s, ContMDiffWithinAt I I' n f s x

/-- Abbreviation for `ContMDiffOn I I' ⊤ f s`. See also documentation for `Smooth`. -/
abbrev SmoothOn (f : M → M') (s : Set M) :=
  ContMDiffOn I I' ⊤ f s

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def ContMDiff (n : ℕ∞) (f : M → M') :=
  ∀ x, ContMDiffAt I I' n f x

/-- Abbreviation for `ContMDiff I I' ⊤ f`.
Short note to work with these abbreviations: a lemma of the form `ContMDiffFoo.bar` will
apply fine to an assumption `SmoothFoo` using dot notation or normal notation.
If the consequence `bar` of the lemma involves `ContDiff`, it is still better to restate
the lemma replacing `ContDiff` with `Smooth` both in the assumption and in the conclusion,
to make it possible to use `Smooth` consistently.
This also applies to `SmoothAt`, `SmoothOn` and `SmoothWithinAt`. -/
abbrev Smooth (f : M → M') :=
  ContMDiff I I' ⊤ f

variable {I I'}

/-! ### Deducing smoothness from higher smoothness -/

theorem ContMDiffWithinAt.of_le (hf : ContMDiffWithinAt I I' n f s x) (le : m ≤ n) :
    ContMDiffWithinAt I I' m f s x := by
  simp only [ContMDiffWithinAt, LiftPropWithinAt] at hf ⊢
  exact ⟨hf.1, hf.2.of_le le⟩

theorem ContMDiffAt.of_le (hf : ContMDiffAt I I' n f x) (le : m ≤ n) : ContMDiffAt I I' m f x :=
  ContMDiffWithinAt.of_le hf le

theorem ContMDiffOn.of_le (hf : ContMDiffOn I I' n f s) (le : m ≤ n) : ContMDiffOn I I' m f s :=
  fun x hx => (hf x hx).of_le le

theorem ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m ≤ n) : ContMDiff I I' m f := fun x =>
  (hf x).of_le le

/-! ### Basic properties of smooth functions between manifolds -/

theorem ContMDiff.smooth (h : ContMDiff I I' ⊤ f) : Smooth I I' f :=
  h

theorem Smooth.contMDiff (h : Smooth I I' f) : ContMDiff I I' n f :=
  h.of_le le_top

theorem ContMDiffOn.smoothOn (h : ContMDiffOn I I' ⊤ f s) : SmoothOn I I' f s :=
  h

theorem SmoothOn.contMDiffOn (h : SmoothOn I I' f s) : ContMDiffOn I I' n f s :=
  h.of_le le_top

theorem ContMDiffAt.smoothAt (h : ContMDiffAt I I' ⊤ f x) : SmoothAt I I' f x :=
  h

theorem SmoothAt.contMDiffAt (h : SmoothAt I I' f x) : ContMDiffAt I I' n f x :=
  h.of_le le_top

theorem ContMDiffWithinAt.smoothWithinAt (h : ContMDiffWithinAt I I' ⊤ f s x) :
    SmoothWithinAt I I' f s x :=
  h

theorem SmoothWithinAt.contMDiffWithinAt (h : SmoothWithinAt I I' f s x) :
    ContMDiffWithinAt I I' n f s x :=
  h.of_le le_top

theorem ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : ContMDiffAt I I' n f x :=
  h x

theorem Smooth.smoothAt (h : Smooth I I' f) : SmoothAt I I' f x :=
  ContMDiff.contMDiffAt h

theorem contMDiffWithinAt_univ : ContMDiffWithinAt I I' n f univ x ↔ ContMDiffAt I I' n f x :=
  Iff.rfl

theorem smoothWithinAt_univ : SmoothWithinAt I I' f univ x ↔ SmoothAt I I' f x :=
  contMDiffWithinAt_univ

theorem contMDiffOn_univ : ContMDiffOn I I' n f univ ↔ ContMDiff I I' n f := by
  simp only [ContMDiffOn, ContMDiff, contMDiffWithinAt_univ, forall_prop_of_true, mem_univ]

theorem smoothOn_univ : SmoothOn I I' f univ ↔ Smooth I I' f :=
  contMDiffOn_univ

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
theorem contMDiffWithinAt_iff :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff']; rfl

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `contMDiffWithinAt_iff`, it is
a smaller set, but their germs at `extChartAt I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
theorem contMDiffWithinAt_iff' :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩
            (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [ContMDiffWithinAt, liftPropWithinAt_iff']
  exact and_congr_right fun hc => contDiffWithinAt_congr_nhds <|
    hc.nhdsWithin_extChartAt_symm_preimage_inter_range I I'

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
theorem contMDiffWithinAt_iff_target :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) s x := by
  simp_rw [ContMDiffWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
      and_iff_left_of_imp <| (continuousAt_extChartAt _ _).comp_continuousWithinAt
  simp_rw [cont, ContDiffWithinAtProp, extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.coe_coe, modelWithCornersSelf_coe,
    chartAt_self_eq, PartialHomeomorph.refl_apply, id_comp]
  rfl

theorem smoothWithinAt_iff :
    SmoothWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 ∞ (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) :=
  contMDiffWithinAt_iff

theorem smoothWithinAt_iff_target :
    SmoothWithinAt I I' f s x ↔
      ContinuousWithinAt f s x ∧ SmoothWithinAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) s x :=
  contMDiffWithinAt_iff_target

theorem contMDiffAt_iff_target {x : M} :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) x := by
  rw [ContMDiffAt, ContMDiffAt, contMDiffWithinAt_iff_target, continuousWithinAt_univ]

theorem smoothAt_iff_target {x : M} :
    SmoothAt I I' f x ↔ ContinuousAt f x ∧ SmoothAt I 𝓘(𝕜, E') (extChartAt I' (f x) ∘ f) x :=
  contMDiffAt_iff_target

theorem contMDiffWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_indep_chart he hx he' hy

/-- An alternative formulation of `contMDiffWithinAt_iff_of_mem_maximalAtlas`
  if the set if `s` lies in `e.source`. -/
theorem contMDiffWithinAt_iff_image {x : M} (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧
        ContDiffWithinAt 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas he he' hx hy, and_congr_right_iff]
  refine fun _ => contDiffWithinAt_congr_nhds ?_
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventuallyEq I hs hx]

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
theorem contMDiffWithinAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas _ x)
    (chart_mem_maximalAtlas _ y) hx hy

theorem contMDiffWithinAt_iff_of_mem_source' {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContinuousWithinAt f s x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (contMDiffWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => contDiffWithinAt_congr_nhds ?_
  rw [← e.image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image' I hx, ←
    map_extChartAt_nhdsWithin' I hx, inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' _ hy)

theorem contMDiffAt_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source)
    (hy : f x' ∈ (chartAt H' y).source) :
    ContMDiffAt I I' n f x' ↔
      ContinuousAt f x' ∧
        ContDiffWithinAt 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
  (contMDiffWithinAt_iff_of_mem_source hx hy).trans <| by
    rw [continuousWithinAt_univ, preimage_univ, univ_inter]

theorem contMDiffWithinAt_iff_target_of_mem_source {x : M} {y : M'}
    (hy : f x ∈ (chartAt H' y).source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContinuousWithinAt f s x ∧ ContMDiffWithinAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) s x := by
  simp_rw [ContMDiffWithinAt]
  rw [(contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas I' y) hy,
    and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy
  simp_rw [(continuousAt_extChartAt' I' hy).comp_continuousWithinAt hf]
  rfl

theorem contMDiffAt_iff_target_of_mem_source {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    ContMDiffAt I I' n f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) x := by
  rw [ContMDiffAt, contMDiffWithinAt_iff_target_of_mem_source hy, continuousWithinAt_univ,
    ContMDiffAt]

theorem contMDiffWithinAt_iff_source_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M)
    (hx : x ∈ e.source) :
    ContMDiffWithinAt I I' n f s x ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s ∩ range I)
        (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source I] at h2x
  simp_rw [ContMDiffWithinAt,
    (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, contDiffWithinAtProp_self_source,
    ContDiffWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl

theorem contMDiffWithinAt_iff_source_of_mem_source {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    ContMDiffWithinAt I I' n f s x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  contMDiffWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas I x) hx'

theorem contMDiffAt_iff_source_of_mem_source {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    ContMDiffAt I I' n f x' ↔
      ContMDiffWithinAt 𝓘(𝕜, E) I' n (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x') := by
  simp_rw [ContMDiffAt, contMDiffWithinAt_iff_source_of_mem_source hx', preimage_univ, univ_inter]

theorem contMDiffOn_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, ContDiffOn, Set.forall_mem_image, ← forall_and, ContMDiffOn]
  exact forall₂_congr fun x hx => contMDiffWithinAt_iff_image he he' hs (hs hx) (h2s hx)

theorem contMDiffOn_iff_of_mem_maximalAtlas' (he : e ∈ maximalAtlas I M)
    (he' : e' ∈ maximalAtlas I' M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    ContMDiffOn I I' n f s ↔
      ContDiffOn 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
  (contMDiffOn_iff_of_mem_maximalAtlas he he' hs h2s).trans <| and_iff_right_of_imp fun h ↦
    (e.continuousOn_writtenInExtend_iff _ _ hs h2s).1 h.continuousOn

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
  into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
  these charts.
  Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
  that this set lies in `(extChartAt I x).target`. -/
theorem contMDiffOn_iff_of_subset_source {x : M} {y : M'} (hs : s ⊆ (chartAt H x).source)
    (h2s : MapsTo f s (chartAt H' y).source) :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  contMDiffOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas I x) (chart_mem_maximalAtlas I' y) hs
    h2s

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
  into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
  these charts.
  Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
  that this set lies in `(extChartAt I x).target`. -/
theorem contMDiffOn_iff_of_subset_source' {x : M} {y : M'} (hs : s ⊆ (extChartAt I x).source)
    (h2s : MapsTo f s (extChartAt I' y).source) :
    ContMDiffOn I I' n f s ↔
        ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact contMDiffOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas I x)
    (chart_mem_maximalAtlas I' y) hs h2s

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
theorem contMDiffOn_iff :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  intro h
  refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
  simp only [mfld_simps] at hz
  let w := (extChartAt I x).symm z
  have : w ∈ s
  simp only [w, hz, mfld_simps]
  specialize h w this
  have w1 : w ∈ (chartAt H x).source
  simp only [w, hz, mfld_simps]
  have w2 : f w ∈ (chartAt H' y).source
  simp only [w, hz, mfld_simps]
  convert ((contMDiffWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
  simp only [w, hz, mfld_simps]
  mfld_set_tac
  rintro ⟨hcont, hdiff⟩ x hx
  refine (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_iff.mpr ?_
  refine ⟨hcont x hx, ?_⟩
  dsimp [ContDiffWithinAtProp]
  convert hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
  mfld_set_tac

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
theorem contMDiffOn_iff_target :
    ContMDiffOn I I' n f s ↔
      ContinuousOn f s ∧
        ∀ y : M',
          ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).source) := by
  simp only [contMDiffOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    PartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  refine fun h' y => ⟨?_, fun x _ => h' x y⟩
  have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
  convert (h''.comp' (chartAt H' y).continuousOn_toFun).comp' h
  simp
  exact fun h' x y => (h' y).2 x 0

theorem smoothOn_iff :
    SmoothOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 ⊤ (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) :=
  contMDiffOn_iff

theorem smoothOn_iff_target :
    SmoothOn I I' f s ↔
      ContinuousOn f s ∧
        ∀ y : M', SmoothOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (s ∩ f ⁻¹' (extChartAt I' y).source) :=
  contMDiffOn_iff_target

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
theorem contMDiff_iff :
    ContMDiff I I' n f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 n (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).source)) := by
  simp [← contMDiffOn_univ, contMDiffOn_iff, continuous_iff_continuousOn_univ]

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
theorem contMDiff_iff_target :
    ContMDiff I I' n f ↔
      Continuous f ∧ ∀ y : M',
        ContMDiffOn I 𝓘(𝕜, E') n (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) := by
  rw [← contMDiffOn_univ, contMDiffOn_iff_target]
  simp [continuous_iff_continuousOn_univ]

theorem smooth_iff :
    Smooth I I' f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          ContDiffOn 𝕜 ⊤ (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (f ⁻¹' (extChartAt I' y).source)) :=
  contMDiff_iff

theorem smooth_iff_target :
    Smooth I I' f ↔
      Continuous f ∧
        ∀ y : M', SmoothOn I 𝓘(𝕜, E') (extChartAt I' y ∘ f) (f ⁻¹' (extChartAt I' y).source) :=
  contMDiff_iff_target

/-! ### Deducing smoothness from smoothness one step beyond -/


theorem ContMDiffWithinAt.of_succ {n : ℕ} (h : ContMDiffWithinAt I I' n.succ f s x) :
    ContMDiffWithinAt I I' n f s x :=
  h.of_le (WithTop.coe_le_coe.2 (Nat.le_succ n))

theorem ContMDiffAt.of_succ {n : ℕ} (h : ContMDiffAt I I' n.succ f x) : ContMDiffAt I I' n f x :=
  ContMDiffWithinAt.of_succ h

theorem ContMDiffOn.of_succ {n : ℕ} (h : ContMDiffOn I I' n.succ f s) : ContMDiffOn I I' n f s :=
  fun x hx => (h x hx).of_succ

theorem ContMDiff.of_succ {n : ℕ} (h : ContMDiff I I' n.succ f) : ContMDiff I I' n f := fun x =>
  (h x).of_succ

/-! ### Deducing continuity from smoothness -/


theorem ContMDiffWithinAt.continuousWithinAt (hf : ContMDiffWithinAt I I' n f s x) :
    ContinuousWithinAt f s x :=
  hf.1

theorem ContMDiffAt.continuousAt (hf : ContMDiffAt I I' n f x) : ContinuousAt f x :=
  (continuousWithinAt_univ _ _).1 <| ContMDiffWithinAt.continuousWithinAt hf

theorem ContMDiffOn.continuousOn (hf : ContMDiffOn I I' n f s) : ContinuousOn f s := fun x hx =>
  (hf x hx).continuousWithinAt

theorem ContMDiff.continuous (hf : ContMDiff I I' n f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

/-! ### `C^∞` smoothness -/

theorem contMDiffWithinAt_top :
    SmoothWithinAt I I' f s x ↔ ∀ n : ℕ, ContMDiffWithinAt I I' n f s x :=
  ⟨fun h n => ⟨h.1, contDiffWithinAt_top.1 h.2 n⟩, fun H =>
    ⟨(H 0).1, contDiffWithinAt_top.2 fun n => (H n).2⟩⟩

theorem contMDiffAt_top : SmoothAt I I' f x ↔ ∀ n : ℕ, ContMDiffAt I I' n f x :=
  contMDiffWithinAt_top

theorem contMDiffOn_top : SmoothOn I I' f s ↔ ∀ n : ℕ, ContMDiffOn I I' n f s :=
  ⟨fun h _ => h.of_le le_top, fun h x hx => contMDiffWithinAt_top.2 fun n => h n x hx⟩

theorem contMDiff_top : Smooth I I' f ↔ ∀ n : ℕ, ContMDiff I I' n f :=
  ⟨fun h _ => h.of_le le_top, fun h x => contMDiffWithinAt_top.2 fun n => h n x⟩

theorem contMDiffWithinAt_iff_nat :
    ContMDiffWithinAt I I' n f s x ↔ ∀ m : ℕ, (m : ℕ∞) ≤ n → ContMDiffWithinAt I I' m f s x := by
  refine ⟨fun h m hm => h.of_le hm, fun h => ?_⟩
  cases' n with n
  exact contMDiffWithinAt_top.2 fun n => h n le_top
  exact h n le_rfl

/-! ### Restriction to a smaller set -/

theorem ContMDiffWithinAt.mono_of_mem (hf : ContMDiffWithinAt I I' n f s x) (hts : s ∈ 𝓝[t] x) :
    ContMDiffWithinAt I I' n f t x :=
  StructureGroupoid.LocalInvariantProp.liftPropWithinAt_mono_of_mem
    (contDiffWithinAtProp_mono_of_mem I I' n) hf hts

theorem ContMDiffWithinAt.mono (hf : ContMDiffWithinAt I I' n f s x) (hts : t ⊆ s) :
    ContMDiffWithinAt I I' n f t x :=
  hf.mono_of_mem <| mem_of_superset self_mem_nhdsWithin hts

theorem contMDiffWithinAt_congr_nhds (hst : 𝓝[s] x = 𝓝[t] x) :
    ContMDiffWithinAt I I' n f s x ↔ ContMDiffWithinAt I I' n f t x :=
  ⟨fun h => h.mono_of_mem <| hst ▸ self_mem_nhdsWithin, fun h =>
    h.mono_of_mem <| hst.symm ▸ self_mem_nhdsWithin⟩

theorem contMDiffWithinAt_insert_self :
    ContMDiffWithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x := by
  simp only [contMDiffWithinAt_iff, continuousWithinAt_insert_self]
  refine Iff.rfl.and <| (contDiffWithinAt_congr_nhds ?_).trans contDiffWithinAt_insert_self
  simp only [← map_extChartAt_nhdsWithin I, nhdsWithin_insert, Filter.map_sup, Filter.map_pure]

alias ⟨ContMDiffWithinAt.of_insert, _⟩ := contMDiffWithinAt_insert_self

-- TODO: use `alias` again once it can make protected theorems
theorem ContMDiffWithinAt.insert (h : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I' n f (insert x s) x :=
  contMDiffWithinAt_insert_self.2 h

theorem ContMDiffAt.contMDiffWithinAt (hf : ContMDiffAt I I' n f x) :
    ContMDiffWithinAt I I' n f s x :=
  ContMDiffWithinAt.mono hf (subset_univ _)

theorem SmoothAt.smoothWithinAt (hf : SmoothAt I I' f x) : SmoothWithinAt I I' f s x :=
  ContMDiffAt.contMDiffWithinAt hf

theorem ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : t ⊆ s) : ContMDiffOn I I' n f t :=
  fun x hx => (hf x (hts hx)).mono hts

theorem ContMDiff.contMDiffOn (hf : ContMDiff I I' n f) : ContMDiffOn I I' n f s := fun x _ =>
  (hf x).contMDiffWithinAt

theorem Smooth.smoothOn (hf : Smooth I I' f) : SmoothOn I I' f s :=
  ContMDiff.contMDiffOn hf

theorem contMDiffWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    ContMDiffWithinAt I I' n f (s ∩ t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_inter' ht

theorem contMDiffWithinAt_inter (ht : t ∈ 𝓝 x) :
    ContMDiffWithinAt I I' n f (s ∩ t) x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_inter ht

theorem ContMDiffWithinAt.contMDiffAt (h : ContMDiffWithinAt I I' n f s x) (ht : s ∈ 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropAt_of_liftPropWithinAt h ht

theorem SmoothWithinAt.smoothAt (h : SmoothWithinAt I I' f s x) (ht : s ∈ 𝓝 x) :
    SmoothAt I I' f x :=
  ContMDiffWithinAt.contMDiffAt h ht

theorem ContMDiffOn.contMDiffAt (h : ContMDiffOn I I' n f s) (hx : s ∈ 𝓝 x) :
    ContMDiffAt I I' n f x :=
  (h x (mem_of_mem_nhds hx)).contMDiffAt hx

theorem SmoothOn.smoothAt (h : SmoothOn I I' f s) (hx : s ∈ 𝓝 x) : SmoothAt I I' f x :=
  h.contMDiffAt hx

theorem contMDiffOn_iff_source_of_mem_maximalAtlas (he : e ∈ maximalAtlas I M) (hs : s ⊆ e.source) :
    ContMDiffOn I I' n f s ↔
      ContMDiffOn 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContMDiffOn, Set.forall_mem_image]
  refine forall₂_congr fun x hx => ?_
  rw [contMDiffWithinAt_iff_source_of_mem_maximalAtlas he (hs hx)]
  apply contMDiffWithinAt_congr_nhds
  simp_rw [nhdsWithin_eq_iff_eventuallyEq,
    e.extend_symm_preimage_inter_range_eventuallyEq I hs (hs hx)]

-- Porting note: didn't compile; fixed by golfing the proof and moving parts to lemmas
/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem contMDiffWithinAt_iff_contMDiffOn_nhds {n : ℕ} :
    ContMDiffWithinAt I I' n f s x ↔ ∃ u ∈ 𝓝[insert x s] x, ContMDiffOn I I' n f u := by
  -- WLOG, `x ∈ s`, otherwise we add `x` to `s`
  wlog hxs : x ∈ s generalizing s
  rw [← contMDiffWithinAt_insert_self, this (mem_insert _ _), insert_idem]
  rw [insert_eq_of_mem hxs]
  -- The `←` implication is trivial
  refine ⟨fun h ↦ ?_, fun ⟨u, hmem, hu⟩ ↦ (hu _ (mem_of_mem_nhdsWithin hxs hmem)).mono_of_mem hmem⟩
  -- The property is true in charts. Let `v` be a good neighborhood in the chart where the function
  -- is smooth.
  rcases (contMDiffWithinAt_iff'.1 h).2.contDiffOn le_rfl with ⟨v, hmem, hsub, hv⟩
  have hxs' : extChartAt I x x ∈ (extChartAt I x).target ∩
      (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source) :=
    ⟨(extChartAt I x).map_source (mem_extChartAt_source _ _), by rwa [extChartAt_to_inv], by
      rw [extChartAt_to_inv]; apply mem_extChartAt_source⟩
  rw [insert_eq_of_mem hxs'] at hmem hsub
  -- Then `(extChartAt I x).symm '' v` is the neighborhood we are looking for.
  refine ⟨(extChartAt I x).symm '' v, ?_, ?_⟩
  rw [← map_extChartAt_symm_nhdsWithin I,
    h.1.nhdsWithin_extChartAt_symm_preimage_inter_range I I']
  exact image_mem_map hmem
  have hv₁ : (extChartAt I x).symm '' v ⊆ (extChartAt I x).source :=
    image_subset_iff.2 fun y hy ↦ (extChartAt I x).map_target (hsub hy).1
  have hv₂ : MapsTo f ((extChartAt I x).symm '' v) (extChartAt I' (f x)).source := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hsub hy).2.2
  rwa [contMDiffOn_iff_of_subset_source' hv₁ hv₂, PartialEquiv.image_symm_image_of_subset_target]
  exact hsub.trans inter_subset_left

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
theorem contMDiffAt_iff_contMDiffOn_nhds {n : ℕ} :
    ContMDiffAt I I' n f x ↔ ∃ u ∈ 𝓝 x, ContMDiffOn I I' n f u := by
  simp [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_contMDiffOn_nhds, nhdsWithin_univ]

/-- Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for every `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`. -/
theorem contMDiffAt_iff_contMDiffAt_nhds {n : ℕ} :
    ContMDiffAt I I' n f x ↔ ∀ᶠ x' in 𝓝 x, ContMDiffAt I I' n f x' := by
  refine ⟨?_, fun h => h.self_of_nhds⟩
  rw [contMDiffAt_iff_contMDiffOn_nhds]
  rintro ⟨u, hu, h⟩
  refine (eventually_mem_nhds.mpr hu).mono fun x' hx' => ?_
  exact (h x' <| mem_of_mem_nhds hx').contMDiffAt hx'

/-! ### Congruence lemmas -/

theorem ContMDiffWithinAt.congr (h : ContMDiffWithinAt I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_congr h h₁ hx

theorem contMDiffWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_congr_iff h₁ hx

theorem ContMDiffWithinAt.congr_of_eventuallyEq (h : ContMDiffWithinAt I I' n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContMDiffWithinAt I I' n f₁ s x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_congr_of_eventuallyEq h h₁ hx

theorem Filter.EventuallyEq.contMDiffWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContMDiffWithinAt I I' n f₁ s x ↔ ContMDiffWithinAt I I' n f s x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

theorem ContMDiffAt.congr_of_eventuallyEq (h : ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropAt_congr_of_eventuallyEq h h₁

theorem Filter.EventuallyEq.contMDiffAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    ContMDiffAt I I' n f₁ x ↔ ContMDiffAt I I' n f x :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropAt_congr_iff_of_eventuallyEq h₁

theorem ContMDiffOn.congr (h : ContMDiffOn I I' n f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropOn_congr h h₁

theorem contMDiffOn_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
    ContMDiffOn I I' n f₁ s ↔ ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropOn_congr_iff h₁

theorem ContMDiffOn.congr_mono (hf : ContMDiffOn I I' n f s) (h₁ : ∀ y ∈ s₁, f₁ y = f y)
    (hs : s₁ ⊆ s) : ContMDiffOn I I' n f₁ s₁ :=
  (hf.mono hs).congr h₁

/-! ### Locality -/


/-- Being `C^n` is a local property. -/
theorem contMDiffOn_of_locally_contMDiffOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' n f (s ∩ u)) : ContMDiffOn I I' n f s :=
  (contDiffWithinAt_localInvariantProp I I' n).liftPropOn_of_locally_liftPropOn h

theorem contMDiff_of_locally_contMDiffOn (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ ContMDiffOn I I' n f u) :
    ContMDiff I I' n f :=
  (contDiffWithinAt_localInvariantProp I I' n).liftProp_of_locally_liftPropOn h
