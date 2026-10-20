/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic.Set
import all Mathlib.Tactic.Set
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable.ApproximableMap

@[expose] public section

/-!
# Lecture II (§2) — approximable mappings: Definitions 2.1, 2.2 and Theorems 2.5–2.7

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19 (1981), Lecture II,
*Approximable mappings*. A mapping of domains that "preserves the spirit of approximation" is given
not by a function on ideal elements but by a **relation between neighbourhoods**: `X f Y` reads "if
the input is approximated at least as well as by `X`, then the output is approximated at least as
well as by `Y`."

This file formalizes the §2 core:

* **Definition 2.1** — `ApproximableMap V₀ V₁`: a relation `f ⊆ 𝒟₀ × 𝒟₁` with
  (i) `Δ₀ f Δ₁` (`master_rel`),
  (ii) `X f Y → X f Y' → X f (Y ∩ Y')` (`inter_right`, the consistency/intersectivity condition),
  (iii) `X f Y → X' ⊆ X → Y ⊆ Y' → X' f Y'` (`mono`, monotonicity: sharper input, blunter output).
  We carry `rel_dom`/`rel_cod` recording `f ⊆ 𝒟₀ × 𝒟₁`.
* **Proposition 2.2** — every approximable mapping determines an elementwise function
  `toElementMap f : |𝒟₀| → |𝒟₁|`, `f(x) = {Y ∣ ∃ X ∈ x, X f Y}`, which is a filter (i)–(iii) are
  *all* used); the relation is recovered by `rel_iff_mem_principal` (`X f Y ↔ Y ∈ f(↑X)`); the map
  is monotone (`toElementMap_mono`); and two approximable maps are equal iff they induce the same
  elementwise map (`ext_of_toElementMap`).
* **Theorem 2.5** — neighbourhood systems and approximable maps form a **category**: identity
  `idMap` (`X I_D Y ↔ X ⊆ Y`), composition `comp g f` (`X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`), with the
  identity laws `idMap_comp`/`comp_idMap` and associativity `comp_assoc`.
* **Proposition 2.6** — the elementwise action is a **functor** to sets and functions:
  `toElementMap_idMap` (`I_D(x) = x`) and `toElementMap_comp` (`(g∘f)(x) = g(f(x))`).
* **Theorem 2.7** — every domain **isomorphism** `e : |𝒟₀| ≃o |𝒟₁|` (Definition 1.9) comes from an
  approximable map: `ofIso e` with `toElementMap_ofIso` (`(ofIso e)(x) = e(x)`), packaged as
  `exists_approximable_of_iso`; moreover `e` carries finite (principal) elements to finite elements
  (`exists_principal_eq_apply_principal`), via the directed-union construction `sSupDirected`.

Everything in this file is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`); the only
classical lemma is `ext_of_toElementMap`, which decides neighbourhood membership by `by_cases`
(`Classical.em`). -/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem

/-- **Directed union of filters.** The union `⋃ S = {Z ∣ ∃ s ∈ S, Z ∈ s}` of a *non-empty directed*
family `S` of elements (any two members have an upper bound in `S`) is again an element. The only
non-trivial law is `inter_mem`: given `Z ∈ a` and `Z' ∈ b`, an upper bound `c ⊇ a, b` contains both,
hence `Z ∩ Z' ∈ c`. (Generalizes `chainUnion` of Exercise 1.24 from chains to directed sets; this is
the construction behind Exercise 2.11 and Scott's finiteness argument in Theorem 2.7.) -/
def sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) : V.Element where
  mem Z := ∃ s ∈ S, s.mem Z
  sub := fun ⟨s, _, hs⟩ => s.sub hs
  master_mem := by obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, s.master_mem⟩
  inter_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ ⟨b, hbS, hbZ⟩
    obtain ⟨c, hcS, hac, hbc⟩ := hdir a haS b hbS
    exact ⟨c, hcS, c.inter_mem (hac Z haZ) (hbc Z' hbZ)⟩
  up_mem := by
    rintro Z Z' ⟨a, haS, haZ⟩ hZ' hZZ'
    exact ⟨a, haS, a.up_mem haZ hZ' hZZ'⟩

end NeighborhoodSystem


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Extensionality for the relation.** Two approximable maps with the same neighbourhood relation
are equal (the remaining fields are propositions). -/
theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

/-- **Proposition 2.2(i) (Scott 1981, PRG-19).** The elementwise function determined by an
approximable mapping: `f(x) = {Y ∈ 𝒟₁ ∣ ∃ X ∈ x, X f Y}`. The four filter laws use *all* of
Definition 2.1: `master_mem` uses (i); `inter_mem` uses (ii) together with (iii) (to pull both
outputs back along the common input `X ∩ X'`); `up_mem` uses (iii). -/
def toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) : V₁.Element where
  mem Y := ∃ X, x.mem X ∧ f.rel X Y
  sub := fun ⟨_, _, hXY⟩ => f.rel_cod hXY
  master_mem := ⟨V₀.master, x.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ ⟨X', hX', hX'Y'⟩
    have hXX'mem : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hXX'mem
    refine ⟨X ∩ X', hXX'mem, ?_⟩
    have h1 : f.rel (X ∩ X') Y :=
      f.mono hXY Set.inter_subset_left subset_rfl hXX' (f.rel_cod hXY)
    have h2 : f.rel (X ∩ X') Y' :=
      f.mono hX'Y' Set.inter_subset_right subset_rfl hXX' (f.rel_cod hX'Y')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Y Y' ⟨X, hX, hXY⟩ hY' hYY'
    exact ⟨X, hX, f.mono hXY subset_rfl hYY' (x.sub hX) hY'⟩

@[simp] theorem mem_toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔ ∃ X, x.mem X ∧ f.rel X Y := Iff.rfl

/-! ### Theorem 2.5 — the category of neighbourhood systems and approximable mappings. -/

/-- **Theorem 2.5(i) (Scott 1981, PRG-19) — the identity mapping `I_D`.** `X I_D Y ↔ X ⊆ Y`
(confined to `𝒟 × 𝒟`). It is approximable: (i) `Δ ⊆ Δ`; (ii) `X ⊆ Y`, `X ⊆ Y'` give `X ⊆ Y ∩ Y'`
with witness `X`; (iii) is transitivity `X' ⊆ X ⊆ Y ⊆ Y'`. -/
def idMap (V : NeighborhoodSystem α) : ApproximableMap V V where
  rel X Y := V.mem X ∧ V.mem Y ∧ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, V.master_mem, subset_rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, V.inter_mem hY hY' hX (Set.subset_inter hXY hXY'), Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

@[simp] theorem idMap_rel {V : NeighborhoodSystem α} {X Y : Set α} :
    (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **Theorem 2.5(ii) (Scott 1981, PRG-19) — composition `g ∘ f`.** `X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`.
Approximability is Scott's verification: (i) use `Y = Δ₁`; (ii) intersect both witnesses via
`f.inter_right` then `g.inter_right` (narrowing the inner neighbourhood with `g.mono`); (iii) narrow
the input with `f.mono` and widen the output with `g.mono`, keeping the same witness. -/
def comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₂ where
  rel X Z := ∃ Y, f.rel X Y ∧ g.rel Y Z
  rel_dom := fun ⟨_, hXY, _⟩ => f.rel_dom hXY
  rel_cod := fun ⟨_, _, hYZ⟩ => g.rel_cod hYZ
  master_rel := ⟨V₁.master, f.master_rel, g.master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨Y, hXY, hYZ⟩ ⟨Y', hXY', hY'Z'⟩
    refine ⟨Y ∩ Y', f.inter_right hXY hXY', ?_⟩
    have hYY'mem : V₁.mem (Y ∩ Y') := f.rel_cod (f.inter_right hXY hXY')
    have h1 : g.rel (Y ∩ Y') Z :=
      g.mono hYZ Set.inter_subset_left subset_rfl hYY'mem (g.rel_cod hYZ)
    have h2 : g.rel (Y ∩ Y') Z' :=
      g.mono hY'Z' Set.inter_subset_right subset_rfl hYY'mem (g.rel_cod hY'Z')
    exact g.inter_right h1 h2
  mono := by
    rintro X X' Z Z' ⟨Y, hXY, hYZ⟩ hX'X hZZ' hX' hZ'
    refine ⟨Y, f.mono hXY hX'X subset_rfl hX' (f.rel_cod hXY), ?_⟩
    exact g.mono hYZ subset_rfl hZZ' (g.rel_dom hYZ) hZ'

@[simp] theorem comp_rel {g : ApproximableMap V₁ V₂} {f : ApproximableMap V₀ V₁} {X : Set α}
    {Z : Set γ} : (g.comp f).rel X Z ↔ ∃ Y, f.rel X Y ∧ g.rel Y Z := Iff.rfl

/-! ### Proposition 2.6 — the functor to sets and functions. -/

@[simp] theorem toElementMap_idMap (x : V₀.Element) : (idMap V₀).toElementMap x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXx, _, hY, hXY⟩
    exact x.up_mem hXx hY hXY
  · intro hY
    exact ⟨Y, hY, x.sub hY, x.sub hY, subset_rfl⟩

/-! ### Theorem 2.7 — every domain isomorphism comes from an approximable mapping. -/

/-- **Theorem 2.7 (Scott 1981, PRG-19) — the approximable map of an isomorphism.** Given a domain
isomorphism `e : |𝒟₀| ≃o |𝒟₁|` (Definition 1.9), Scott's "only way to define a neighbourhood
mapping" is the relation `X f Y ↔ Y ∈ e(↑X)`. The conditions of 2.1 hold because `e` is monotone:
(i) `Δ₁ ∈ e(⊥₀)` is `master_mem`; (ii) is `inter_mem` of the filter `e(↑X)`; (iii) sharpening `X' ⊆ X`
means `↑X ⊑ ↑X'`, so `e(↑X) ⊑ e(↑X')` and the output transports along, then widens by `up_mem`. -/
def ofIso (e : V₀.Element ≃o V₁.Element) : ApproximableMap V₀ V₁ where
  rel X Y := ∃ _ : V₀.mem X, (e (V₀.principal ‹V₀.mem X›)).mem Y
  rel_dom := fun h => h.1
  rel_cod := fun h => (e _).sub h.2
  master_rel := ⟨V₀.master_mem, (e _).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (e (V₀.principal hX)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', ?_⟩
    have hle : V₀.principal hX ≤ V₀.principal hX' := (V₀.principal_le_iff hX hX').mpr hX'X
    have hmem : (e (V₀.principal hX')).mem Y := (e.monotone hle) Y hY
    exact (e (V₀.principal hX')).up_mem hmem hY' hYY'
end ApproximableMap
end DomainTheory.NeighbourhoodSystems
