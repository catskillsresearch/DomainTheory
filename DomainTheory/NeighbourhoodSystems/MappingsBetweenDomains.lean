module


public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Image
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Order.Directed
public import Mathlib.Tactic.Set


@[expose] public section

section
-- Approximable/ApproximableMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

/-- **Definition 2.1 (Scott 1981, PRG-19).** An *approximable mapping* `f : 𝒟₀ → 𝒟₁` is a relation
`rel` between neighbourhoods (`rel X Y`, Scott's `X f Y`) confined to `𝒟₀ × 𝒟₁` and satisfying
Scott's three conditions:

* (i)   `Δ₀ f Δ₁`                                   — `master_rel`;
* (ii)  `X f Y` and `X f Y'` imply `X f (Y ∩ Y')`   — `inter_right`;
* (iii) `X f Y`, `X' ⊆ X`, `Y ⊆ Y'` imply `X' f Y'` — `mono` (the targets `X'`, `Y'` must be
  neighbourhoods, as Scott's relation lives on `𝒟₀ × 𝒟₁`). -/
structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where
  /-- The underlying neighbourhood relation `X f Y`. -/
  rel : Set α → Set β → Prop
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (domain side): related inputs are neighbourhoods. -/
  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X
  /-- `f ⊆ 𝒟₀ × 𝒟₁` (codomain side): related outputs are neighbourhoods. -/
  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y
  /-- (i) `Δ₀ f Δ₁`. -/
  master_rel : rel V₀.master V₁.master
  /-- (ii) intersectivity on the output: `X f Y → X f Y' → X f (Y ∩ Y')`. -/
  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')
  /-- (iii) monotonicity: a sharper input `X' ⊆ X` with a blunter output `Y ⊆ Y'` is still related,
  provided `X'`, `Y'` are neighbourhoods. -/
  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/ext.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Extensionality for the relation.** Two approximable maps with the same neighbourhood relation
are equal (the remaining fields are propositions). -/
theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/sSupDirected.lean
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

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

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

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/mem_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

@[simp] theorem mem_toElementMap (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔ ∃ X, x.mem X ∧ f.rel X Y := Iff.rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/idMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

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

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/idMap_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

@[simp] theorem idMap_rel {V : NeighborhoodSystem α} {X Y : Set α} :
    (idMap V).rel X Y ↔ V.mem X ∧ V.mem Y ∧ X ⊆ Y := Iff.rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/comp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

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

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/comp_rel.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

@[simp] theorem comp_rel {g : ApproximableMap V₁ V₂} {f : ApproximableMap V₀ V₁} {X : Set α}
    {Z : Set γ} : (g.comp f).rel X Z ↔ ∃ Y, f.rel X Y ∧ g.rel Y Z := Iff.rfl

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/toElementMap_idMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

@[simp] theorem toElementMap_idMap (x : V₀.Element) : (idMap V₀).toElementMap x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXx, _, hY, hXY⟩
    exact x.up_mem hXx hY hXY
  · intro hY
    exact ⟨Y, hY, x.sub hY, x.sub hY, subset_rfl⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/ofIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

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
end

section
-- Approximable/comp_assoc.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.5 — associativity.** `h ∘ (g ∘ f) = (h ∘ g) ∘ f`. Pure reassociation of the
existential witnesses. -/
theorem comp_assoc {V₃ : NeighborhoodSystem δ} (h : ApproximableMap V₂ V₃)
    (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨Y, hXY, Z, hYZ, hZW⟩
    exact ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
  · rintro ⟨Z, ⟨Y, hXY, hYZ⟩, hZW⟩
    exact ⟨Y, hXY, Z, hYZ, hZW⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/comp_idMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.5 — right identity law.** `f ∘ I_{D₀} = f`. (`→`: a witness `X ⊆ Y` sharpens the
input of `f` by `f.mono`; `←`: take `Y = X`.) -/
theorem comp_idMap (f : ApproximableMap V₀ V₁) : f.comp (idMap V₀) = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, hYZ⟩
    exact f.mono hYZ hXY subset_rfl hX (f.rel_cod hYZ)
  · intro hXZ
    exact ⟨X, ⟨f.rel_dom hXZ, f.rel_dom hXZ, subset_rfl⟩, hXZ⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/idMap_comp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.5 — left identity law.** `I_{D₁} ∘ f = f`. (`→`: a witness `Y ⊆ Z` widens the output
of `f` by `f.mono`; `←`: take `Y = Z`.) -/
theorem idMap_comp (f : ApproximableMap V₀ V₁) : (idMap V₁).comp f = f := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, hXY, _, hZ, hYZ⟩
    exact f.mono hXY subset_rfl hYZ (f.rel_dom hXY) hZ
  · intro hXZ
    exact ⟨Z, hXZ, f.rel_cod hXZ, f.rel_cod hXZ, subset_rfl⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/le_sSupDirected.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem


/-- Each member of a directed family approximates the directed union. -/
theorem le_sSupDirected (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {a : V.Element} (ha : a ∈ S) :
    a ≤ V.sSupDirected S hne hdir :=
  fun _ hZ => ⟨a, ha, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/rel_iff_mem_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Proposition 2.2(ii) (Scott 1981, PRG-19).** The relation is recovered from the elementwise
map: for `X ∈ 𝒟₀`, `X f Y ↔ Y ∈ f(↑X)`. (`→` since `X ∈ ↑X`; `←` since any `Z ∈ ↑X` has `X ⊆ Z`,
so `Z f Y` monotonically yields `X f Y`.) -/
theorem rel_iff_mem_principal (f : ApproximableMap V₀ V₁) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    f.rel X Y ↔ (f.toElementMap (V₀.principal hX)).mem Y := by
  constructor
  · intro hXY
    exact ⟨X, ⟨hX, subset_rfl⟩, hXY⟩
  · rintro ⟨Z, ⟨_, hXZ⟩, hZY⟩
    exact f.mono hZY hXZ subset_rfl hX (f.rel_cod hZY)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/ext_of_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Proposition 2.2(iv) (Scott 1981, PRG-19).** Two approximable maps are *identical as relations*
iff they induce the same elementwise function: `(∀ x, f(x) = g(x)) ⟹ f = g`. For neighbourhoods `X`
the relation is read off `f(↑X)` (`rel_iff_mem_principal`); off `𝒟₀` both relations are empty. -/
theorem ext_of_toElementMap {f g : ApproximableMap V₀ V₁}
    (h : ∀ x, f.toElementMap x = g.toElementMap x) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/sSupDirected_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}

namespace NeighborhoodSystem


/-- The directed union is the least upper bound: an upper bound of every member dominates it. -/
theorem sSupDirected_le (V : NeighborhoodSystem α) (S : Set V.Element) (hne : S.Nonempty)
    (hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c) {y : V.Element}
    (hy : ∀ s ∈ S, s ≤ y) : V.sSupDirected S hne hdir ≤ y := by
  rintro Z ⟨s, hs, hsZ⟩
  exact hy s hs Z hsZ

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/exists_principal_eq_apply_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.7 (Scott 1981, PRG-19) — finite elements go to finite elements.** A domain
isomorphism `e` carries the finite (principal) element `↑X` to a finite element `↑Y` of the other
domain. Following Scott: with `w = e(↑X)`, the set `S = {e⁻¹(↑Y) ∣ Y ∈ w}` is directed (intersections
of members of `w` give upper bounds), so its union `z = ⋃ S` is an element (`sSupDirected`). One shows
`z = ↑X` (each `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`, and conversely `w ⊑ e(z)` forces `↑X = e⁻¹(w) ⊑ z`); then
`X ∈ z` lands in some `e⁻¹(↑Y)`, giving `w ⊑ ↑Y`, while `↑Y ⊑ w` is automatic — so `w = ↑Y`. -/
theorem exists_principal_eq_apply_principal (e : V₀.Element ≃o V₁.Element)
    {X : Set α} (hX : V₀.mem X) :
    ∃ (Y : Set β) (hY : V₁.mem Y), e (V₀.principal hX) = V₁.principal hY := by
  -- `w = e(↑X)`, and the directed family `S` of inverse images of principals of members of `w`.
  set w : V₁.Element := e (V₀.principal hX) with hw
  set S : Set V₀.Element :=
    {z | ∃ (Y : Set β) (hY : V₁.mem Y), w.mem Y ∧ z = e.symm (V₁.principal hY)} with hS
  -- `e⁻¹(w) = ↑X`.
  have hsymm_w : e.symm w = V₀.principal hX := by rw [hw, e.symm_apply_apply]
  -- For `Y ∈ w`, `↑Y ⊑ w`.
  have hprin_le_w : ∀ {Y : Set β} (hY : V₁.mem Y), w.mem Y → V₁.principal hY ≤ w :=
    fun hY hYw Z hZ => w.up_mem hYw hZ.1 hZ.2
  -- `S` is non-empty (use `Y = Δ₁`).
  have hne : S.Nonempty :=
    ⟨e.symm (V₁.principal V₁.master_mem), V₁.master, V₁.master_mem, w.master_mem, rfl⟩
  -- `S` is directed: intersect the two members of `w`.
  have hdir : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, a ≤ c ∧ b ≤ c := by
    rintro a ⟨Y, hY, hYw, rfl⟩ b ⟨Y', hY', hY'w, rfl⟩
    have hYY'w : w.mem (Y ∩ Y') := w.inter_mem hYw hY'w
    have hYY' : V₁.mem (Y ∩ Y') := w.sub hYY'w
    refine ⟨e.symm (V₁.principal hYY'), ⟨Y ∩ Y', hYY', hYY'w, rfl⟩, ?_, ?_⟩
    · exact e.symm.monotone ((V₁.principal_le_iff hY hYY').mpr Set.inter_subset_left)
    · exact e.symm.monotone ((V₁.principal_le_iff hY' hYY').mpr Set.inter_subset_right)
  -- The directed union `z = ⋃ S`.
  set z : V₀.Element := V₀.sSupDirected S hne hdir with hz
  -- `z ⊑ ↑X`: every member `e⁻¹(↑Y) ⊑ e⁻¹(w) = ↑X`.
  have hz_le : z ≤ V₀.principal hX := by
    apply V₀.sSupDirected_le
    rintro s ⟨Y, hY, hYw, rfl⟩
    have : e.symm (V₁.principal hY) ≤ e.symm w := e.symm.monotone (hprin_le_w hY hYw)
    rwa [hsymm_w] at this
  -- `↑X ⊑ z`: show `w ⊑ e(z)`, then `↑X = e⁻¹(w) ⊑ z`.
  have hw_le_ez : w ≤ e z := by
    intro Y hYw
    have hY : V₁.mem Y := w.sub hYw
    have hmem_S : e.symm (V₁.principal hY) ∈ S := ⟨Y, hY, hYw, rfl⟩
    have h1 : e.symm (V₁.principal hY) ≤ z := V₀.le_sSupDirected S hne hdir hmem_S
    have h2 : V₁.principal hY ≤ e z := by
      have := e.monotone h1
      rwa [e.apply_symm_apply] at this
    exact h2 Y ⟨hY, subset_rfl⟩
  have hX_le_z : V₀.principal hX ≤ z := by
    have : e.symm w ≤ e.symm (e z) := e.symm.monotone hw_le_ez
    rwa [hsymm_w, e.symm_apply_apply] at this
  -- Hence `z = ↑X`, so `X ∈ z` lands in some member `e⁻¹(↑Y)`.
  have hz_eq : z = V₀.principal hX := le_antisymm hz_le hX_le_z
  have hXz : z.mem X := hz_eq ▸ ⟨hX, subset_rfl⟩
  obtain ⟨s, ⟨Y, hY, hYw, rfl⟩, hXs⟩ := hXz
  -- `↑X ⊑ e⁻¹(↑Y)` (it contains `X`), so `w = e(↑X) ⊑ ↑Y`; with `↑Y ⊑ w` we get `w = ↑Y`.
  refine ⟨Y, hY, ?_⟩
  have hprinX_le : V₀.principal hX ≤ e.symm (V₁.principal hY) :=
    fun Z hZ => (e.symm (V₁.principal hY)).up_mem hXs hZ.1 hZ.2
  have hw_le_prinY : w ≤ V₁.principal hY := by
    have := e.monotone hprinX_le
    rw [e.apply_symm_apply] at this
    rwa [← hw] at this
  exact le_antisymm hw_le_prinY (hprin_le_w hY hYw)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/toElementMap_comp.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Proposition 2.6(ii) (Scott 1981, PRG-19).** Composition of approximable mappings becomes
composition of the elementwise functions: `(g ∘ f)(x) = g(f(x))`. Both sides unfold to
`∃ Y X, x.mem X ∧ X f Y ∧ Y g Z`; the proof is a reassociation of existentials. -/
theorem toElementMap_comp (g : ApproximableMap V₁ V₂) (f : ApproximableMap V₀ V₁) (x : V₀.Element) :
    (g.comp f).toElementMap x = g.toElementMap (f.toElementMap x) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, hXx, Y, hXY, hYZ⟩
    exact ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
  · rintro ⟨Y, ⟨X, hXx, hXY⟩, hYZ⟩
    exact ⟨X, hXx, Y, hXY, hYZ⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/toElementMap_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Proposition 2.2(iii) (Scott 1981, PRG-19).** Approximable maps are monotone on elements:
`x ⊑ y ⟹ f(x) ⊑ f(y)`. -/
theorem toElementMap_mono (f : ApproximableMap V₀ V₁) {x y : V₀.Element} (hxy : x ≤ y) :
    f.toElementMap x ≤ f.toElementMap y := by
  rintro Y ⟨X, hX, hXY⟩
  exact ⟨X, hxy X hX, hXY⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/toElementMap_ofIso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.7 — the relation re-defines the function.** The elementwise map of `ofIso e` is `e`
itself: `(ofIso e)(x) = e(x)` for every `x`. The forward inclusion uses that `X ∈ x` implies
`↑X ⊑ x`, hence `e(↑X) ⊑ e(x)`; the reverse uses surjectivity of `e` (via `e.symm`) exactly as in
Scott's proof — one shows `x = e⁻¹((ofIso e)(x))` by antisymmetry. -/
theorem toElementMap_ofIso (e : V₀.Element ≃o V₁.Element) (x : V₀.Element) :
    (ofIso e).toElementMap x = e x := by
  have hgxle : (ofIso e).toElementMap x ≤ e x := by
    rintro Y ⟨X, hXx, hX, hY⟩
    have hpx : V₀.principal hX ≤ x := fun Z hZ => x.up_mem hXx hZ.1 hZ.2
    exact (e.monotone hpx) Y hY
  have key : x = e.symm ((ofIso e).toElementMap x) := by
    apply le_antisymm
    · intro X hXx
      have hX : V₀.mem X := x.sub hXx
      have hsub : e (V₀.principal hX) ≤ (ofIso e).toElementMap x :=
        fun Y hY => ⟨X, hXx, hX, hY⟩
      have hple : V₀.principal hX ≤ e.symm ((ofIso e).toElementMap x) := by
        have h := e.symm.monotone hsub
        rwa [e.symm_apply_apply] at h
      exact hple X ⟨hX, subset_rfl⟩
    · have h := e.symm.monotone hgxle
      rwa [e.symm_apply_apply] at h
  have h1 : e x = e (e.symm ((ofIso e).toElementMap x)) := congrArg e key
  rw [e.apply_symm_apply] at h1
  exact h1.symm

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Approximable/exists_approximable_of_iso.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Theorem 2.7 (statement) (Scott 1981, PRG-19).** "Every isomorphism between domains results from
an approximable mapping." For any domain isomorphism `e`, there is an approximable mapping whose
elementwise action is exactly `e`. -/
theorem exists_approximable_of_iso (e : V₀.Element ≃o V₁.Element) :
    ∃ f : ApproximableMap V₀ V₁, ∀ x, f.toElementMap x = e x :=
  ⟨ofIso e, toElementMap_ofIso e⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/ApproximableMap₂.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

/-- **Exercise 2.19 (Scott 1981, PRG-19).** An *approximable mapping of two variables*
`f : 𝒟₀ × 𝒟₁ → 𝒟₂` is a ternary relation `X, Y f Z` confined to `𝒟₀ × 𝒟₁ × 𝒟₂` with the natural
generalization of Definition 2.1: (i) `Δ₀, Δ₁ f Δ₂`; (ii) intersectivity on the output; (iii)
monotonicity jointly in both inputs (sharper) and the output (blunter). -/
structure ApproximableMap₂ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) where
  /-- The underlying ternary relation `X, Y f Z`. -/
  rel : Set α → Set β → Set γ → Prop
  rel_dom₀ : ∀ {X Y Z}, rel X Y Z → V₀.mem X
  rel_dom₁ : ∀ {X Y Z}, rel X Y Z → V₁.mem Y
  rel_cod : ∀ {X Y Z}, rel X Y Z → V₂.mem Z
  /-- (i) `Δ₀, Δ₁ f Δ₂`. -/
  master_rel : rel V₀.master V₁.master V₂.master
  /-- (ii) intersectivity on the output. -/
  inter_right : ∀ {X Y Z Z'}, rel X Y Z → rel X Y Z' → rel X Y (Z ∩ Z')
  /-- (iii) joint monotonicity: sharper inputs `X' ⊆ X`, `Y' ⊆ Y`; blunter output `Z ⊆ Z'`. -/
  mono : ∀ {X X' Y Y' Z Z'}, rel X Y Z → X' ⊆ X → Y' ⊆ Y → Z ⊆ Z' →
    V₀.mem X' → V₁.mem Y' → V₂.mem Z' → rel X' Y' Z'

end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/iSupDirected.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem

/-- **Exercise 2.11 — directed union (indexed form).** For a directed family `a : I → |𝒟|` (any two
`a i, a j` have a common upper bound `a k`), the union `⋃ᵢ a i` is again an element of `|𝒟|`. Built
on `sSupDirected` over the range. -/
def iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) : V.Element :=
  V.sSupDirected (Set.range a) (Set.range_nonempty a) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨a k, ⟨k, rfl⟩, hik, hjk⟩)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/iSupMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.12 (Scott 1981, PRG-19).** The pointwise union of a *directed* family of approximable
maps is approximable. Directedness is stated on the relations: any two `f i, f j` are dominated by
some `f k`. The union relation is `X g Z ↔ ∃ i, X (f i) Z`. -/
def iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) : ApproximableMap V₀ V₁ where
  rel X Z := ∃ i, (f i).rel X Z
  rel_dom := fun ⟨i, h⟩ => (f i).rel_dom h
  rel_cod := fun ⟨i, h⟩ => (f i).rel_cod h
  master_rel := by obtain ⟨i⟩ := (inferInstance : Nonempty I); exact ⟨i, (f i).master_rel⟩
  inter_right := by
    rintro X Z Z' ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, (f k).inter_right (hik X Z hi) (hjk X Z' hj)⟩
  mono := by
    rintro X X' Z Z' ⟨i, hi⟩ hX'X hZZ' hX' hZ'
    exact ⟨i, (f i).mono hi hX'X hZZ' hX' hZ'⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/interMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.10 (Scott 1981, PRG-19).** The pointwise **intersection** `h` of two approximable
maps: `X h Z ↔ X f Z ∧ X g Z`. It is approximable, and (`mem_toElementMap_interMap`)
`h(x) = f(x) ∩ g(x)`. -/
def interMap (f g : ApproximableMap V₀ V₁) : ApproximableMap V₀ V₁ where
  rel X Z := f.rel X Z ∧ g.rel X Z
  rel_dom h := f.rel_dom h.1
  rel_cod h := f.rel_cod h.1
  master_rel := ⟨f.master_rel, g.master_rel⟩
  inter_right := fun ⟨hf, hg⟩ ⟨hf', hg'⟩ => ⟨f.inter_right hf hf', g.inter_right hg hg'⟩
  mono := fun ⟨hf, hg⟩ hX'X hZZ' hX' hZ' =>
    ⟨f.mono hf hX'X hZZ' hX' hZ', g.mono hg hX'X hZZ' hX' hZ'⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/ofMono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.8 (extension).** *Any* monotone function on finite elements comes from an
approximable map. Here a "monotone function on finite elements" is a map `m` sending each
neighbourhood `X` (a finite element `↑X`) to an element `m X hX : |𝒟₁|`, monotone in the sense
`X' ⊆ X → m X hX ≤ m X' hX'` (i.e. `↑X ⊑ ↑X' ⟹ m(↑X) ⊑ m(↑X')`). The induced relation is
`X f Y ↔ Y ∈ m(↑X)`. -/
def ofMono (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX') :
    ApproximableMap V₀ V₁ where
  rel X Y := ∃ hX : V₀.mem X, (m X hX).mem Y
  rel_dom := fun ⟨hX, _⟩ => hX
  rel_cod := fun ⟨hX, hY⟩ => (m _ hX).sub hY
  master_rel := ⟨V₀.master_mem, (m _ V₀.master_mem).master_mem⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY⟩ ⟨_, hY'⟩
    exact ⟨hX, (m X hX).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY⟩ hX'X hYY' hX' hY'
    have hle : m X hX ≤ m X' hX' := hmono X X' hX hX' hX'X
    exact ⟨hX', (m X' hX').up_mem (hle Y hY) hY' hYY'⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/toElementMap₂.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 2.19 (Proposition 2.2 analogue).** A two-variable approximable mapping determines an
elementwise function of two arguments: `f(x, y) = {Z ∣ ∃ X ∈ x, ∃ Y ∈ y, X, Y f Z}`. The filter
laws use all three conditions: `inter_mem` pulls both outputs back to `(X ∩ X', Y ∩ Y')` via `mono`
then `inter_right`. -/
def toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element) : V₂.Element where
  mem Z := ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z
  sub := fun ⟨_, _, _, _, hrel⟩ => f.rel_cod hrel
  master_mem := ⟨V₀.master, V₁.master, x.master_mem, y.master_mem, f.master_rel⟩
  inter_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ ⟨X', Y', hX', hY', hrel'⟩
    have hXX' : x.mem (X ∩ X') := x.inter_mem hX hX'
    have hYY' : y.mem (Y ∩ Y') := y.inter_mem hY hY'
    have hXX'm : V₀.mem (X ∩ X') := x.sub hXX'
    have hYY'm : V₁.mem (Y ∩ Y') := y.sub hYY'
    refine ⟨X ∩ X', Y ∩ Y', hXX', hYY', ?_⟩
    have h1 : f.rel (X ∩ X') (Y ∩ Y') Z :=
      f.mono hrel Set.inter_subset_left Set.inter_subset_left subset_rfl hXX'm hYY'm (f.rel_cod hrel)
    have h2 : f.rel (X ∩ X') (Y ∩ Y') Z' :=
      f.mono hrel' Set.inter_subset_right Set.inter_subset_right subset_rfl hXX'm hYY'm
        (f.rel_cod hrel')
    exact f.inter_right h1 h2
  up_mem := by
    rintro Z Z' ⟨X, Y, hX, hY, hrel⟩ hZ' hZZ'
    exact ⟨X, Y, hX, hY, f.mono hrel subset_rfl subset_rfl hZZ' (x.sub hX) (y.sub hY) hZ'⟩

end ApproximableMap₂

end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


end NeighborhoodSystem

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


end ApproximableMap


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


@[simp] theorem mem_toElementMap₂ (f : ApproximableMap₂ V₀ V₁ V₂) (x : V₀.Element) (y : V₁.Element)
    {Z : Set γ} : (f.toElementMap₂ x y).mem Z ↔ ∃ X Y, x.mem X ∧ y.mem Y ∧ f.rel X Y Z := Iff.rfl
end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/eq_of_toElementMap_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.8 (uniqueness).** An approximable mapping is *uniquely determined by its elementwise
effect on finite elements*: if `f(↑X) = g(↑X)` for every neighbourhood `X`, then `f = g`. (Off `𝒟₀`
both relations are empty; on `𝒟₀` use `rel_iff_mem_principal`.) -/
theorem eq_of_toElementMap_principal {f g : ApproximableMap V₀ V₁}
    (h : ∀ (X : Set α) (hX : V₀.mem X),
      f.toElementMap (V₀.principal hX) = g.toElementMap (V₀.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : V₀.mem X
  · rw [f.rel_iff_mem_principal hX, g.rel_iff_mem_principal hX, h X hX]
  · constructor
    · intro hr; exact absurd (f.rel_dom hr) hX
    · intro hr; exact absurd (g.rel_dom hr) hX

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/mem_iSupDirected.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem mem_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {Z : Set α} :
    (iSupDirected a hdir).mem Z ↔ ∃ i, (a i).mem Z := by
  constructor
  · rintro ⟨s, ⟨i, rfl⟩, hsZ⟩; exact ⟨i, hsZ⟩
  · rintro ⟨i, hi⟩; exact ⟨a i, ⟨i, rfl⟩, hi⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/iSupDirected_le.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem iSupDirected_le {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {y : V.Element}
    (hy : ∀ i, a i ≤ y) : iSupDirected a hdir ≤ y := by
  intro Z hZ
  obtain ⟨i, hi⟩ := (mem_iSupDirected a hdir).mp hZ
  exact hy i Z hi

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/le_iSupDirected.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem le_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) (i : I) :
    a i ≤ iSupDirected a hdir :=
  fun _ hZ => (mem_iSupDirected a hdir).mpr ⟨i, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/mem_toElementMap_iSupMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.12.** The induced elementwise map is the pointwise union: `g(x) = ⋃ᵢ f i (x)`. -/
theorem mem_toElementMap_iSupMap {I : Type*} [Nonempty I] (f : I → ApproximableMap V₀ V₁)
    (hdir : ∀ i j, ∃ k, (∀ X Y, (f i).rel X Y → (f k).rel X Y) ∧
      (∀ X Y, (f j).rel X Y → (f k).rel X Y)) (x : V₀.Element) {Y : Set β} :
    ((iSupMap f hdir).toElementMap x).mem Y ↔ ∃ i, ((f i).toElementMap x).mem Y := by
  constructor
  · rintro ⟨X, hxX, i, hrel⟩
    exact ⟨i, X, hxX, hrel⟩
  · rintro ⟨i, X, hxX, hrel⟩
    exact ⟨X, hxX, i, hrel⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/mem_toElementMap_interMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.10.** `h(x) = f(x) ∩ g(x)` (the meet in `|𝒟₁|`). The non-trivial direction combines
witnesses `X ∈ x` (for `f`) and `X' ∈ x` (for `g`) through `X ∩ X' ∈ x` using `mono`. -/
theorem mem_toElementMap_interMap (f g : ApproximableMap V₀ V₁) (x : V₀.Element) {Z : Set β} :
    ((interMap f g).toElementMap x).mem Z ↔
      (f.toElementMap x).mem Z ∧ (g.toElementMap x).mem Z := by
  constructor
  · rintro ⟨X, hxX, hf, hg⟩
    exact ⟨⟨X, hxX, hf⟩, ⟨X, hxX, hg⟩⟩
  · rintro ⟨⟨X, hxX, hf⟩, ⟨X', hxX', hg⟩⟩
    have hxXX' : x.mem (X ∩ X') := x.inter_mem hxX hxX'
    have hXX' : V₀.mem (X ∩ X') := x.sub hxXX'
    refine ⟨X ∩ X', hxXX', ?_, ?_⟩
    · exact f.mono hf Set.inter_subset_left subset_rfl hXX' (f.rel_cod hf)
    · exact g.mono hg Set.inter_subset_right subset_rfl hXX' (g.rel_cod hg)

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/relu2082_iff_mem_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.19 (recovery of the relation).** `X, Y f Z ↔ Z ∈ f(↑X, ↑Y)`, the two-variable
analogue of Proposition 2.2(ii). -/
theorem rel₂_iff_mem_principal (f : ApproximableMap₂ V₀ V₁ V₂) {X : Set α} (hX : V₀.mem X)
    {Y : Set β} (hY : V₁.mem Y) {Z : Set γ} :
    f.rel X Y Z ↔ (f.toElementMap₂ (V₀.principal hX) (V₁.principal hY)).mem Z := by
  constructor
  · intro hrel
    exact ⟨X, Y, ⟨hX, subset_rfl⟩, ⟨hY, subset_rfl⟩, hrel⟩
  · rintro ⟨X', Y', ⟨_, hXX'⟩, ⟨_, hYY'⟩, hrel⟩
    exact f.mono hrel hXX' hYY' subset_rfl hX hY (f.rel_cod hrel)

end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/toElementMap_iSupDirected.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.11 (Scott 1981, PRG-19).** Approximable mappings *preserve directed unions*:
`f(⋃ᵢ a i) = ⋃ᵢ f(a i)`. Both sides have member `Y` iff `∃ i X, X ∈ a i ∧ X f Y`. -/
theorem toElementMap_iSupDirected (f : ApproximableMap V₀ V₁) {I : Type*} [Nonempty I]
    (a : I → V₀.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) :
    f.toElementMap (NeighborhoodSystem.iSupDirected a hdir) =
      NeighborhoodSystem.iSupDirected (fun i => f.toElementMap (a i))
        (fun i j => by
          obtain ⟨k, hik, hjk⟩ := hdir i j
          exact ⟨k, f.toElementMap_mono hik, f.toElementMap_mono hjk⟩) := by
  apply Element.ext
  intro Y
  rw [mem_toElementMap, NeighborhoodSystem.mem_iSupDirected]
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨i, hi⟩ := (NeighborhoodSystem.mem_iSupDirected a hdir).mp hX
    exact ⟨i, X, hi, hrel⟩
  · rintro ⟨i, X, hi, hrel⟩
    exact ⟨X, (NeighborhoodSystem.mem_iSupDirected a hdir).mpr ⟨i, hi⟩, hrel⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/toElementMap_mem_iff_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.9 (Scott 1981, PRG-19).** `f(x) = ⋃ {f(↑X) ∣ X ∈ x}`: a neighbourhood `Y` lies in
`f(x)` iff it lies in `f(↑X)` for some `X ∈ x`. (Immediate from `rel_iff_mem_principal`.) -/
theorem toElementMap_mem_iff_principal (f : ApproximableMap V₀ V₁) (x : V₀.Element) {Y : Set β} :
    (f.toElementMap x).mem Y ↔
      ∃ (X : Set α) (hx : x.mem X), (f.toElementMap (V₀.principal (x.sub hx))).mem Y := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mp hrel⟩
  · rintro ⟨X, hxX, hmem⟩
    exact ⟨X, hxX, (f.rel_iff_mem_principal (x.sub hxX)).mpr hmem⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/toElementMap_ofMono_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.8 (extension, computed).** The map `ofMono m` realizes `m` on finite elements:
`(ofMono m)(↑X) = m(↑X)`. -/
theorem toElementMap_ofMono_principal
    (m : (X : Set α) → V₀.mem X → V₁.Element)
    (hmono : ∀ (X X' : Set α) (hX : V₀.mem X) (hX' : V₀.mem X'), X' ⊆ X → m X hX ≤ m X' hX')
    (X : Set α) (hX : V₀.mem X) :
    (ofMono m hmono).toElementMap (V₀.principal hX) = m X hX := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨Z, ⟨hZmem, hXZ⟩, hZ', hmY⟩
    have hle : m Z hZ' ≤ m X hX := hmono Z X hZ' hX hXZ
    exact hle Y hmY
  · intro hmY
    exact ⟨X, ⟨hX, subset_rfl⟩, hX, hmY⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- ApproximableExercises/toElementMapu2082_mono.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}


namespace ApproximableMap₂

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 2.19 (monotonicity).** The two-variable elementwise map is monotone in each argument
jointly: `x ⊑ x'`, `y ⊑ y'` imply `f(x, y) ⊑ f(x', y')`. -/
theorem toElementMap₂_mono (f : ApproximableMap₂ V₀ V₁ V₂) {x x' : V₀.Element} {y y' : V₁.Element}
    (hx : x ≤ x') (hy : y ≤ y') : f.toElementMap₂ x y ≤ f.toElementMap₂ x' y' := by
  rintro Z ⟨X, Y, hX, hY, hrel⟩
  exact ⟨X, Y, hx X hX, hy Y hY, hrel⟩

end ApproximableMap₂
end DomainTheory.NeighbourhoodSystems
end

section
-- Cl.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- The **closure** `F̄ = ⋂ {X ∈ C ∣ F ⊆ X}` of a set `F` relative to the family `C`. -/
def Cl (F : Set τ) : Set τ := ⋂₀ {X | X ∈ C ∧ F ⊆ X}

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- Cl_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- Every closure `F̄` of a token lies in `C` (closure under non-empty intersection). -/
theorem Cl_mem {F : Set τ} (h : ∃ X ∈ C, F ⊆ X) : Cl C F ∈ C := by
  show ⋂₀ {X | X ∈ C ∧ F ⊆ X} ∈ C
  apply hInter
  · obtain ⟨X, hX, hFX⟩ := h
    exact ⟨X, hX, hFX⟩
  · intro X hX
    exact hX.1

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- Cl_subset.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- `F̄ ⊆ X` whenever `X ∈ C` contains `F`: the closure is the *smallest* member of `C` over `F`. -/
theorem Cl_subset {F X : Set τ} (hX : X ∈ C) (hFX : F ⊆ X) : Cl C F ⊆ X := by
  intro t ht
  exact (Set.mem_sInter.mp ht) X ⟨hX, hFX⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- Example23/T.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The two-token codomain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/botElt.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Scott's `⊥`: the unique partial element `{Δ}` of `T`. -/
def botElt : T.Element := Example12.neighborhoodSystem.bot

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/botElt_le.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `⊥` approximates every element of `T` (the local `{Δ}` form, proved directly). -/
theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = Example12.master := hZ
  subst this
  exact x.master_mem

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/falseElt.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Scott's `false`: the total element `{Δ, {1}}` of `T`. -/
def falseElt : T.Element := Example12.neighborhoodSystem.elemOne

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The parity scanner.** `scan σ = none` while `σ` is an unbroken run of `0`'s; once a `1`
appears, `scan σ = some b` with `b = true` iff an even number of `0`'s preceded it. A leading `0`
flips the parity of the rest; a leading `1` fixes parity `true` (zero preceding zeros). -/
def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_nil.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem scan_nil : scan [] = none := rfl

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_true.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem scan_true (t : Str) : scan (true :: t) = some true := rfl

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_false.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem scan_false (t : Str) : scan (false :: t) = (scan t).map (!·) := rfl

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_append.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Stability of the scan under extension.** Once `scan σ` has committed to a parity `some b`,
every extension `σ ++ t` keeps that value. This is the engine of monotonicity for `parityMap`. -/
theorem scan_append {σ : Str} {b : Bool} (h : scan σ = some b) (t : Str) :
    scan (σ ++ t) = some b := by
  induction σ generalizing b with
  | nil => simp at h
  | cons c σ₀ ih =>
    cases c with
    | true => simp only [scan_true] at h ⊢; exact h
    | false =>
      simp only [List.cons_append, scan_false] at h ⊢
      rw [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [ih ha]
      rfl

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/trueElt.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Scott's `true`: the total element `{Δ, {0}}` of `T`. -/
def trueElt : T.Element := Example12.neighborhoodSystem.elemZero

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/valElt.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The codomain element selected by a parity reading: `none ↦ ⊥`, `some true ↦ true`,
`some false ↦ false`. -/
def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/valElt_scan_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Monotonicity of the parity value.** A longer prefix `σ <+: σ'` yields a (weakly) more defined
value: `valElt (scan σ) ⊑ valElt (scan σ')`. If `scan σ = none` then `valElt = ⊥ ⊑ _`; otherwise the
value is fixed by `scan_append`. -/
theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/parityMap.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Example 2.3 — the parity mapping `f : B → T`.** `X f Y` iff `X` is the cone `σΣ*` of some
prefix `σ` and `Y` is approximated by the parity verdict `valElt (scan σ)`. Definition 2.1:
(i) the empty prefix scans to `none = ⊥`, and `⊥` contains `Δ_T`; (ii) for a fixed cone the verdict
is a *single* filter (cones have a unique prefix), closed under `∩`; (iii) extending the prefix only
sharpens the verdict (`valElt_scan_mono`). -/
def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone_nil.symm, ?_⟩
    show (botElt).mem Example12.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/eq_botElt_of_le.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`⊥` is the unique common lower bound of `true` and `false`.** Any `a : |𝒯|` approximated by
*both* total elements is `⊥` — `𝒯`'s flatness. (Exercise 2.16's uniqueness argument: reading no
tokens yet is the only state consistent with committing to either verdict.) -/
theorem eq_botElt_of_le {a : T.Element} (h0 : a ≤ trueElt) (h1 : a ≤ falseElt) : a = botElt :=
  Example12.neighborhoodSystem.eq_bot_of_le_elemZero_of_le_elemOne h0 h1

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/parityMap_rel_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`parityMap`'s relation on a cone, read off.** `cone σ f Y ↔ Y ∈ valElt(scan σ)` — the
defining existential collapses since a cone has a *unique* generating prefix (`cone_injective`).
(Used throughout Exercise 2.16's uniqueness argument.) -/
theorem parityMap_rel_cone (σ : Str) (Y : Set Example12.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone_injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/parityMap_toElementMap_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`parityMap`'s elementwise value, read off cone-by-cone.** `f(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ valElt(scan σ)` — every neighbourhood of `x` is a cone
(`Element.sub`), and `parityMap`'s relation is exactly `parityMap_rel_cone`. -/
theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/parityMap_toElementMap_sigmaElt.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The "shift formula" for `parityMap`.** Reading off the parity of `σx` depends on `x` only
through *some* cone `cone τ ∈ x`, via the scan of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`valElt_scan_mono`), so the longest
one — `σ ++ τ` itself — already witnesses the answer. This is the key computation behind Exercise
2.16's second half: `parityMap` genuinely satisfies its own defining equations. -/
theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone_subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_append_falseFalse.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Two leading `0`'s cancel.** `scan([0,0]++τ) = scan τ`: reading two extra zeros flips the
parity twice, i.e. not at all (`Bool.not_not`). (Exercise 2.16's third equation, at the token
level — the recursive step behind the uniqueness argument for the parity map.) -/
theorem scan_append_falseFalse (τ : Str) : scan ([false, false] ++ τ) = scan τ := by
  show scan (false :: false :: τ) = scan τ
  cases h : scan τ with
  | none => simp [scan_false, h]
  | some b => simp [scan_false, h, Bool.not_not]

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_append_falseTrue.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **A leading `01` always commits to `false`, whatever follows.** `scan([0,1]++τ) = false`, for
*every* tail `τ`. (Exercise 2.16's second equation, at the token level.) -/
theorem scan_append_falseTrue (τ : Str) : scan ([false, true] ++ τ) = some false := by
  show scan (false :: true :: τ) = some false
  simp [scan_false, scan_true]

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example23/scan_append_true.lean
namespace DomainTheory.NeighbourhoodSystems.Example23

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **A leading `1` always commits to `true`, whatever follows.** `scan([1]++τ) = true`, for
*every* tail `τ`. (Exercise 2.16's first equation, at the token level.) -/
theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ

end DomainTheory.NeighbourhoodSystems.Example23
end

section
-- Example24/SatisfiesRunEquations.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The four equations of Exercise 2.17.** `g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x` for
*every* `x : |B|`, plus the single value equation `g(1) = ⊥` (this last one is *not* quantified
over `x`: it pins down `g` at the single finite element `1⊥`, matching Scott's literal statement
"`g(1) = ⊥`"). -/
structure SatisfiesRunEquations (g : ApproximableMap B B) : Prop where
  zero : ∀ x : B.Element, g.toElementMap (sigmaElt [false] x) = sigmaElt [false] (g.toElementMap x)
  oneOne : ∀ x : B.Element, g.toElementMap (sigmaElt [true, true] x) = g.toElementMap (sigmaElt [true] x)
  oneZero : ∀ x : B.Element, g.toElementMap (sigmaElt [true, false] x) = sigmaElt [false] x
  one : g.toElementMap (sigmaElt [true] B.bot) = B.bot

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/del.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Inside the first run of `1`'s: swallow `1`'s; on the first `0`, emit it and copy the rest. -/
def del : Str → Str
  | [] => []
  | true :: t => del t
  | false :: t => false :: t

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/del_nil.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem del_nil : del [] = [] := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/del_true.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem del_true (t : Str) : del (true :: t) = del t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/del_false.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem del_false (t : Str) : del (false :: t) = false :: t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The guaranteed output prefix: copy leading `0`'s; on the first `1`, eliminate the run via `del`.
-/
def out : Str → Str
  | [] => []
  | false :: t => false :: out t
  | true :: t => del t

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_nil.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem out_nil : out [] = [] := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_false.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem out_false (t : Str) : out (false :: t) = false :: out t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_true.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem out_true (t : Str) : out (true :: t) = del t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/del_append.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `del` only grows under extension: `del s <+: del (s ++ t)`. -/
theorem del_append (s t : Str) : del s <+: del (s ++ t) := by
  induction s with
  | nil => simp
  | cons c s₀ ih =>
    cases c with
    | true => simpa using ih
    | false => exact ⟨t, rfl⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_append.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `out` only grows under extension: `out σ <+: out (σ ++ t)`. -/
theorem out_append (σ t : Str) : out σ <+: out (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons c σ₀ ih =>
    cases c with
    | true => simpa using del_append σ₀ t
    | false =>
      simp only [List.cons_append, out_false]
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, by rw [List.cons_append, hu]⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Prefix-monotonicity of the output.** Extending the input prefix can only extend the guaranteed
output: `σ <+: σ' → out σ <+: out σ'`. This is the heart of Definition 2.1(iii) for `g`. -/
theorem out_mono {σ σ' : Str} (h : σ <+: σ') : out σ <+: out σ' := by
  obtain ⟨t, rfl⟩ := h
  exact out_append σ t

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/runMap.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Example 2.4 — the run-eliminating mapping `g : B → B`.** `X g Y` iff `X = σΣ*` and the cone of
the guaranteed output `(out σ)Σ*` approximates `Y`. Definition 2.1: (i) `out [] = []` so `Δ g Δ`;
(ii) a fixed cone has a unique prefix, and the value is the principal filter `↑((out σ)Σ*)`, closed
under `∩`; (iii) `out_mono` shrinks the output cone as the input cone shrinks. -/
def runMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (out σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [out_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (out σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (out σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (out σ') ⊆ cone (out σ) := cone_subset_cone.mpr (out_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_append_false.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **A leading `0` always emits it and continues copying.** `out([0]++τ) = 0::out τ`, for every
tail `τ`. (Exercise 2.17's first equation, at the token level.) -/
theorem out_append_false (τ : Str) : out ([false] ++ τ) = false :: out τ := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_append_trueFalse.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`10` terminates the run and emits the `0`, whatever follows.** `out([1,0]++τ) = 0::τ`, for
every tail `τ`. (Exercise 2.17's third equation, at the token level.) -/
theorem out_append_trueFalse (τ : Str) : out ([true, false] ++ τ) = false :: τ := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_append_trueTrue.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **A second consecutive `1` changes nothing.** `out([1,1]++τ) = out([1]++τ)`: once inside the
run of `1`'s, an extra `1` is simply swallowed by `del`. (Exercise 2.17's second equation, at the
token level — the recursive step behind the uniqueness argument for `runMap`.) -/
theorem out_append_trueTrue (τ : Str) : out ([true, true] ++ τ) = out ([true] ++ τ) := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_true_false.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Cons-form restatement of `out_append_trueFalse`, for peeling one token at a time in `key`. -/
theorem out_true_false (t : Str) : out (true :: false :: t) = false :: t := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/out_true_true.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Cons-form restatement of `out_append_trueTrue`, for peeling one token at a time in `key`. -/
theorem out_true_true (t : Str) : out (true :: true :: t) = out (true :: t) := rfl

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/key.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The recursive core of uniqueness.** Any `g` satisfying the four equations agrees with
`runMap` on every principal (finite) element `σ⊥`. The recursion peels *one* token at a time,
matching `out`'s own case split: a leading `0` recurses via `hg.zero` (`Basic decreasing case`);
inside a run of `1`'s, a further `1` recurses via `hg.oneOne` (peeling to `1τ`, still one token
shorter); a `1` followed by `0` is pinned *directly* by `hg.oneZero` for any tail (no recursion);
the lone token `1` (nothing more) is pinned directly by `hg.one`; and the base case `σ = []` is
the one place order theory enters: `⊥ ≤ 1⊥` forces `g(⊥) ≤ g(1⊥) = ⊥` by monotonicity, and `⊥` is
already the least element, so `g(⊥) = ⊥`. -/
theorem key (g : ApproximableMap B B) (hg : SatisfiesRunEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = sigmaElt (out σ) B.bot
  | [] => by
      rw [show out ([] : Str) = ([] : Str) from rfl, sigmaElt_nil]
      have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
      rw [hg.one] at hm
      exact le_antisymm hm (B.bot_le _)
  | [true] => by
      rw [show out [true] = ([] : Str) from rfl, sigmaElt_nil]
      exact hg.one
  | true :: false :: t => by
      rw [out_true_false, show (true :: false :: t : Str) = [true, false] ++ t from rfl,
        sigmaElt_append, hg.oneZero, ← sigmaElt_append]
      rfl
  | true :: true :: t => by
      rw [out_true_true, show (true :: true :: t : Str) = [true, true] ++ t from rfl,
        sigmaElt_append, hg.oneOne, ← sigmaElt_append]
      exact key g hg (true :: t)
  | false :: t => by
      rw [out_false, show (false :: t : Str) = [false] ++ t from rfl, sigmaElt_append, hg.zero,
        key g hg t, show (false :: out t : Str) = [false] ++ out t from rfl, sigmaElt_append]

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/runMap_rel_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`runMap`'s relation on a cone, read off.** `σΣ* g Y ↔ Y ∈ B ∧ (out σ)Σ* ⊆ Y` — the defining
existential collapses since a cone has a *unique* generating prefix (`cone_injective`). -/
theorem runMap_rel_cone (σ : Str) (Y : Set Str) :
    runMap.rel (cone σ) Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y := by
  constructor
  · rintro ⟨ρ, hρ, hYmem, hsub⟩
    obtain rfl : ρ = σ := (cone_injective hρ).symm
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/eq_runMap_of_satisfies.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Exercise 2.17, second half.** `runMap` is the *unique* approximable map `B → B` satisfying
`g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x`, `g(1) = ⊥`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = runMap` to matching relations on cones, which
is exactly `key` read through `rel_iff_mem_principal`/`runMap_rel_cone`. -/
theorem eq_runMap_of_satisfies {g : ApproximableMap B B} (hg : SatisfiesRunEquations g) :
    g = runMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ runMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, sigmaElt_bot, runMap_rel_cone]
    show (B.principal (memB_cone (out σ))).mem Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y
    exact B.mem_principal (memB_cone (out σ))
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX, fun hr => absurd (runMap.rel_dom hr) hX⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/runMap_toElementMap_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`runMap`'s elementwise value, read off cone-by-cone.** `g(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ B` and `(out σ)Σ* ⊆ Y`. -/
theorem runMap_toElementMap_mem (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out τ) ⊆ Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (runMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone τ, hτ, (runMap_rel_cone τ Y).mpr ⟨hYmem, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/runMap_toElementMap_sigmaElt.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The "shift formula" for `runMap` (input side).** Reading off `g(σx)` depends on `x` only
through *some* cone `cone τ ∈ x`, via the output of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`out_mono`), so the longest one —
`σ ++ τ` itself — already witnesses the answer. -/
theorem runMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out (σ ++ τ)) ⊆ Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hYmem, hsubOut⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, hYmem, (cone_subset_cone.mpr (out_mono (cone_subset_cone.mp hsub))).trans hsubOut⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩,
      (runMap_rel_cone (σ ++ τ) Y).mpr ⟨hYmem, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/sigmaElt_runMap_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The "shift formula" for `runMap` (output side).** Since `g(x)`'s membership predicate is
itself a cone-monotone family (`runMap_toElementMap_mem`), prepending `τ₀` to `g(x)` collapses the
same way: the up-closure of neighbourhoods `Z ⊇ (out τ)Σ*` is absorbed because `(out τ)Σ*` itself
is the *deepest* (hence hardest-to-satisfy, so witness-minimal) choice. -/
theorem sigmaElt_runMap_toElementMap (τ₀ : Str) (x : B.Element) (Y : Set Str) :
    (sigmaElt τ₀ (runMap.toElementMap x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (τ₀ ++ out τ) ⊆ Y := by
  constructor
  · rintro ⟨hYmem, Z, hZ, hsub⟩
    obtain ⟨τ, hτ, _, hZsub⟩ := (runMap_toElementMap_mem x Z).mp hZ
    refine ⟨τ, hτ, hYmem, ?_⟩
    rw [← prepend_cone]
    exact (prepend_mono τ₀ hZsub).trans hsub
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    refine ⟨hYmem, cone (out τ),
      (runMap_toElementMap_mem x _).mpr ⟨τ, hτ, memB_cone _, subset_rfl⟩, ?_⟩
    rw [prepend_cone]
    exact hsub

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Example24/runMap_satisfies.lean
namespace DomainTheory.NeighbourhoodSystems.Example24

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`runMap` satisfies its own defining equations.** `zero`/`oneOne`/`oneZero` are direct
instances of the two "shift formulas" (`runMap_toElementMap_sigmaElt` on the input side,
`sigmaElt_runMap_toElementMap` on the output side), using that the output of a leading `0`
(resp. `11`, `10`) is fixed by `out_append_false`/`out_append_trueTrue`/`out_append_trueFalse`
regardless of the tail. `one` reads off the unique cone (`Λ`) that `⊥` sits in
(`bot_mem_cone_iff`), where `out [true] = []`. -/
theorem runMap_satisfies : SatisfiesRunEquations runMap where
  zero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, sigmaElt_runMap_toElementMap]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false]⟩
  oneOne x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_trueTrue] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [← out_append_trueTrue] at hsub⟩
  oneZero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      rw [out_append_trueFalse] at hsub
      exact ⟨hYmem, cone τ, hτ, by rw [prepend_cone]; exact hsub⟩
    · rintro ⟨hYmem, X, hX, hsub⟩
      obtain ⟨τ, rfl⟩ := x.sub hX
      rw [prepend_cone] at hsub
      exact ⟨τ, hX, hYmem, by rwa [out_append_trueFalse]⟩
  one := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      obtain rfl : τ = [] := bot_mem_cone_iff.mp hτ
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil] at hsub
      rw [mem_bot]
      exact Set.eq_univ_of_univ_subset hsub
    · intro hY
      rw [mem_bot] at hY
      refine ⟨[], bot_mem_cone_iff.mpr rfl, hY ▸ B.master_mem, ?_⟩
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil, hY, B_master]

end DomainTheory.NeighbourhoodSystems.Example24
end

section
-- Exercise213/BasicInst8.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace NeighborhoodSystem

/-- **Algebraicity.** Every element `x` is the directed union of its own principal
("finite"/compact) approximants: `x = ⋃ {↑X ∣ X ∈ x}`, literally as an `iSupDirected`. (Used below
to reduce continuity checks to principal elements; a duplicate of `Theorem85.lean`'s own copy,
kept local here to avoid a heavy import for this early file.) -/
instance instNonemptyMemSubtype (x : V₀.Element) : Nonempty {X : Set α // x.mem X} :=
  ⟨⟨V₀.master, x.master_mem⟩⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/continuous_monotone.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace NeighborhoodSystem

/-- A continuous function between domains is monotone for the approximation order `⊑`: this is
because `⊑` is recoverable from the topology (`le_iff_isOpen_imp`) and continuous preimages of opens
are open and upward closed (`isOpen_isUpperSet`). -/
theorem continuous_monotone {c : V₀.Element → V₁.Element} (hc : Continuous c) : Monotone c := by
  intro x y hxy
  rw [V₁.le_iff_isOpen_imp]
  intro U hU hxU
  exact V₀.isOpen_isUpperSet (hU.preimage hc) hxU hxy

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/ofContinuous.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- **Exercise 2.13 (reverse).** The approximable mapping determined by a continuous function `c`:
its action on the finite element `↑X` is the value `c(↑X)`, extended to all of `𝒟₀` via `ofMono`.
Monotonicity of `X ↦ c(↑X)` is `continuous_monotone` together with the inclusion-reversal
`X' ⊆ X ↔ ↑X ⊑ ↑X'`. -/
def ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c) : ApproximableMap V₀ V₁ :=
  ofMono (fun _X hX => c (V₀.principal hX))
    (fun _X _X' hX hX' hX'X =>
      NeighborhoodSystem.continuous_monotone hc ((V₀.principal_le_iff hX hX').mpr hX'X))

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/continuous_toElementMap.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- **Exercise 2.13 (forward).** The elementwise function of an approximable mapping is continuous.
For an open `U` and `x` with `f(x) ∈ U`, openness gives `Y` with `Y ∈ f(x)` and `[Y] ⊆ U`; unfolding
`Y ∈ f(x)` produces `X ∈ x` with `X f Y`; then `[X] ⊆ f⁻¹U`, since any `x' ∈ [X]` has `Y ∈ f(x')`
(via `X f Y`). -/
theorem continuous_toElementMap (f : ApproximableMap V₀ V₁) :
    Continuous (fun x => f.toElementMap x) := by
  rw [continuous_def]
  intro U hU
  show V₀.OpenFilter _
  constructor
  intro x hx
  obtain ⟨Y, hY, hYU⟩ := hU.out (f.toElementMap x) hx
  obtain ⟨X, hxX, hrel⟩ := hY
  exact ⟨X, hxX, fun x' hx' => hYU ⟨X, hx', hrel⟩⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/mem_iff_principal_of_continuous.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem


/-- **Exercise 2.13 — Scott's union formula for a continuous map.** For continuous `c` and any
`x ∈ |𝒟₀|`: `Y ∈ c(x) ↔ ∃ X ∈ x, Y ∈ c(↑X)`.

* `→` : `c⁻¹[[Y]]` is open and contains `x`, so it contains a basic neighbourhood `[X]` with `X ∈ x`;
  since `↑X ∈ [X]`, `Y ∈ c(↑X)`.
* `←` : `↑X ⊑ x` and `c` monotone (`continuous_monotone`) give `c(↑X) ⊑ c(x)`, transporting `Y`. -/
theorem mem_iff_principal_of_continuous {c : V₀.Element → V₁.Element} (hc : Continuous c)
    (x : V₀.Element) {Y : Set β} :
    (c x).mem Y ↔ ∃ (X : Set α) (hx : x.mem X), (c (V₀.principal (x.sub hx))).mem Y := by
  constructor
  · intro hY
    have hxpre : x ∈ c ⁻¹' V₁.basicOpen Y := hY
    have hopen : IsOpen (c ⁻¹' V₁.basicOpen Y) := (V₁.isOpen_basicOpen Y).preimage hc
    obtain ⟨X, hxX, hXU⟩ := hopen.out x hxpre
    refine ⟨X, hxX, ?_⟩
    exact hXU (show V₀.principal (x.sub hxX) ∈ V₀.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)
  · rintro ⟨X, hxX, hY⟩
    have hple : V₀.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact (continuous_monotone hc hple) Y hY

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/principalFamily_directed.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem


theorem principalFamily_directed (x : V₀.Element) :
    ∀ i j : {X : Set α // x.mem X}, ∃ k : {X : Set α // x.mem X},
      V₀.principal (x.sub i.2) ≤ V₀.principal (x.sub k.2) ∧
        V₀.principal (x.sub j.2) ≤ V₀.principal (x.sub k.2) :=
  fun i j => ⟨⟨i.1 ∩ j.1, x.inter_mem i.2 j.2⟩,
    (V₀.principal_le_iff (x.sub i.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_left,
    (V₀.principal_le_iff (x.sub j.2) (x.sub (x.inter_mem i.2 j.2))).mpr Set.inter_subset_right⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/eq_iSupDirected_principal.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem


theorem eq_iSupDirected_principal (x : V₀.Element) :
    x = iSupDirected (fun i : {X : Set α // x.mem X} => V₀.principal (x.sub i.2))
      (principalFamily_directed x) := by
  apply Element.ext
  intro Z
  rw [mem_iSupDirected]
  constructor
  · intro hZ; exact ⟨⟨Z, hZ⟩, (V₀.mem_principal _).mpr ⟨x.sub hZ, subset_rfl⟩⟩
  · rintro ⟨⟨X, hX⟩, hZ'⟩
    obtain ⟨hZmem, hXZ⟩ := (V₀.mem_principal _).mp hZ'
    exact x.up_mem hX hZmem hXZ

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/continuous_of_monotone_iSupDirected.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace NeighborhoodSystem


/-- **The converse of `continuous_toElementMap`/`continuous_monotone`, in domain-theoretic form.**
A monotone function that also preserves directed unions is topologically continuous — the standard
"Scott continuity ⟺ order-theoretic continuity" bridge, proved directly from algebraicity rather
than through a general topological-basis argument: given `x ∈ c⁻¹U`, decompose `x` as the directed
union of its principal approximants (`eq_iSupDirected_principal`); `c` preserving the union puts
`c x` there too, so openness of `U` finds a witness `Y` in *some* `c(↑X)` (`X ∈ x`); monotonicity of
`c` then transfers `Y ∈ c(↑X)` up to every `x' ∈ [X]`, giving `[X] ⊆ c⁻¹U`. -/
theorem continuous_of_monotone_iSupDirected {c : V₀.Element → V₁.Element} (hmono : Monotone c)
    (hsup : ∀ {I : Type u} [Nonempty I] (d : I → V₀.Element)
      (hdir : ∀ i j, ∃ k, d i ≤ d k ∧ d j ≤ d k)
      (hdir' : ∀ i j, ∃ k, c (d i) ≤ c (d k) ∧ c (d j) ≤ c (d k)),
      c (iSupDirected d hdir) = iSupDirected (fun i => c (d i)) hdir') :
    Continuous c := by
  rw [continuous_def]
  intro U hU
  constructor
  intro x hx
  rw [Set.mem_preimage] at hx
  set fam : {X : Set α // x.mem X} → V₀.Element := fun i => V₀.principal (x.sub i.2) with hfam
  have hdir : ∀ i j : {X : Set α // x.mem X}, ∃ k, fam i ≤ fam k ∧ fam j ≤ fam k :=
    principalFamily_directed x
  have hdir' : ∀ i j : {X : Set α // x.mem X}, ∃ k, c (fam i) ≤ c (fam k) ∧ c (fam j) ≤ c (fam k) :=
    fun i j => by obtain ⟨k, hik, hjk⟩ := hdir i j; exact ⟨k, hmono hik, hmono hjk⟩
  have hxeq : c x = iSupDirected (fun i => c (fam i)) hdir' :=
    (congrArg c (eq_iSupDirected_principal x)).trans
      (hsup (I := {X : Set α // x.mem X}) fam hdir hdir')
  rw [hxeq] at hx
  obtain ⟨Y, hY, hYU⟩ := hU.out _ hx
  obtain ⟨i, hi⟩ := (mem_iSupDirected _ hdir').mp hY
  refine ⟨i.1, i.2, fun x' hx' => hYU ?_⟩
  have hple : fam i ≤ x' := fun Z hZ => x'.up_mem hx' hZ.1 hZ.2
  exact (hmono hple) Y hi

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213/toElementMap_ofContinuous.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

universe u

variable {α : Type u} {β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


namespace ApproximableMap


/-- **Exercise 2.13 — the round trip.** `ofContinuous c hc` induces exactly `c`:
`(ofContinuous c hc)(x) = c(x)` for all `x`. Exercise 2.9 reduces `f(x)` to a union over finite
approximants `↑X` (`X ∈ x`), where `ofMono` evaluates to `c(↑X)`; the union formula
`mem_iff_principal_of_continuous` then re-assembles `c(x)`. -/
theorem toElementMap_ofContinuous (c : V₀.Element → V₁.Element) (hc : Continuous c)
    (x : V₀.Element) : (ofContinuous c hc).toElementMap x = c x := by
  apply Element.ext
  intro Y
  rw [toElementMap_mem_iff_principal, NeighborhoodSystem.mem_iff_principal_of_continuous hc]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal] at hmem
  · rintro ⟨X, hxX, hmem⟩
    refine ⟨X, hxX, ?_⟩
    rwa [ofContinuous, toElementMap_ofMono_principal]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise213.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_213.{u, u_1} : And
  (And
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y)))
  (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (c :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (hc :
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofContinuous α β V₀ V₁ c hc) x)
      (c x)) :=
  @And.intro
  (And
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y)))
  (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (c :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
    (hc :
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀),
    @Eq (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofContinuous α β V₀ V₁ c hc) x)
      (c x))
  (@And.intro
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁),
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁)
        fun (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) =>
        @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap α β V₀ V₁ f x)
    (∀ {α : Type u} {β : Type u_1} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      {c :
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀ →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁},
      @Continuous (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement α V₀)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement β V₁) c →
        ∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀) {Y : Set β},
          Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁ (c x) Y)
            (∃ (X : Set α) (hx : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V₀ x X),
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem β V₁
                (c
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V₀ X
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.sub α V₀ x X hx)))
                Y))
    @DomainTheory.NeighbourhoodSystems.ApproximableMap.continuous_toElementMap
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem_iff_principal_of_continuous)
  @DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap_ofContinuous

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise214/phi.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.14 — the correspondence `φ`.** For a domain isomorphism `e` and `X ∈ 𝒟₀`, `φ(X)` is
the neighbourhood with `e(↑X) = ↑φ(X)` provided by Theorem 2.7. -/
noncomputable def phi (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) : Set β :=
  Classical.choose (exists_principal_eq_apply_principal e hX)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise214/phi_mem.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- `φ(X) ∈ 𝒟₁`. -/
theorem phi_mem (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    V₁.mem (phi e hX) :=
  Classical.choose (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise214/phi_spec.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Theorem 2.7 defining equation: `e(↑X) = ↑φ(X)`.** -/
theorem phi_spec (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) :
    e (V₀.principal hX) = V₁.principal (phi_mem e hX) :=
  Classical.choose_spec (Classical.choose_spec (exists_principal_eq_apply_principal e hX))

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise214/phi_inter.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 2.14 — `φ` preserves consistent intersections.** If `X, X'` are consistent
(`X ∩ X' ∈ 𝒟₀`), then `φ(X ∩ X') = φ(X) ∩ φ(X')`.

`↑(X ∩ X')` is the join of `↑X, ↑X'` in `|𝒟₀|` (the order is inclusion-reversed). `e`/`e.symm`
preserve this least upper bound, and the join of the consistent principals `↑φ(X), ↑φ(X')` is
`↑(φ(X) ∩ φ(X'))`. -/
theorem phi_inter (e : V₀.Element ≃o V₁.Element) {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hXX' : V₀.mem (X ∩ X')) :
    phi e hXX' = phi e hX ∩ phi e hX' := by
  have hpX_le : V₀.principal hX ≤ V₀.principal hXX' :=
    (V₀.principal_le_iff hX hXX').mpr Set.inter_subset_left
  have hpX'_le : V₀.principal hX' ≤ V₀.principal hXX' :=
    (V₀.principal_le_iff hX' hXX').mpr Set.inter_subset_right
  have hleast : ∀ w : V₀.Element, V₀.principal hX ≤ w → V₀.principal hX' ≤ w →
      V₀.principal hXX' ≤ w := by
    intro w hXw hX'w Z hZ
    obtain ⟨hZmem, hsubZ⟩ := hZ
    have hwX : w.mem X := hXw X ⟨hX, subset_rfl⟩
    have hwX' : w.mem X' := hX'w X' ⟨hX', subset_rfl⟩
    exact w.up_mem (w.inter_mem hwX hwX') hZmem hsubZ
  have hqX : e (V₀.principal hX) = V₁.principal (phi_mem e hX) := phi_spec e hX
  have hqX' : e (V₀.principal hX') = V₁.principal (phi_mem e hX') := phi_spec e hX'
  have hqXX' : e (V₀.principal hXX') = V₁.principal (phi_mem e hXX') := phi_spec e hXX'
  have hsub1 : phi e hXX' ⊆ phi e hX := by
    have h : e (V₀.principal hX) ≤ e (V₀.principal hXX') := e.monotone hpX_le
    rw [hqX, hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hX) (phi_mem e hXX')).mp h
  have hsub1' : phi e hXX' ⊆ phi e hX' := by
    have h : e (V₀.principal hX') ≤ e (V₀.principal hXX') := e.monotone hpX'_le
    rw [hqX', hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hX') (phi_mem e hXX')).mp h
  have hsubInter : phi e hXX' ⊆ phi e hX ∩ phi e hX' := Set.subset_inter hsub1 hsub1'
  have hinter : V₁.mem (phi e hX ∩ phi e hX') :=
    V₁.inter_mem (phi_mem e hX) (phi_mem e hX') (phi_mem e hXX') hsubInter
  have hsub2 : phi e hX ∩ phi e hX' ⊆ phi e hXX' := by
    have hqXleI : e (V₀.principal hX) ≤ V₁.principal hinter := by
      rw [hqX]; exact (V₁.principal_le_iff (phi_mem e hX) hinter).mpr Set.inter_subset_left
    have hqX'leI : e (V₀.principal hX') ≤ V₁.principal hinter := by
      rw [hqX']; exact (V₁.principal_le_iff (phi_mem e hX') hinter).mpr Set.inter_subset_right
    have hpXleI : V₀.principal hX ≤ e.symm (V₁.principal hinter) := by
      have h := e.symm.monotone hqXleI; rwa [e.symm_apply_apply] at h
    have hpX'leI : V₀.principal hX' ≤ e.symm (V₁.principal hinter) := by
      have h := e.symm.monotone hqX'leI; rwa [e.symm_apply_apply] at h
    have hpXX'leI : V₀.principal hXX' ≤ e.symm (V₁.principal hinter) :=
      hleast _ hpXleI hpX'leI
    have h : e (V₀.principal hXX') ≤ V₁.principal hinter := by
      have h := e.monotone hpXX'leI; rwa [e.apply_symm_apply] at h
    rw [hqXX'] at h
    exact (V₁.principal_le_iff (phi_mem e hXX') hinter).mp h
  exact Set.Subset.antisymm hsubInter hsub2

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise214/rel_ofIso_iff.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Exercise 2.14 — the approximable mapping of `e` is `φ(X) ⊆ Y`.** For `X ∈ 𝒟₀`,
`(ofIso e).rel X Y ↔ Y ∈ 𝒟₁ ∧ φ(X) ⊆ Y`. (Immediate from `phi_spec` and `mem_principal`.) -/
theorem rel_ofIso_iff (e : V₀.Element ≃o V₁.Element) {X : Set α} (hX : V₀.mem X) {Y : Set β} :
    (ofIso e).rel X Y ↔ V₁.mem Y ∧ phi e hX ⊆ Y := by
  constructor
  · rintro ⟨_, hmem⟩
    have h : (e (V₀.principal hX)).mem Y := hmem
    rw [phi_spec e hX] at h
    exact h
  · intro h
    refine ⟨hX, ?_⟩
    rw [phi_spec e hX]
    exact h

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise214.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_214.{u_1, u_2} : And
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X X' : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X)
    (hX' : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X')
    (hXX' :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Inter.inter (Set α) (@Set.instInter α) X X')),
    @Eq (Set β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e (@Inter.inter (Set α) (@Set.instInter α) X X') hXX')
      (@Inter.inter (Set β) (@Set.instInter β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX)
        (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X' hX')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X) {Y : Set β},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β V₀ V₁ e) X Y)
      (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y)
        (@LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX) Y))) :=
  @And.intro
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X X' : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X)
    (hX' : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X')
    (hXX' :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ (@Inter.inter (Set α) (@Set.instInter α) X X')),
    @Eq (Set β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e (@Inter.inter (Set α) (@Set.instInter α) X X') hXX')
      (@Inter.inter (Set β) (@Set.instInter β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX)
        (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X' hX')))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (e :
      @OrderIso (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V₀)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V₀)))
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element β V₁)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement β V₁))))
    {X : Set α} (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V₀ X) {Y : Set β},
    Iff
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V₀ V₁
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.ofIso α β V₀ V₁ e) X Y)
      (And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β V₁ Y)
        (@LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.phi α β V₀ V₁ e X hX) Y)))
  @DomainTheory.NeighbourhoodSystems.phi_inter @DomainTheory.NeighbourhoodSystems.rel_ofIso_iff

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise215/memO.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership for `𝒪`: a neighbourhood is the master `Δ = univ` or the empty set. -/
def memO (X : Set (Fin 1)) : Prop := X = Set.univ ∨ X = ∅

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/nestedOrDisjoint_O.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem nestedOrDisjoint_O : NestedOrDisjoint memO := by
  rintro X Y (rfl | rfl) (rfl | rfl)
  · exact Or.inl subset_rfl
  · exact Or.inr (Or.inl (Set.empty_subset _))
  · exact Or.inl (Set.empty_subset _)
  · exact Or.inl subset_rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/subMaster_O.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem subMaster_O : ∀ {X : Set (Fin 1)}, memO X → X ⊆ Set.univ := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.15 — the one-token system `𝒪 = {Δ, ∅}`.** -/
def O : NeighborhoodSystem (Fin 1) :=
  NeighborhoodSystem.ofNestedOrDisjoint memO Set.univ Set.univ_nonempty
    (Or.inl rfl) nestedOrDisjoint_O subMaster_O

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem O_mem {X : Set (Fin 1)} : O.mem X ↔ memO X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem O_master : O.master = (Set.univ : Set (Fin 1)) := rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O_mem_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem O_mem_empty : O.mem (∅ : Set (Fin 1)) := Or.inr rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O_inter_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `𝒪` is closed under intersection (used to verify the relation of `openToMap`). -/
theorem O_inter_mem {Y Y' : Set (Fin 1)} (hY : O.mem Y) (hY' : O.mem Y') : O.mem (Y ∩ Y') := by
  rcases hY with rfl | rfl
  · rw [Set.univ_inter]; exact hY'
  · rw [Set.empty_inter]; exact O_mem_empty

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/botElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The bottom element `⊥ = ↑Δ = {Δ}` of `|𝒪|`. -/
def botElt : O.Element := O.bot

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/mem_botElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `Y ∈ ⊥` iff `Y = Δ = univ`. -/
theorem mem_botElt {Y : Set (Fin 1)} : botElt.mem Y ↔ Y = (Set.univ : Set (Fin 1)) := by
  rw [botElt, O.mem_bot, O_master]

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/topElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The top element `⊤ = ↑∅` of `|𝒪|`. -/
def topElt : O.Element := O.principal O_mem_empty

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/mapToOpen.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — the open set of an approximable map.** `mapToOpen f = {x ∣ f(x) = ⊤}`. -/
def mapToOpen (f : ApproximableMap V O) : Set V.Element := {x | f.toElementMap x = topElt}

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/mem_empty_iff_eq_top.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **The defining property of `⊤`.** An element `z` of `|𝒪|` is `⊤` iff it contains `∅`: `∅` is
the sharpest neighbourhood, so `∅ ∈ z` forces `z` to be the principal filter `↑∅ = ⊤`. -/
theorem mem_empty_iff_eq_top (z : O.Element) : z.mem ∅ ↔ z = topElt := by
  constructor
  · intro hz
    exact O.eq_principal_of_isMin z hz (fun Y _ => Set.empty_subset Y)
  · rintro rfl
    exact ⟨O_mem_empty, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/element_eq_bot_or_top.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Two elements.** Every element of `|𝒪|` is `⊥` or `⊤`. -/
theorem element_eq_bot_or_top (z : O.Element) : z = botElt ∨ z = topElt := by
  by_cases hz : z.mem ∅
  · exact Or.inr ((mem_empty_iff_eq_top z).mp hz)
  · refine Or.inl ?_
    apply Element.ext
    intro Y
    constructor
    · intro hY
      rcases (O_mem.mp (z.sub hY)) with rfl | rfl
      · exact mem_botElt.mpr rfl
      · exact absurd hY hz
    · intro hY
      rw [mem_botElt.mp hY, ← O_master]
      exact z.master_mem

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O_ext.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Extensionality for `|𝒪|`.** Two elements agreeing on membership of `∅` are equal (it
distinguishes `⊥` from `⊤`). -/
theorem O_ext {z w : O.Element} (h : z.mem ∅ ↔ w.mem ∅) : z = w := by
  by_cases hz : z.mem ∅
  · rw [(mem_empty_iff_eq_top z).mp hz, (mem_empty_iff_eq_top w).mp (h.mp hz)]
  · have ez : z = botElt :=
      (element_eq_bot_or_top z).resolve_right (fun c => hz ((mem_empty_iff_eq_top z).mpr c))
    have ew : w = botElt :=
      (element_eq_bot_or_top w).resolve_right
        (fun c => (fun c' => hz (h.mpr c')) ((mem_empty_iff_eq_top w).mpr c))
    rw [ez, ew]

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/isOpen_mapToOpen.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- `mapToOpen f` is open: it is the preimage of the open point `{⊤} = [∅]` under the continuous
`x ↦ f(x)` (Exercise 2.13). -/
theorem isOpen_mapToOpen (f : ApproximableMap V O) : IsOpen (mapToOpen V f) := by
  have heq : mapToOpen V f = (fun x => f.toElementMap x) ⁻¹' O.basicOpen ∅ := by
    ext x
    simp only [mapToOpen, Set.mem_ofPred_eq, Set.mem_preimage, mem_basicOpen]
    exact (mem_empty_iff_eq_top (f.toElementMap x)).symm
  rw [heq]
  exact (O.isOpen_basicOpen ∅).preimage f.continuous_toElementMap

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/univ_ne_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem univ_ne_empty : (Set.univ : Set (Fin 1)) ≠ ∅ := by
  intro h
  have h0 : (0 : Fin 1) ∈ (∅ : Set (Fin 1)) := h ▸ Set.mem_univ 0
  simp at h0

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/openToMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — the approximable map of an open set.** For open `U ⊆ |𝒟|`, the relation
`X f Y ↔ X ∈ 𝒟 ∧ Y ∈ 𝒪 ∧ (Y = ∅ → ↑X ∈ U)`. The single nontrivial obligation is monotonicity:
sharpening the input `X' ⊆ X` means `↑X ⊑ ↑X'`, and `U` open (an upper set) carries `↑X ∈ U` up to
`↑X' ∈ U`. Choice-free. -/
def openToMap (U : Set V.Element) (hU : IsOpen U) : ApproximableMap V O where
  rel X Y := V.mem X ∧ O.mem Y ∧ (Y = ∅ → ∃ hX : V.mem X, V.principal hX ∈ U)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V.master_mem, O.master_mem, fun heq => (univ_ne_empty (O_master ▸ heq)).elim⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, fY⟩ ⟨_, hY', fY'⟩
    refine ⟨hX, O_inter_mem hY hY', ?_⟩
    intro h
    rcases O_mem.mp hY with rfl | rfl
    · rw [Set.univ_inter] at h; exact fY' h
    · exact fY rfl
  mono := by
    rintro X X' Y Y' ⟨hX, _, fY⟩ hX'X hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    intro hY'eq
    have hYeq : Y = ∅ := Set.subset_empty_iff.mp (hY'eq ▸ hYY')
    obtain ⟨hX0, hmem⟩ := fY hYeq
    have hmem' : V.principal hX ∈ U := hmem
    have hle : V.principal hX ≤ V.principal hX' := (V.principal_le_iff hX hX').mpr hX'X
    exact ⟨hX', V.isOpen_isUpperSet hU hmem' hle⟩

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/toElementMap_openToMap_principal_mem_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- The value of `openToMap U hU` on the finite element `↑X` contains `∅` iff `↑X ∈ U`; i.e.
`(openToMap U hU)(↑X) = ⊤ ↔ ↑X ∈ U`. -/
theorem toElementMap_openToMap_principal_mem_empty (U : Set V.Element) (hU : IsOpen U)
    {X : Set γ} (hX : V.mem X) :
    ((openToMap V U hU).toElementMap (V.principal hX)).mem ∅ ↔ V.principal hX ∈ U := by
  rw [← (openToMap V U hU).rel_iff_mem_principal hX]
  constructor
  · rintro ⟨_, _, fimpl⟩
    obtain ⟨_, hmem⟩ := fimpl rfl
    exact hmem
  · intro h
    exact ⟨hX, O_mem_empty, fun _ => ⟨hX, h⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/mem_mapToOpen_openToMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — round trip (open → map → open).** `mapToOpen (openToMap U hU) = U`. -/
theorem mem_mapToOpen_openToMap (U : Set V.Element) (hU : IsOpen U) (x : V.Element) :
    x ∈ mapToOpen V (openToMap V U hU) ↔ x ∈ U := by
  rw [mapToOpen, Set.mem_ofPred_eq, ← mem_empty_iff_eq_top,
    ApproximableMap.toElementMap_mem_iff_principal]
  constructor
  · rintro ⟨X, hxX, hmem⟩
    rw [toElementMap_openToMap_principal_mem_empty] at hmem
    have hple : V.principal (x.sub hxX) ≤ x := fun Z hZ => x.up_mem hxX hZ.1 hZ.2
    exact V.isOpen_isUpperSet hU hmem hple
  · intro hxU
    obtain ⟨X, hxX, hXU⟩ := hU.out x hxU
    refine ⟨X, hxX, ?_⟩
    rw [toElementMap_openToMap_principal_mem_empty]
    exact hXU (show V.principal (x.sub hxX) ∈ V.basicOpen X from ⟨x.sub hxX, subset_rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/openToMap_mapToOpen.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 — round trip (map → open → map).** `openToMap (mapToOpen f) = f`. -/
theorem openToMap_mapToOpen (f : ApproximableMap V O) :
    openToMap V (mapToOpen V f) (isOpen_mapToOpen V f) = f := by
  apply ApproximableMap.eq_of_toElementMap_principal
  intro X hX
  apply O_ext
  rw [toElementMap_openToMap_principal_mem_empty, mapToOpen, Set.mem_ofPred_eq,
    ← mem_empty_iff_eq_top]

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

set_option linter.unusedVariables false

theorem example_215.{u_1} : And
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
    (hU :
      @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement γ V) U)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V),
    Iff
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V
          (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V U hU))
        x)
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)) U x))
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (f :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O)
      (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V f)
        (@DomainTheory.NeighbourhoodSystems.Exercise215.isOpen_mapToOpen γ V f))
      f) :=
  @And.intro
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (U : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
    (hU :
      @IsOpen (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instTopologicalSpaceElement γ V) U)
    (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V),
    Iff
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V
          (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V U hU))
        x)
      (@Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)
        (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V))
        (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element γ V)) U x))
  (∀ {γ : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ)
    (f :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap γ
        (Fin (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) V
        DomainTheory.NeighbourhoodSystems.Exercise215.O)
      (@DomainTheory.NeighbourhoodSystems.Exercise215.openToMap γ V
        (@DomainTheory.NeighbourhoodSystems.Exercise215.mapToOpen γ V f)
        (@DomainTheory.NeighbourhoodSystems.Exercise215.isOpen_mapToOpen γ V f))
      f)
  @DomainTheory.NeighbourhoodSystems.Exercise215.mem_mapToOpen_openToMap
  @DomainTheory.NeighbourhoodSystems.Exercise215.openToMap_mapToOpen

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/openSet_equiv_map.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

variable {γ : Type*} (V : NeighborhoodSystem γ)

/-- **Exercise 2.15 (main).** The open subsets of `|𝒟|` are in one-one correspondence with the
approximable mappings `𝒟 → 𝒪`, via `U ↦ openToMap U` and `f ↦ {x ∣ f(x) = ⊤}`. -/
def openSet_equiv_map : {U : Set V.Element // IsOpen U} ≃ ApproximableMap V O where
  toFun U := openToMap V U.1 U.2
  invFun f := ⟨mapToOpen V f, isOpen_mapToOpen V f⟩
  left_inv := by
    rintro ⟨U, hU⟩
    apply Subtype.ext
    ext x
    exact mem_mapToOpen_openToMap V U hU x
  right_inv f := openToMap_mapToOpen V f

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/O_mem_univ.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem O_mem_univ : O.mem (Set.univ : Set (Fin 1)) := Or.inl rfl

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/basicOpen_empty_eq_singleton_top.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- The open point `{⊤}` is the basic open `[∅]`. -/
theorem basicOpen_empty_eq_singleton_top : O.basicOpen ∅ = {topElt} := by
  ext x
  rw [mem_basicOpen, mem_empty_iff_eq_top]
  exact Set.mem_singleton_iff.symm

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/botElt_le_topElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `⊥ ⊑ ⊤`. -/
theorem botElt_le_topElt : botElt ≤ topElt := O.bot_le _

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/botElt_ne_topElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `⊥ ≠ ⊤` (so `⊥ ⊏ ⊤`). -/
theorem botElt_ne_topElt : botElt ≠ topElt := by
  intro h
  have htop : topElt.mem ∅ := ⟨O_mem_empty, subset_rfl⟩
  rw [← h, mem_botElt] at htop
  exact univ_ne_empty htop.symm

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise215/not_isOpen_singleton_botElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise215

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **The opens of `|𝒪|`.** `{⊥}` is not open: `⊥` is the generic point. (The basic neighbourhood of
`⊥` is `[Δ] = |𝒪|`, which is not contained in `{⊥}` because it also contains `⊤`.) -/
theorem not_isOpen_singleton_botElt : ¬ IsOpen ({botElt} : Set O.Element) := by
  intro h
  obtain ⟨X, hX, hsub⟩ := h.out botElt rfl
  rw [mem_botElt] at hX
  subst hX
  have htop : topElt ∈ ({botElt} : Set O.Element) :=
    hsub (show topElt ∈ O.basicOpen Set.univ from (O_master ▸ topElt.master_mem))
  exact botElt_ne_topElt (Set.mem_singleton_iff.mp htop).symm

end DomainTheory.NeighbourhoodSystems.Exercise215
end

section
-- Exercise216/SatisfiesParityEquations.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The three equations of Exercise 2.16.** `f(1x) = true`, `f(01x) = false`, `f(00x) = f(x)`,
for *every* `x : |B|`. -/
structure SatisfiesParityEquations (g : ApproximableMap B Example23.T) : Prop where
  one : ∀ x : B.Element, g.toElementMap (sigmaElt [true] x) = Example23.trueElt
  zeroOne : ∀ x : B.Element, g.toElementMap (sigmaElt [false, true] x) = Example23.falseElt
  zeroZero : ∀ x : B.Element, g.toElementMap (sigmaElt [false, false] x) = g.toElementMap x

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise216/sigmaMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Exercise 2.16 — `x ↦ σx` is approximable.** The neighbourhood relation `X f Y ↔ σX ⊆ Y`
(confined to `B × B`). Definition 2.1: (i) `σΔ ⊆ Δ`; (ii) the prefixed cone `σX` is a common lower
bound of `Y, Y'`, witnessing `Y ∩ Y' ∈ B`; (iii) `prepend_mono` shrinks `σX'` as `X' ⊆ X`. -/
def sigmaMap (σ : Str) : ApproximableMap B B where
  rel X Y := B.mem X ∧ B.mem Y ∧ prepend σ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨B.master_mem, B.master_mem, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hpre : B.mem (prepend σ X) := memB_prepend σ hX
    have hsubInter : prepend σ X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, B.inter_mem hY hY' hpre hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', ((prepend_mono σ hX'X).trans hsub).trans hYY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise216/key.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **The recursive core of uniqueness.** Any `g` satisfying the three equations agrees with
`parityMap` on every principal (finite) element `σ⊥`. Recursion peels *two* tokens at a time
(mirroring `scan`'s own recursion `scan(00τ)=scanτ`): `1τ` and `01τ` are pinned directly by
`hg.one`/`hg.zeroOne` for *any* tail (no recursion needed there); `00τ` reduces to `τ` by
`hg.zeroZero`, decreasing structurally. The base case `σ = []` and the leftover singleton
`σ = [false]` (an odd trailing zero, never reached by the two-at-a-time step) are the two places
genuine order theory enters: `⊥ ≤ 1⊥` and `⊥ ≤ 01⊥` force `g(⊥) ≤ true` and `g(⊥) ≤ false`, and
`⊥` is the *only* element below both (`eq_botElt_of_le`, `𝒯`'s flatness); the singleton then
follows by squeezing `g(0⊥)` between `⊥` and `g(00⊥) = g(⊥)` via monotonicity. -/
theorem key (g : ApproximableMap B Example23.T) (hg : SatisfiesParityEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = Example23.valElt (Example23.scan σ)
  | [] => by
      rw [sigmaElt_nil]
      have h1 : g.toElementMap B.bot ≤ Example23.trueElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
        rwa [hg.one] at hm
      have h2 : g.toElementMap B.bot ≤ Example23.falseElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [false, true] B.bot))
        rwa [hg.zeroOne] at hm
      exact Example23.eq_botElt_of_le h1 h2
  | [false] => by
      have hbase : g.toElementMap B.bot = Example23.botElt := by
        have h0 := key g hg []
        rwa [sigmaElt_nil] at h0
      have hb : sigmaElt [false] B.bot ≤ sigmaElt [false, false] B.bot := by
        rw [sigmaElt_bot, sigmaElt_bot]
        exact (sigmaBot_le_iff _ _).mpr ⟨[false], rfl⟩
      have hm : g.toElementMap (sigmaElt [false] B.bot) ≤ Example23.botElt := by
        have := g.toElementMap_mono hb
        rwa [hg.zeroZero, hbase] at this
      have hm2 : Example23.botElt ≤ g.toElementMap (sigmaElt [false] B.bot) :=
        Example23.botElt_le _
      exact (le_antisymm hm hm2).trans rfl
  | (true :: t) => by
      rw [show (true :: t : Str) = [true] ++ t from rfl, sigmaElt_append, hg.one,
        Example23.scan_append_true]
      rfl
  | (false :: true :: t) => by
      rw [show (false :: true :: t : Str) = [false, true] ++ t from rfl, sigmaElt_append,
        hg.zeroOne, Example23.scan_append_falseTrue]
      rfl
  | (false :: false :: t) => by
      rw [show (false :: false :: t : Str) = [false, false] ++ t from rfl, sigmaElt_append,
        hg.zeroZero, key g hg t, Example23.scan_append_falseFalse]

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise216/eq_parityMap_of_satisfies.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Exercise 2.16, second half.** `parityMap` is the *unique* approximable map `B → T`
satisfying `f(1x)=true`, `f(01x)=false`, `f(00x)=f(x)`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = parityMap` to matching relations on cones,
which is exactly `key` read through `rel_iff_mem_principal`/`parityMap_rel_cone`. -/
theorem eq_parityMap_of_satisfies {g : ApproximableMap B Example23.T}
    (hg : SatisfiesParityEquations g) : g = Example23.parityMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ Example23.parityMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, Example23.parityMap_rel_cone]
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX,
      fun hr => absurd (Example23.parityMap.rel_dom hr) hX⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise216/parityMap_satisfies.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`parityMap` satisfies its own defining equations.** Each is a direct instance of the
"shift formula" `Example23.parityMap_toElementMap_sigmaElt`, using that a leading `1` (resp. `01`,
`00`) fixes the scan of the concatenation `σ ++ τ` regardless of the tail `τ`
(`scan_append_true`/`scan_append_falseTrue`/`scan_append_falseFalse`). -/
theorem parityMap_satisfies : SatisfiesParityEquations Example23.parityMap where
  one x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_true] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_true]⟩
  zeroOne x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_falseTrue] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_falseTrue]⟩
  zeroZero x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt, Example23.parityMap_toElementMap_mem]
    constructor
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse] at hval⟩
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse]⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise216/toElementMap_sigmaMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Exercise 2.16.** The elementwise action of `sigmaMap σ` is Scott's `σx`: `(sigmaMap σ)(x) =
σx` for every `x ∈ |B|`. -/
theorem toElementMap_sigmaMap (σ : Str) (x : B.Element) :
    (sigmaMap σ).toElementMap x = sigmaElt σ x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hxX, _, hY, hsub⟩
    exact ⟨hY, X, hxX, hsub⟩
  · rintro ⟨hY, X, hxX, hsub⟩
    exact ⟨X, hxX, x.sub hxX, hY, hsub⟩

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise216.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise216

set_option linter.unusedVariables false

theorem example_216 : And
  (∀
    {g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.Example23.T},
    DomainTheory.NeighbourhoodSystems.Exercise216.SatisfiesParityEquations g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.Example23.T)
        g DomainTheory.NeighbourhoodSystems.Example23.parityMap)
  (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise216.sigmaMap σ) x)
      (DomainTheory.NeighbourhoodSystems.ExampleB.sigmaElt σ x)) :=
  @And.intro
  (∀
    {g :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.Example23.T},
    DomainTheory.NeighbourhoodSystems.Exercise216.SatisfiesParityEquations g →
      @Eq
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.Example12.Token DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.Example23.T)
        g DomainTheory.NeighbourhoodSystems.Example23.parityMap)
  (∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
    (x :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise216.sigmaMap σ) x)
      (DomainTheory.NeighbourhoodSystems.ExampleB.sigmaElt σ x))
  (@DomainTheory.NeighbourhoodSystems.Exercise216.eq_parityMap_of_satisfies)
  DomainTheory.NeighbourhoodSystems.Exercise216.toElementMap_sigmaMap

end DomainTheory.NeighbourhoodSystems.Exercise216
end

section
-- Exercise218/hOut.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The guaranteed output of `h` on a finite prefix: each symbol `b` becomes the block `b0`. -/
def hOut : Str → Str
  | [] => []
  | b :: t => b :: false :: hOut t

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/hOut_nil.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem hOut_nil : hOut [] = [] := rfl

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/hOut_cons.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem hOut_cons (b : Bool) (t : Str) : hOut (b :: t) = b :: false :: hOut t := rfl

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/hOut_append.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `hOut` grows under extension: `hOut σ <+: hOut (σ ++ t)`. -/
theorem hOut_append (σ t : Str) : hOut σ <+: hOut (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons b s ih =>
    simp only [List.cons_append, hOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, List.cons_append, hu]⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/hOut_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **Prefix-monotonicity of `hOut`.** `σ <+: σ' → hOut σ <+: hOut σ'`. -/
theorem hOut_mono {σ σ' : Str} (h : σ <+: σ') : hOut σ <+: hOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact hOut_append σ t

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- The guaranteed output of `k` on a finite prefix: keep the first bit of every *complete* pair,
discard the inserted `0`. A trailing odd bit is an incomplete pair, hence dropped. -/
def kOut : Str → Str
  | [] => []
  | [_] => []
  | b :: _ :: t => b :: kOut t

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut_nil.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem kOut_nil : kOut [] = [] := rfl

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut_single.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem kOut_single (b : Bool) : kOut [b] = [] := rfl

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut_cons.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

@[simp] theorem kOut_cons (b c : Bool) (t : Str) : kOut (b :: c :: t) = b :: kOut t := rfl

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/hMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **Exercise 2.18 — the spacing map `h : 𝔹 → 𝔹`.** `X h Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ 𝔹 ∧ (hOut σ)Σ* ⊆ Y`.
Same shape as `Example24.runMap`, with the doubling `hOut` (`hOut_mono` gives Definition 2.1(iii)). -/
def hMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (hOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [hOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (hOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (hOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (hOut σ') ⊆ cone (hOut σ) := cone_subset_cone.mpr (hOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut_append.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- `kOut` grows under extension: `kOut σ <+: kOut (σ ++ t)`. -/
theorem kOut_append (σ t : Str) : kOut σ <+: kOut (σ ++ t) := by
  induction σ using kOut.induct with
  | case1 => simp
  | case2 _ => simp
  | case3 b c t' ih =>
    simp only [List.cons_append, kOut_cons]
    obtain ⟨u, hu⟩ := ih
    exact ⟨u, by rw [List.cons_append, hu]⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **Prefix-monotonicity of `kOut`.** `σ <+: σ' → kOut σ <+: kOut σ'`. -/
theorem kOut_mono {σ σ' : Str} (h : σ <+: σ') : kOut σ <+: kOut σ' := by
  obtain ⟨t, rfl⟩ := h
  exact kOut_append σ t

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap

/-- **Exercise 2.18 — the left inverse `k : 𝔹 → 𝔹`.** `X k Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ 𝔹 ∧ (kOut σ)Σ* ⊆ Y`. -/
def kMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (kOut σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [kOut_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (kOut σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (kOut σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp; rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (kOut σ') ⊆ cone (kOut σ) := cone_subset_cone.mpr (kOut_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kOut_hOut.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **`k` inverts `h` on prefixes.** `kOut (hOut σ) = σ`. -/
theorem kOut_hOut (σ : Str) : kOut (hOut σ) = σ := by
  induction σ with
  | nil => rfl
  | cons b t ih => simp only [hOut_cons, kOut_cons, ih]

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kMap_comp_hMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Exercise 2.18 — `k ∘ h = I_𝔹`.** The composite recovers the identity: reading `kOut (hOut σ) = σ`
through the cone relations. -/
theorem kMap_comp_hMap : kMap.comp hMap = idMap B := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨σ, hXcone, _, hYsub⟩, τ, hYcone, hZmem, hZsub⟩
    refine ⟨⟨σ, hXcone⟩, hZmem, ?_⟩
    have hτ : τ <+: hOut σ := cone_subset_cone.mp (hYcone ▸ hYsub)
    have hτσ : kOut τ <+: σ := by have := kOut_mono hτ; rwa [kOut_hOut] at this
    calc X = cone σ := hXcone
      _ ⊆ cone (kOut τ) := cone_subset_cone.mpr hτσ
      _ ⊆ Z := hZsub
  · rintro ⟨⟨σ, hXcone⟩, hZmem, hXZ⟩
    refine ⟨cone (hOut σ), ⟨σ, hXcone, memB_cone (hOut σ), subset_rfl⟩, hOut σ, rfl, hZmem, ?_⟩
    rw [kOut_hOut, hXcone] at *
    exact hXZ

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/toElementMap_hMap_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- The elementwise value of `hMap` on the finite element `↑(σΣ*)` is `↑((hOut σ)Σ*)`. -/
theorem toElementMap_hMap_cone (σ : Str) :
    hMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (hOut σ)) := by
  apply Element.ext
  intro Y
  rw [← hMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/toElementMap_kMap_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- The elementwise value of `kMap` on the finite element `↑(σΣ*)` is `↑((kOut σ)Σ*)`. -/
theorem toElementMap_kMap_cone (σ : Str) :
    kMap.toElementMap (B.principal (memB_cone σ)) = B.principal (memB_cone (kOut σ)) := by
  apply Element.ext
  intro Y
  rw [← kMap.rel_iff_mem_principal (memB_cone σ), mem_principal]
  constructor
  · rintro ⟨ρ, hcone, hYmem, hsub⟩
    have : σ = ρ := cone_injective hcone
    subst this
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/hMap_not_surjective.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Exercise 2.18 — `h` is not an isomorphism.** It is not surjective: `↑(01Σ*)` is not in the
range (any preimage `x` satisfies `x = k(h(x))`, forcing `h(x) = ↑(00Σ*) ≠ ↑(01Σ*)`). -/
theorem hMap_not_surjective : ¬ Function.Surjective hMap.toElementMap := by
  intro hsurj
  obtain ⟨x, hx⟩ := hsurj (B.principal (memB_cone [false, true]))
  have hkhx : kMap.toElementMap (hMap.toElementMap x) = x := by
    rw [← toElementMap_comp, kMap_comp_hMap, toElementMap_idMap]
  rw [hx, toElementMap_kMap_cone] at hkhx
  rw [← hkhx, toElementMap_hMap_cone] at hx
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) hx)
  simp at hcone

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218/kMap_not_injective.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB ApproximableMap


/-- **Exercise 2.18 — `k` is not one-one.** `↑(0Σ*)` and `↑(1Σ*)` are distinct finite elements that
`k` collapses to `⊥` (a length-1 prefix is an incomplete pair, so its bit is dropped). -/
theorem kMap_not_injective : ¬ Function.Injective kMap.toElementMap := by
  intro hinj
  have h1 : kMap.toElementMap (B.principal (memB_cone [false]))
      = kMap.toElementMap (B.principal (memB_cone [true])) := by
    rw [toElementMap_kMap_cone, toElementMap_kMap_cone]; rfl
  have h2 := hinj h1
  have hcone := cone_injective (B.principal_injective (memB_cone _) (memB_cone _) h2)
  simp at hcone

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise218.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise218

set_option linter.unusedVariables false

theorem example_218 : And
  (And
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)))
  (Not
    (@Function.Injective
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap))) :=
  @And.intro
  (And
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)))
  (Not
    (@Function.Injective
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap)))
  (@And.intro
    (Not
      (@Function.Surjective
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.B)
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
          DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
          DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.hMap)))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.ExampleB.B
        DomainTheory.NeighbourhoodSystems.ExampleB.B DomainTheory.NeighbourhoodSystems.Exercise218.kMap
        DomainTheory.NeighbourhoodSystems.Exercise218.hMap)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.B))
    DomainTheory.NeighbourhoodSystems.Exercise218.hMap_not_surjective
    DomainTheory.NeighbourhoodSystems.Exercise218.kMap_comp_hMap)
  DomainTheory.NeighbourhoodSystems.Exercise218.kMap_not_injective

end DomainTheory.NeighbourhoodSystems.Exercise218
end

section
-- Exercise220/powerSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — the powerset system `𝒫`.** Tokens `ℕ`; the neighbourhoods are the cofinite
sets, closed under finite intersection (`(X ∩ Y)ᶜ = Xᶜ ∪ Yᶜ`). -/
def powerSet : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]; exact hX.union hY
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/mem_powerSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_powerSet {X : Set ℕ} : powerSet.mem X ↔ Xᶜ.Finite := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/powerSet_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem powerSet_master : powerSet.master = (Set.univ : Set ℕ) := rfl

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/mem_compl_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The complement of a singleton is a neighbourhood (it represents the finite element `{n}`). -/
theorem mem_compl_singleton (n : ℕ) : powerSet.mem ({n}ᶜ) := by
  rw [mem_powerSet, compl_compl]; exact Set.finite_singleton n

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/powerSet_inter_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Cofinite sets are closed under intersection (witness-free form). -/
theorem powerSet_inter_mem {A B : Set ℕ} (hA : powerSet.mem A) (hB : powerSet.mem B) :
    powerSet.mem (A ∩ B) := by
  rw [mem_powerSet, Set.compl_inter]; exact hA.union hB

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/toSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The subset of `ℕ` represented by an element: `n ∈ toSet x ↔ {n}ᶜ ∈ x`. -/
def toSet (x : powerSet.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/mem_toSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_toSet {x : powerSet.Element} {n : ℕ} : n ∈ toSet x ↔ x.mem ({n}ᶜ) := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/mem_compl_of_finite.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Filters are determined on cofinite sets by their singleton-complements.** For cofinite `Z`,
`Z ∈ x ↔ ∀ n ∈ Zᶜ, {n}ᶜ ∈ x` (since `Z = ⋂_{n ∈ Zᶜ} {n}ᶜ`, a *finite* intersection). -/
theorem mem_compl_of_finite (x : powerSet.Element) {t : Set ℕ} (ht : t.Finite)
    (h : ∀ n ∈ t, x.mem ({n}ᶜ)) : x.mem (tᶜ) := by
  revert h
  induction t, ht using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ha _hsfin ih =>
    intro h
    have hcompl : (insert a s)ᶜ = ({a}ᶜ) ∩ (sᶜ) := by rw [Set.insert_eq, Set.compl_union]
    rw [hcompl]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/ofSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The filter of a subset `S ⊆ ℕ`: the cofinite `Z` with `Zᶜ ⊆ S`. -/
def ofSet (S : Set ℕ) : powerSet.Element where
  mem Z := powerSet.mem Z ∧ Zᶜ ⊆ S
  sub h := h.1
  master_mem := ⟨powerSet.master_mem, by rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset S⟩
  inter_mem := by
    rintro Z W ⟨hZ, hZS⟩ ⟨hW, hWS⟩
    refine ⟨powerSet_inter_mem hZ hW, ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hZS hWS
  up_mem := by
    rintro Z W ⟨hZ, hZS⟩ hW hZW
    exact ⟨hW, (Set.compl_subset_compl.mpr hZW).trans hZS⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/ofSet_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `ofSet` is monotone in the set. -/
theorem ofSet_mono {S S' : Set ℕ} (h : S ⊆ S') : ofSet S ≤ ofSet S' :=
  fun _ hZ => ⟨hZ.1, hZ.2.trans h⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/ofSet_toSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem ofSet_toSet (x : powerSet.Element) : ofSet (toSet x) = x := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hZsub⟩
    have hmem := mem_compl_of_finite x hZ (fun n hn => hZsub hn)
    rwa [compl_compl] at hmem
  · intro hZ
    refine ⟨x.sub hZ, ?_⟩
    intro n hn
    rw [mem_toSet]
    exact x.up_mem hZ (mem_compl_singleton n) (Set.subset_compl_singleton_iff.mpr hn)

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/predSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `S − 1 = {n ∣ n + 1 ∈ S}`. -/
def predSet (S : Set ℕ) : Set ℕ := {n | n + 1 ∈ S}

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/mem_predSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_predSet {S : Set ℕ} {n : ℕ} : n ∈ predSet S ↔ n + 1 ∈ S := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/interMap₂.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — `x ∩ y` is approximable (two variables).** `X, Y f Z ↔ X ∪ Y ⊆ Z`
(`(Xᶜ ∩ Yᶜ)ᶜ = X ∪ Y`). -/
def interMap₂ : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∪ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem,
    Set.union_subset (Set.subset_univ _) (Set.subset_univ _)⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.union_subset_union hX'X hY'Y).trans (hsub.trans hZZ')⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/predSet_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem predSet_mono {S T : Set ℕ} (h : S ⊆ T) : predSet S ⊆ predSet T := fun _ hn => h hn

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/predMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — `x − 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ − 1)`. -/
def predMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ predSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (predSet_mono (Set.compl_subset_compl.mpr hX'X)))

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/succSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `S + 1 = {n + 1 ∣ n ∈ S}`. -/
def succSet (S : Set ℕ) : Set ℕ := (· + 1) '' S

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/succSet_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem succSet_mono {S T : Set ℕ} (h : S ⊆ T) : succSet S ⊆ succSet T := Set.image_mono h

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/succMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — `x + 1` is approximable.** `X f Z ↔ Zᶜ ⊆ (Xᶜ + 1)`. -/
def succMap : ApproximableMap powerSet powerSet where
  rel X Z := powerSet.mem X ∧ powerSet.mem Z ∧ Zᶜ ⊆ succSet Xᶜ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨powerSet.master_mem, powerSet.master_mem, ?_⟩
    rw [powerSet_master, Set.compl_univ]; exact Set.empty_subset _
  inter_right := by
    rintro X Z Z' ⟨hX, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    refine ⟨hX, powerSet_inter_mem hZ hZ', ?_⟩
    rw [Set.compl_inter]; exact Set.union_subset hsub hsub'
  mono := by
    rintro X X' Z Z' ⟨_, _, hsub⟩ hX'X hZZ' hX' hZ'
    refine ⟨hX', hZ', ?_⟩
    exact (Set.compl_subset_compl.mpr hZZ').trans
      (hsub.trans (succSet_mono (Set.compl_subset_compl.mpr hX'X)))

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/toSet_ofSet.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem toSet_ofSet (S : Set ℕ) : toSet (ofSet S) = S := by
  ext n
  simp only [mem_toSet]
  constructor
  · rintro ⟨_, hsub⟩
    rw [compl_compl] at hsub
    exact hsub (Set.mem_singleton n)
  · intro hn
    exact ⟨mem_compl_singleton n, by rw [compl_compl]; exact Set.singleton_subset_iff.mpr hn⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/equivSetNat.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — the identification `|𝒫| ≅ (Set ℕ, ⊆)`.** -/
def equivSetNat : powerSet.Element ≃o Set ℕ where
  toFun := toSet
  invFun := ofSet
  left_inv := ofSet_toSet
  right_inv := toSet_ofSet
  map_rel_iff' := by
    intro x y
    show toSet x ≤ toSet y ↔ x ≤ y
    constructor
    · intro h
      have hmono := ofSet_mono h
      rwa [ofSet_toSet, ofSet_toSet] at hmono
    · intro h n hn
      exact h _ hn

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/unionMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 2.20 — `x ∪ y` is approximable (two variables).** `X, Y f Z ↔ X ∩ Y ⊆ Z`
(`(Xᶜ ∪ Yᶜ)ᶜ = X ∩ Y`). -/
def unionMap : ApproximableMap₂ powerSet powerSet powerSet where
  rel X Y Z := powerSet.mem X ∧ powerSet.mem Y ∧ powerSet.mem Z ∧ X ∩ Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨powerSet.master_mem, powerSet.master_mem, powerSet.master_mem, Set.inter_subset_left⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, powerSet_inter_mem hZ hZ', Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨_, _, _, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    exact ⟨hX', hY', hZ', (Set.inter_subset_inter hX'X hY'Y).trans (hsub.trans hZZ')⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/toSet_interMapu2082.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem toSet_interMap₂ (x y : powerSet.Element) :
    toSet (interMap₂.toElementMap₂ x y) = toSet x ∩ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_inter_iff]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    have hkX : k ∉ X := fun h => (hsub (Or.inl h)) rfl
    have hkY : k ∉ Y := fun h => (hsub (Or.inr h)) rfl
    exact ⟨x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX),
      y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)⟩
  · rintro ⟨hkx, hky⟩
    exact ⟨{k}ᶜ, {k}ᶜ, hkx, hky, mem_compl_singleton k, mem_compl_singleton k,
      mem_compl_singleton k, Set.union_subset subset_rfl subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/toSet_predMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem toSet_predMap (x : powerSet.Element) :
    toSet (predMap.toElementMap x) = predSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap, mem_predSet]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    have hk : k + 1 ∈ Xᶜ := hsub (Set.mem_singleton k)
    exact x.up_mem hxX (mem_compl_singleton (k + 1)) (Set.subset_compl_singleton_iff.mpr hk)
  · intro hk
    refine ⟨{k + 1}ᶜ, hk, mem_compl_singleton (k + 1), mem_compl_singleton k, ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    rw [mem_predSet, compl_compl]
    exact Set.mem_singleton (a + 1)

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/toSet_succMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem toSet_succMap (x : powerSet.Element) :
    toSet (succMap.toElementMap x) = succSet (toSet x) := by
  ext k
  simp only [mem_toSet, ApproximableMap.mem_toElementMap]
  constructor
  · rintro ⟨X, hxX, _, _, hsub⟩
    rw [compl_compl] at hsub
    obtain ⟨m, hm, rfl⟩ := hsub (Set.mem_singleton k)
    exact ⟨m, x.up_mem hxX (mem_compl_singleton m) (Set.subset_compl_singleton_iff.mpr hm), rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨{m}ᶜ, hm, mem_compl_singleton m, mem_compl_singleton (m + 1), ?_⟩
    rw [compl_compl]
    intro a ha
    rw [Set.mem_singleton_iff] at ha; subst ha
    exact ⟨m, by rw [compl_compl]; exact Set.mem_singleton m, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220/toSet_unionMap.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem toSet_unionMap (x y : powerSet.Element) :
    toSet (unionMap.toElementMap₂ x y) = toSet x ∪ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_union]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    by_cases hkX : k ∈ X
    · refine Or.inr ?_
      have hkY : k ∉ Y := fun hkY => (hsub ⟨hkX, hkY⟩) rfl
      exact y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)
    · exact Or.inl (x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX))
  · rintro (hkx | hky)
    · exact ⟨{k}ᶜ, Set.univ, hkx, y.master_mem, mem_compl_singleton k, powerSet.master_mem,
        mem_compl_singleton k, Set.inter_subset_left⟩
    · exact ⟨Set.univ, {k}ᶜ, x.master_mem, hky, powerSet.master_mem, mem_compl_singleton k,
        mem_compl_singleton k, Set.inter_subset_right⟩

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise220.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise220

set_option linter.unusedVariables false

theorem example_220 : ∀
  (x y :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
      DomainTheory.NeighbourhoodSystems.Exercise220.powerSet),
  @Eq (Set Nat)
    (DomainTheory.NeighbourhoodSystems.Exercise220.toSet
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.toElementMap₂ Nat Nat Nat
        DomainTheory.NeighbourhoodSystems.Exercise220.powerSet DomainTheory.NeighbourhoodSystems.Exercise220.powerSet
        DomainTheory.NeighbourhoodSystems.Exercise220.powerSet DomainTheory.NeighbourhoodSystems.Exercise220.unionMap x
        y))
    (@Union.union (Set Nat) (@Set.instUnion Nat) (DomainTheory.NeighbourhoodSystems.Exercise220.toSet x)
      (DomainTheory.NeighbourhoodSystems.Exercise220.toSet y)) :=
  DomainTheory.NeighbourhoodSystems.Exercise220.toSet_unionMap

end DomainTheory.NeighbourhoodSystems.Exercise220
end

section
-- Exercise221/cone_not_subset_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- A singleton is never a cone (a cone has at least two elements `σ` and `σ0`). -/
theorem cone_not_subset_singleton (σ τ : Str) : ¬ cone σ ⊆ ({τ} : Set Str) := by
  intro h
  have h1 : σ ∈ ({τ} : Set Str) := h (mem_cone.mpr List.prefix_rfl)
  have h2 : (σ ++ [false]) ∈ ({τ} : Set Str) := h (mem_cone.mpr (List.prefix_append σ [false]))
  rw [Set.mem_singleton_iff] at h1 h2
  rw [← h1] at h2
  have hlen := congrArg List.length h2
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/cone_ne_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Cones and singletons are distinct neighbourhoods. -/
theorem cone_ne_singleton (σ τ : Str) : cone σ ≠ ({τ} : Set Str) := by
  intro h
  refine cone_not_subset_singleton σ τ ?_
  intro x hx
  rw [← h]; exact hx

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/cone_singleton_nd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Nested-or-disjoint for a cone vs. a terminator singleton: `{τ} ⊆ σΣ*` iff `σ ⪯ τ`, else
disjoint. Choice-free (`σ <+: τ` is decidable). -/
theorem cone_singleton_nd (σ τ : Str) :
    cone σ ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ cone σ ∨ cone σ ∩ ({τ} : Set Str) = ∅ :=
  if h : σ <+: τ then
    Or.inr (Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h)))
  else
    Or.inr (Or.inr (by
      ext w
      simp only [Set.mem_inter_iff, mem_cone, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro hw rfl
      exact h hw))

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/memC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Membership in `𝒞`: `X` is either a cone `σΣ*` (as in `𝔹`) or a terminator singleton `{σ}`. -/
def memC (X : Set Str) : Prop := (∃ σ, X = cone σ) ∨ (∃ σ, X = {σ})

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/singleton_cone_nd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Nested-or-disjoint for a terminator singleton vs. a cone (the mirror of `cone_singleton_nd`). -/
theorem singleton_cone_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ cone τ ∨ cone τ ⊆ ({σ} : Set Str) ∨ ({σ} : Set Str) ∩ cone τ = ∅ :=
  if h : τ <+: σ then
    Or.inl (Set.singleton_subset_iff.mpr (mem_cone.mpr h))
  else
    Or.inr (Or.inr (by
      ext w
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, mem_cone, Set.mem_empty_iff_false,
        iff_false, not_and]
      rintro rfl hw
      exact h hw))

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/singleton_singleton_nd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Nested-or-disjoint for two terminator singletons: equal or disjoint. -/
theorem singleton_singleton_nd (σ τ : Str) :
    ({σ} : Set Str) ⊆ ({τ} : Set Str) ∨ ({τ} : Set Str) ⊆ ({σ} : Set Str) ∨
      ({σ} : Set Str) ∩ ({τ} : Set Str) = ∅ := by
  by_cases h : σ = τ
  · subst h; exact Or.inl subset_rfl
  · refine Or.inr (Or.inr ?_)
    ext w
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
      not_and]
    rintro rfl h2
    exact h h2

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/nestedOrDisjoint_C.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **`𝒞` is pairwise nested-or-disjoint.** Cone/cone is the `𝔹` trichotomy; the mixed and
singleton/singleton cases are the three lemmas above. -/
theorem nestedOrDisjoint_C : NestedOrDisjoint memC := by
  rintro X Y hX hY
  rcases hX with ⟨σ, rfl⟩ | ⟨σ, rfl⟩ <;> rcases hY with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
  · exact cone_trichotomy σ τ
  · exact cone_singleton_nd σ τ
  · exact singleton_cone_nd σ τ
  · exact singleton_singleton_nd σ τ

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/C.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The system `𝒞`** on `Δ = Σ*`: cones and terminator singletons. -/
def C : NeighborhoodSystem Str :=
  ofNestedOrDisjoint memC Set.univ ⟨[], Set.mem_univ _⟩
    (Or.inl ⟨[], cone_nil.symm⟩) nestedOrDisjoint_C
    (by rintro X (⟨σ, rfl⟩ | ⟨σ, rfl⟩) <;> exact Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/C_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem C_mem {X : Set Str} : C.mem X ↔ memC X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/C_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem C_master : C.master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/memC_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Every cone is a neighbourhood of `𝒞` — this is the inclusion `𝔹 ⊆ 𝒞`. -/
theorem memC_cone (σ : Str) : C.mem (cone σ) := Or.inl ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/memC_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Every terminator singleton `{σ}` is a neighbourhood of `𝒞`. -/
theorem memC_singleton (σ : Str) : C.mem ({σ} : Set Str) := Or.inr ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/prepend_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Prepending is monotone in the suffix set. -/
theorem prepend_mono (σ : Str) {Y Y' : Set Str} (h : Y' ⊆ Y) : prepend σ Y' ⊆ prepend σ Y := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/prepend_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `σ{ρ} = {σρ}`: prepending `σ` to a terminator singleton. -/
theorem prepend_singleton (σ ρ : Str) : prepend σ ({ρ} : Set Str) = ({σ ++ ρ} : Set Str) := by
  ext w
  simp only [mem_prepend, Set.mem_singleton_iff]
  constructor
  · rintro ⟨τ, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨ρ, rfl, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/memC_prepend.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- Prepending preserves `𝒞`-membership (cone ↦ cone, singleton ↦ singleton). -/
theorem memC_prepend (σ : Str) {Y : Set Str} (hY : C.mem Y) : C.mem (prepend σ Y) := by
  rcases hY with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · rw [prepend_cone]; exact memC_cone (σ ++ ρ)
  · rw [prepend_singleton]; exact memC_singleton (σ ++ ρ)

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/prepend_subset_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `σY ⊆ σΣ* = cone σ`: prepending `σ` always lands inside the cone of `σ`. -/
theorem prepend_subset_cone (σ : Str) (Y : Set Str) : prepend σ Y ⊆ cone σ := by
  rintro w ⟨τ, _, rfl⟩
  exact mem_cone.mpr (List.prefix_append σ τ)

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/singletonElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The **total finite sequence** `σ` as an element of `|𝒞|`: the principal filter `↑{σ}`. -/
def singletonElt (σ : Str) : C.Element := C.principal (memC_singleton σ)

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/Lambda.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- `Λ`, the **total empty sequence** (terminated): `↑{[]}`. -/
def Lambda : C.Element := singletonElt []

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/subset_singleton_eq.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- A nonempty `𝒞`-neighbourhood contained in a singleton *is* that singleton. -/
theorem subset_singleton_eq {W : Set Str} {σ : Str} (hW : C.mem W) (hsub : W ⊆ ({σ} : Set Str)) :
    W = ({σ} : Set Str) := by
  rcases hW with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact absurd hsub (cone_not_subset_singleton ρ σ)
  · rw [Set.singleton_subset_iff, Set.mem_singleton_iff] at hsub
    rw [hsub]

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/juxtapose.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **Juxtaposition `xy`** as an approximable map `𝒞 × 𝒞 → 𝒞`.

The relation `X, Y j Z` reads off the *left-to-right bias*: if the first input neighbourhood `X` is
a cone `σΣ*` (`x` extends `σ` but is undetermined), the output only commits to the prefix `σ`
(`σΣ* ⊆ Z`), ignoring `Y`; if `X` is a terminator `{σ}` (`x` is the total finite sequence `σ`), the
output prepends `σ` to the second input `Y` (`σY ⊆ Z`). -/
def juxtapose : ApproximableMap₂ C C C where
  rel X Y Z := C.mem Y ∧ C.mem Z ∧
    ((∃ σ, X = cone σ ∧ cone σ ⊆ Z) ∨ (∃ σ, X = ({σ} : Set Str) ∧ prepend σ Y ⊆ Z))
  rel_dom₀ := by
    rintro X Y Z ⟨_, _, (⟨σ, rfl, _⟩ | ⟨σ, rfl, _⟩)⟩
    · exact memC_cone σ
    · exact memC_singleton σ
  rel_dom₁ := fun ⟨hY, _, _⟩ => hY
  rel_cod := fun ⟨_, hZ, _⟩ => hZ
  master_rel := ⟨C.master_mem, C.master_mem,
    Or.inl ⟨[], C_master.trans cone_nil.symm, by rw [C_master]; exact Set.subset_univ _⟩⟩
  inter_right := by
    rintro X Y Z Z' ⟨hY, hZ, hd⟩ ⟨_, hZ', hd'⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hd' with ⟨σ', hX', hsub'⟩ | ⟨σ', hX', _⟩
      · obtain rfl : σ = σ' := cone_injective hX'
        exact ⟨hY, C.inter_mem hZ hZ' (memC_cone σ) (Set.subset_inter hsub hsub'),
          Or.inl ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
      · exact absurd hX' (cone_ne_singleton σ σ')
    · rcases hd' with ⟨σ', hX', _⟩ | ⟨σ', hX', hsub'⟩
      · exact absurd hX'.symm (cone_ne_singleton σ' σ)
      · obtain rfl : σ = σ' := by
          have := hX'; rw [Set.singleton_eq_singleton_iff] at this; exact this
        exact ⟨hY, C.inter_mem hZ hZ' (memC_prepend σ hY) (Set.subset_inter hsub hsub'),
          Or.inr ⟨σ, rfl, Set.subset_inter hsub hsub'⟩⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hY, _, hd⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hY', hZ', ?_⟩
    rcases hd with ⟨σ, rfl, hsub⟩ | ⟨σ, rfl, hsub⟩
    · rcases hX' with ⟨σ', rfl⟩ | ⟨σ', rfl⟩
      · exact Or.inl ⟨σ', rfl, (hX'X.trans hsub).trans hZZ'⟩
      · refine Or.inr ⟨σ', rfl, ?_⟩
        have hσσ' : σ <+: σ' := mem_cone.mp (Set.singleton_subset_iff.mp hX'X)
        have h2 : cone σ' ⊆ cone σ := cone_subset_cone.mpr hσσ'
        exact ((prepend_subset_cone σ' Y').trans (h2.trans hsub)).trans hZZ'
    · obtain rfl : X' = ({σ} : Set Str) := subset_singleton_eq hX' hX'X
      exact Or.inr ⟨σ, rfl, ((prepend_mono σ hY'Y).trans hsub).trans hZZ'⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/bot_lt_Lambda.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`⊥ ⊏ Λ`.** The undefined sequence `⊥ = ↑Δ` is strictly below the total empty sequence
`Λ = ↑{[]}`: they are distinct because `⊥` contains only `Δ`, whereas `Λ` contains `{[]} ≠ Δ`. -/
theorem bot_lt_Lambda : C.bot < Lambda := by
  refine lt_of_le_of_ne (C.bot_le _) ?_
  intro h
  have hmem : C.bot.mem ({([] : Str)} : Set Str) := by
    rw [h]; exact ⟨memC_singleton [], subset_rfl⟩
  rw [C.mem_bot, C_master] at hmem
  have h2 : ([true] : Str) ∈ ({([] : Str)} : Set Str) := by rw [hmem]; trivial
  rw [Set.mem_singleton_iff] at h2
  exact absurd h2 (by decide)

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/isTotal_singletonElt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Total finite sequences.** `↑{σ}` is a total (maximal) element of `|𝒞|`: any element above it
must equal it, because `{σ}` is a minimal nonempty neighbourhood. This is what was *false* in `𝔹`,
where finite sequences gave only the partial `σ⊥`. -/
theorem isTotal_singletonElt (σ : Str) : C.IsTotal (singletonElt σ) := by
  intro y hy Z hZ
  have hσy : y.mem ({σ} : Set Str) := hy {σ} ⟨memC_singleton σ, subset_rfl⟩
  have hinter : y.mem (({σ} : Set Str) ∩ Z) := y.inter_mem hσy hZ
  have hmemC : C.mem (({σ} : Set Str) ∩ Z) := y.sub hinter
  have heq : ({σ} : Set Str) ∩ Z = ({σ} : Set Str) :=
    subset_singleton_eq hmemC Set.inter_subset_left
  exact ⟨y.sub hZ, by rw [← heq]; exact Set.inter_subset_right⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/juxtapose_cone.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **Left-to-right bias / "`x` infinite ⟹ `xy = x`".** On a partial input `σ⊥ = ↑(σΣ*)` the
juxtaposition returns `σ⊥` itself, *independently of `y`*. Since an infinite (total) sequence is the
directed union of its finite approximants `σ⊥`, this says `xy = x` for total infinite `x`. -/
theorem juxtapose_cone (σ : Str) (y : C.Element) :
    juxtapose.toElementMap₂ (C.principal (memC_cone σ)) y = C.principal (memC_cone σ) := by
  apply Element.ext
  intro Z
  constructor
  · rintro ⟨X, Y, ⟨_, hconeX⟩, _, hY, hZ, hd⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, _⟩
    · exact ⟨hZ, hconeX.trans hsub⟩
    · exact absurd hconeX (cone_not_subset_singleton σ ρ)
  · rintro ⟨hZ, hconeσZ⟩
    exact ⟨cone σ, C.master, ⟨memC_cone σ, subset_rfl⟩, y.master_mem, C.master_mem, hZ,
      Or.inl ⟨σ, rfl, hconeσZ⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/juxtapose_singleton_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`σy` for a total finite `x = ↑{σ}`.** When the first argument is the total finite sequence
`σ`, juxtaposition prepends `σ` to `y`: `Z ∈ (↑{σ})y` iff `Z` contains `σY'` for some `Y' ∈ y`. The
coarser cone witnesses `σΣ* ∈ ↑{σ}` add nothing, since `σΔ = σΣ*` is itself of the form `σY'`. -/
theorem juxtapose_singleton_mem (σ : Str) (y : C.Element) {Z : Set Str} :
    (juxtapose.toElementMap₂ (singletonElt σ) y).mem Z ↔
      C.mem Z ∧ ∃ Y', y.mem Y' ∧ prepend σ Y' ⊆ Z := by
  constructor
  · rintro ⟨X, Y, ⟨_, hsingleX⟩, hYmem, _, hZ, hd⟩
    refine ⟨hZ, ?_⟩
    rcases hd with ⟨ρ, rfl, hsub⟩ | ⟨ρ, rfl, hsub⟩
    · have hρσ : ρ <+: σ := mem_cone.mp (Set.singleton_subset_iff.mp hsingleX)
      refine ⟨C.master, y.master_mem, ?_⟩
      rw [C_master, prepend_univ]
      exact (cone_subset_cone.mpr hρσ).trans hsub
    · obtain rfl : σ = ρ := by
        have := Set.singleton_subset_iff.mp hsingleX
        rwa [Set.mem_singleton_iff] at this
      exact ⟨Y, hYmem, hsub⟩
  · rintro ⟨hZ, Y', hY'mem, hsub⟩
    exact ⟨{σ}, Y', ⟨memC_singleton σ, subset_rfl⟩, hY'mem, y.sub hY'mem, hZ,
      Or.inr ⟨σ, rfl, hsub⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

set_option linter.unusedVariables false

theorem example_221 : ∀ (σ : DomainTheory.NeighbourhoodSystems.ExampleB.Str)
  (y :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Exercise221.C)
  {Z : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str},
  Iff
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
      DomainTheory.NeighbourhoodSystems.Exercise221.C
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap₂.toElementMap₂ DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Exercise221.C DomainTheory.NeighbourhoodSystems.Exercise221.C
        DomainTheory.NeighbourhoodSystems.Exercise221.C DomainTheory.NeighbourhoodSystems.Exercise221.juxtapose
        (DomainTheory.NeighbourhoodSystems.Exercise221.singletonElt σ) y)
      Z)
    (And
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem DomainTheory.NeighbourhoodSystems.ExampleB.Str
        DomainTheory.NeighbourhoodSystems.Exercise221.C Z)
      (∃ (Y' : Set DomainTheory.NeighbourhoodSystems.ExampleB.Str),
        And
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
            DomainTheory.NeighbourhoodSystems.ExampleB.Str DomainTheory.NeighbourhoodSystems.Exercise221.C y Y')
          (@LE.le (Set DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (@Set.instLE DomainTheory.NeighbourhoodSystems.ExampleB.Str)
            (DomainTheory.NeighbourhoodSystems.ExampleB.prepend σ Y') Z))) :=
  DomainTheory.NeighbourhoodSystems.Exercise221.juxtapose_singleton_mem

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/memB_imp_memC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- **`𝔹 ⊆ 𝒞`.** Every neighbourhood of `𝔹` is a neighbourhood of `𝒞`. -/
theorem memB_imp_memC {X : Set Str} (hX : B.mem X) : C.mem X := by
  obtain ⟨σ, rfl⟩ := hX; exact memC_cone σ

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- Exercise221/memC_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise221

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Every neighbourhood of `𝒞` is nonempty (there is no empty token). -/
theorem memC_nonempty {W : Set Str} (hW : C.mem W) : W.Nonempty := by
  rcases hW with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨σ, mem_cone.mpr List.prefix_rfl⟩
  · exact ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise221
end

section
-- IsTok.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- A token: a finite set included in some member of `C`. -/
class IsTok (F : Set τ) : Prop where
  out : F.Finite ∧ ∃ X ∈ C, F ⊆ X

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- Tok.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- Scott's `Δ`: the type of tokens (finite sets included in members of `C`). -/
abbrev Tok := {F : Set τ // IsTok C F}

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- nbhd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

/-- Scott's neighbourhood `C(F) = {G ∈ Δ ∣ F ⊆ Ḡ}`. -/
def nbhd (F : Set τ) : Set (Tok C) := {G | F ⊆ Cl C G.1}

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- mem_nbhd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

@[simp] theorem mem_nbhd {F : Set τ} {G : Tok C} : G ∈ nbhd C F ↔ F ⊆ Cl C G.1 := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- botTok.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

include hne in
/-- The empty token `∅ ∈ Δ` (needs `C` non-empty for `∅` to lie in some member). -/
def botTok : Tok C := ⟨∅, ⟨⟨Set.finite_empty, hne.choose, hne.choose_spec, Set.empty_subset _⟩⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- nbhd_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

/-- `C(∅) = Δ`: the empty token's neighbourhood is everything (the master). -/
theorem nbhd_empty : nbhd C (∅ : Set τ) = Set.univ := by
  ext G
  simp [nbhd]

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- subset_Cl.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

/-- `F ⊆ F̄`: a set is contained in its closure. -/
theorem subset_Cl (F : Set τ) : F ⊆ Cl C F := by
  intro t ht
  rw [Cl, Set.mem_sInter]
  intro X hX
  exact hX.2 ht

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- nbhd_subset_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

include hInter in
/-- `C(F) ⊆ C(G) ↔ G ⊆ F̄`: comparison of neighbourhoods reduces to inclusion against closures. -/
theorem nbhd_subset_iff {F G : Set τ} (hF : IsTok C F) :
    nbhd C F ⊆ nbhd C G ↔ G ⊆ Cl C F := by
  constructor
  · intro h
    have hmem : (⟨F, hF⟩ : Tok C) ∈ nbhd C F := subset_Cl C F
    exact h hmem
  · intro hG H hH
    exact hG.trans (Cl_subset C (Cl_mem C hInter H.2.out.2) hH)

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- reprSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

include hInter hne in
/-- **The representation neighbourhood system** `reprSystem` over `Δ = Tok C`: neighbourhoods are
exactly the `C(F)` for tokens `F`, the master is all of `Δ = C(∅)`. -/
def reprSystem : NeighborhoodSystem (Tok C) where
  mem N := ∃ F : Tok C, N = nbhd C F.1
  master := Set.univ
  master_nonempty := ⟨botTok C hne, Set.mem_univ _⟩
  master_mem := ⟨botTok C hne, (nbhd_empty C).symm⟩
  inter_mem := by
    rintro X Y Z ⟨F, rfl⟩ ⟨F', rfl⟩ ⟨F'', rfl⟩ hZsub
    have hF''mem : (F'' : Tok C) ∈ nbhd C F''.1 := subset_Cl C F''.1
    have h := hZsub hF''mem
    have hClF'' : Cl C F''.1 ∈ C := Cl_mem C hInter F''.2.out.2
    have hunionsub : F.1 ∪ F'.1 ⊆ Cl C F''.1 := Set.union_subset h.1 h.2
    refine ⟨⟨F.1 ∪ F'.1, ⟨⟨F.2.out.1.union F'.2.out.1, Cl C F''.1, hClF'', hunionsub⟩⟩⟩, ?_⟩
    ext G
    simp only [mem_nbhd, Set.mem_inter_iff, Set.union_subset_iff]
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- mem_reprSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

@[simp] theorem mem_reprSystem {N : Set (Tok C)} :
    (reprSystem C hInter hne).mem N ↔ ∃ F : Tok C, N = nbhd C F.1 := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- reprSystem_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

@[simp] theorem reprSystem_master : (reprSystem C hInter hne).master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- directed_step.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Directedness step.** If `C(F), C(F') ∈ x` then there is a token `F₃` with `C(F₃) ∈ x` whose
closure dominates both `F̄` and `F̄'`. (From the filter intersection `C(F) ∩ C(F') ∈ x`, which is
some `C(F₃)`.) -/
theorem directed_step (x : (reprSystem C hInter hne).Element) {F F' : Tok C}
    (hF : x.mem (nbhd C F.1)) (hF' : x.mem (nbhd C F'.1)) :
    ∃ F₃ : Tok C, x.mem (nbhd C F₃.1) ∧ Cl C F.1 ⊆ Cl C F₃.1 ∧ Cl C F'.1 ⊆ Cl C F₃.1 := by
  have hinter : x.mem (nbhd C F.1 ∩ nbhd C F'.1) := x.inter_mem hF hF'
  have hmemD : (reprSystem C hInter hne).mem (nbhd C F.1 ∩ nbhd C F'.1) := x.sub hinter
  obtain ⟨F₃, hF₃eq⟩ := hmemD
  rw [hF₃eq] at hinter
  have hF₃self : (F₃ : Tok C) ∈ nbhd C F₃.1 := subset_Cl C F₃.1
  rw [← hF₃eq] at hF₃self
  refine ⟨F₃, hinter, ?_, ?_⟩
  · exact Cl_subset C (Cl_mem C hInter F₃.2.out.2) hF₃self.1
  · exact Cl_subset C (Cl_mem C hInter F₃.2.out.2) hF₃self.2

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- famC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- The family `{F̄ ∣ C(F) ∈ x}` of finite-element closures present in the ideal element `x`. -/
def famC (x : (reprSystem C hInter hne).Element) : Set (Set τ) :=
  {Y | ∃ F : Tok C, x.mem (nbhd C F.1) ∧ Y = Cl C F.1}

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- mem_nbhd_bot.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- The empty token's neighbourhood `C(∅) = Δ` is in every element (it is the master). -/
theorem mem_nbhd_bot (x : (reprSystem C hInter hne).Element) :
    x.mem (nbhd C (botTok C hne).1) := by
  have h : (botTok C hne).1 = (∅ : Set τ) := rfl
  rw [h, nbhd_empty C]
  exact x.master_mem

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- ofC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- The ideal element generated by `X ∈ C`: it contains the neighbourhoods above some `C(F)` with
`F ⊆ X`. -/
def ofC (X : Set τ) (hX : X ∈ C) : (reprSystem C hInter hne).Element where
  mem N := (reprSystem C hInter hne).mem N ∧ ∃ F : Tok C, F.1 ⊆ X ∧ nbhd C F.1 ⊆ N
  sub h := h.1
  master_mem :=
    ⟨(reprSystem C hInter hne).master_mem, botTok C hne, Set.empty_subset X, Set.subset_univ _⟩
  inter_mem := by
    rintro N M ⟨hN, F, hFX, hFN⟩ ⟨hM, F', hF'X, hF'M⟩
    have htok : IsTok C (F.1 ∪ F'.1) :=
      ⟨⟨F.2.out.1.union F'.2.out.1, X, hX, Set.union_subset hFX hF'X⟩⟩
    have hsub : nbhd C (F.1 ∪ F'.1) ⊆ N ∩ M := by
      intro G hG
      rw [mem_nbhd, Set.union_subset_iff] at hG
      exact ⟨hFN hG.1, hF'M hG.2⟩
    exact ⟨(reprSystem C hInter hne).inter_mem hN hM ⟨⟨_, htok⟩, rfl⟩ hsub,
      ⟨F.1 ∪ F'.1, htok⟩, Set.union_subset hFX hF'X, hsub⟩
  up_mem := by
    rintro N M ⟨_, F, hFX, hFN⟩ hM hNM
    exact ⟨hM, F, hFX, hFN.trans hNM⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- toC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- Scott's `⋃ {F̄ ∣ C(F) ∈ x}`: the set of `C` represented by the ideal element `x`. -/
def toC (x : (reprSystem C hInter hne).Element) : Set τ := ⋃₀ famC C hInter hne x

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- mem_toC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

theorem mem_toC (x : (reprSystem C hInter hne).Element) {t : τ} :
    t ∈ toC C hInter hne x ↔ ∃ F : Tok C, x.mem (nbhd C F.1) ∧ t ∈ Cl C F.1 := by
  simp only [toC, famC, Set.mem_sUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨Y, ⟨F, hF, rfl⟩, ht⟩
    exact ⟨F, hF, ht⟩
  · rintro ⟨F, hF, ht⟩
    exact ⟨Cl C F.1, ⟨F, hF, rfl⟩, ht⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- exists_tok_of_finite_subset.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Finite sets are captured by a single token.** A finite `s ⊆ toC x` is contained in some `F̄`
with `C(F) ∈ x` — the finite-subcover property of the directed union `toC x`. -/
theorem exists_tok_of_finite_subset (x : (reprSystem C hInter hne).Element) {s : Set τ}
    (hs : s.Finite) (hsub : s ⊆ toC C hInter hne x) :
    ∃ F : Tok C, x.mem (nbhd C F.1) ∧ s ⊆ Cl C F.1 := by
  revert hsub
  induction s, hs using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨botTok C hne, mem_nbhd_bot C hInter hne x, Set.empty_subset _⟩
  | @insert a s _ha _hsfin ih =>
    intro hsub
    have ha' : a ∈ toC C hInter hne x := hsub (Set.mem_insert a s)
    rw [mem_toC] at ha'
    obtain ⟨Fa, hFa, haCl⟩ := ha'
    obtain ⟨Fs, hFs, hsCl⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem a hy))
    obtain ⟨F₃, hF₃, hFaF₃, hFsF₃⟩ := directed_step C hInter hne x hFa hFs
    refine ⟨F₃, hF₃, ?_⟩
    rw [Set.insert_subset_iff]
    exact ⟨hFaF₃ haCl, hsCl.trans hFsF₃⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- mem_nbhd_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Key membership identity.** `C(G) ∈ x ↔ G ⊆ toC x`. Forward: `G ⊆ Ḡ ⊆ toC x`. Reverse: `G` is
finite, so the finite-subcover lemma gives `F` with `C(F) ∈ x` and `G ⊆ F̄`, whence `C(F) ⊆ C(G)`
and upward closure gives `C(G) ∈ x`. -/
theorem mem_nbhd_iff (x : (reprSystem C hInter hne).Element) (G : Tok C) :
    x.mem (nbhd C G.1) ↔ G.1 ⊆ toC C hInter hne x := by
  constructor
  · intro hx t ht
    rw [mem_toC]
    exact ⟨G, hx, subset_Cl C G.1 ht⟩
  · intro hsub
    obtain ⟨F, hF, hGF⟩ := exists_tok_of_finite_subset C hInter hne x G.2.out.1 hsub
    have hnsub : nbhd C F.1 ⊆ nbhd C G.1 := (nbhd_subset_iff C hInter F.2).mpr hGF
    exact x.up_mem hF ⟨G, rfl⟩ hnsub

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- toC_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/-- `toC x ∈ C`: the represented set lies in the family (closure under directed unions). -/
theorem toC_mem (x : (reprSystem C hInter hne).Element) : toC C hInter hne x ∈ C := by
  show ⋃₀ famC C hInter hne x ∈ C
  apply hDir (famC C hInter hne x)
  · exact ⟨Cl C (botTok C hne).1, botTok C hne, mem_nbhd_bot C hInter hne x, rfl⟩
  · rintro Y ⟨F, _, rfl⟩
    exact Cl_mem C hInter F.2.out.2
  · rintro Y ⟨F, hF, rfl⟩ Y' ⟨F', hF', rfl⟩
    obtain ⟨F₃, hF₃, hFF₃, hF'F₃⟩ := directed_step C hInter hne x hF hF'
    exact ⟨Cl C F₃.1, ⟨F₃, hF₃, rfl⟩, hFF₃, hF'F₃⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- ofC_toC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

/-- The other round-trip `ofC (toC x) = x`. -/
theorem ofC_toC (x : (reprSystem C hInter hne).Element) :
    ofC C hInter hne (toC C hInter hne x) (toC_mem C hInter hne hDir x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨hN, F, hFtoC, hFN⟩
    have hxF : x.mem (nbhd C F.1) := (mem_nbhd_iff C hInter hne x F).mpr hFtoC
    exact x.up_mem hxF hN hFN
  · intro hxN
    have hN : (reprSystem C hInter hne).mem N := x.sub hxN
    obtain ⟨G, rfl⟩ := hN
    have hGtoC : G.1 ⊆ toC C hInter hne x := (mem_nbhd_iff C hInter hne x G).mp hxN
    exact ⟨⟨G, rfl⟩, G, hGtoC, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- Exercise222.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))


variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)


variable (hne : C.Nonempty)


variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)


end DomainTheory.NeighbourhoodSystems.Exercise222

namespace DomainTheory.NeighbourhoodSystems.Exercise222

set_option linter.unusedVariables false

theorem example_222.{u_1} : ∀ {τ : Type u_1} (C : Set (Set τ))
  (hInter :
    ∀ (𝒮 : Set (Set τ)),
      @Set.Nonempty (Set τ) 𝒮 →
        @LE.le (Set (Set τ)) (@Set.instLE (Set τ)) 𝒮 C →
          @Membership.mem (Set τ) (Set (Set τ)) (@Set.instMembership (Set τ)) C (@Set.sInter τ 𝒮))
  (hne : @Set.Nonempty (Set τ) C)
  (hDir :
    ∀ (𝒮 : Set (Set τ)),
      @Set.Nonempty (Set τ) 𝒮 →
        @LE.le (Set (Set τ)) (@Set.instLE (Set τ)) 𝒮 C →
          @DirectedOn (Set τ) (fun (x1 x2 : Set τ) => @LE.le (Set τ) (@Set.instLE τ) x1 x2) 𝒮 →
            @Membership.mem (Set τ) (Set (Set τ)) (@Set.instMembership (Set τ)) C (@Set.sUnion τ 𝒮))
  (x :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
      (@DomainTheory.NeighbourhoodSystems.Exercise222.Tok τ C)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.reprSystem τ C hInter hne)),
  @Eq
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
      (@DomainTheory.NeighbourhoodSystems.Exercise222.Tok τ C)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.reprSystem τ C hInter hne))
    (@DomainTheory.NeighbourhoodSystems.Exercise222.ofC τ C hInter hne
      (@DomainTheory.NeighbourhoodSystems.Exercise222.toC τ C hInter hne x)
      (@DomainTheory.NeighbourhoodSystems.Exercise222.toC_mem τ C hInter hne hDir x))
    x :=
  @DomainTheory.NeighbourhoodSystems.Exercise222.ofC_toC

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- toC_ofC.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

/-- **Scott's identity** `X = ⋃ {F̄ ∣ F ⊆ X, F ∈ Δ}` in round-trip form: `toC (ofC X) = X`. -/
theorem toC_ofC (X : Set τ) (hX : X ∈ C) : toC C hInter hne (ofC C hInter hne X hX) = X := by
  apply Set.Subset.antisymm
  · intro t ht
    rw [mem_toC] at ht
    obtain ⟨F, hF, htCl⟩ := ht
    obtain ⟨_, F', hF'X, hF'F⟩ := hF
    have h1 : F.1 ⊆ Cl C F'.1 := (nbhd_subset_iff C hInter F'.2).mp hF'F
    have hFX : F.1 ⊆ X := h1.trans (Cl_subset C hX hF'X)
    exact Cl_subset C hX hFX htCl
  · intro t ht
    have hst : IsTok C {t} := ⟨⟨Set.finite_singleton t, X, hX, Set.singleton_subset_iff.mpr ht⟩⟩
    rw [mem_toC]
    refine ⟨⟨{t}, hst⟩, ?_, subset_Cl C {t} rfl⟩
    exact ⟨⟨⟨{t}, hst⟩, rfl⟩, ⟨{t}, hst⟩, Set.singleton_subset_iff.mpr ht, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end

section
-- reprIso.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise222

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem Set

variable {τ : Type*} (C : Set (Set τ))

variable (hInter : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → ⋂₀ 𝒮 ∈ C)

variable (hne : C.Nonempty)

variable (hDir : ∀ 𝒮 : Set (Set τ), 𝒮.Nonempty → 𝒮 ⊆ C → DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C)

include hDir in
/-- **Exercise 2.22 — the representation theorem.** `C`, ordered by inclusion, is order-isomorphic
to the domain `|reprSystem|`. The isomorphism sends `x ↦ ⋃ {F̄ ∣ C(F) ∈ x}` (`toC`) and
`X ↦ {C(F) ∣ F ⊆ X}` (`ofC`). -/
def reprIso : (reprSystem C hInter hne).Element ≃o {X : Set τ // X ∈ C} where
  toFun x := ⟨toC C hInter hne x, toC_mem C hInter hne hDir x⟩
  invFun X := ofC C hInter hne X.1 X.2
  left_inv x := ofC_toC C hInter hne hDir x
  right_inv X := Subtype.ext (toC_ofC C hInter hne X.1 X.2)
  map_rel_iff' := by
    intro a b
    show toC C hInter hne a ⊆ toC C hInter hne b ↔ a ≤ b
    constructor
    · intro hsub N hN
      have hmemD : (reprSystem C hInter hne).mem N := a.sub hN
      obtain ⟨G, rfl⟩ := hmemD
      have hGa : G.1 ⊆ toC C hInter hne a := (mem_nbhd_iff C hInter hne a G).mp hN
      exact (mem_nbhd_iff C hInter hne b G).mpr (hGa.trans hsub)
    · intro hab t ht
      rw [mem_toC] at ht ⊢
      obtain ⟨F, hF, htCl⟩ := ht
      exact ⟨F, hab _ hF, htCl⟩

end DomainTheory.NeighbourhoodSystems.Exercise222
end
