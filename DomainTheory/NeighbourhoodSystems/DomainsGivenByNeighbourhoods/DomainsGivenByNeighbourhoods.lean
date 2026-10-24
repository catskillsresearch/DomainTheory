module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Countable.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.Infix
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Zorn
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public import Mathlib.Topology.Inseparable

@[expose] public section

section
-- NeighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems

/- concordance: source L120 DEFINITION 1.1 neighbourhood system -/
/-- **Definition 1.1 (Scott 1981, PRG-19).** A *neighbourhood system* over a token type
`α`. `mem X` means "`X` is a neighbourhood" (`X ∈ 𝒟`), and `master` is Scott's least
informative neighbourhood `Δ` (the whole token set, "ask me no questions").

The two conditions are exactly Scott's:

* (i)  `Δ ∈ 𝒟`                                        — `master_mem`;
* (ii) whenever `X, Y, Z ∈ 𝒟` and `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟` — `inter_mem`.

We keep `master` as a field (rather than hard-wiring `Set.univ`) to stay faithful to
Scott's `Δ` notation, and record Scott's standing assumption `𝒟 ⊆ 𝒫(Δ)` as the field
`sub_master` (every neighbourhood is a subset of `Δ`). Scott also assumes from the outset
that the token set `Δ` is non-empty; `master_nonempty` records this standing assumption
explicitly. The subset condition is what makes the principal filter `↑X` (Definition 1.7)
contain `Δ`, and underlies the least element `⊥ = ↑Δ`. -/
structure NeighborhoodSystem (α : Type*) where
  /-- `mem X` holds iff `X` is a neighbourhood of the system (`X ∈ 𝒟`). -/
  mem : Set α → Prop
  /-- Scott's distinguished least-informative neighbourhood `Δ`. -/
  master : Set α
  /-- Scott's standing assumption that the token set `Δ` is non-empty. -/
  master_nonempty : master.Nonempty
  /-- (i) `Δ ∈ 𝒟`. -/
  master_mem : mem master
  /-- (ii) Closure under intersection of a *consistent* pair: if `X, Y, Z ∈ 𝒟` with the
  witness `Z ⊆ X ∩ Y`, then `X ∩ Y ∈ 𝒟`. -/
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  /-- Scott's `𝒟 ⊆ 𝒫(Δ)`: every neighbourhood is a subset of the master neighbourhood `Δ`. -/
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

end DomainTheory.NeighbourhoodSystems
end

section
-- Element.lean
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L240 DEFINITION 1.6 ideal elements -/
/-- **Definition 1.6 (Scott 1981, PRG-19).** An (ideal) *element* of a neighbourhood system:
a subfamily `x ⊆ 𝒟` that is a *filter* — (i) `Δ ∈ x`, (ii) closed under intersection, (iii)
upward closed within `𝒟`. The domain is the type `Element` of all such filters, ordered by
inclusion. -/
structure Element where
  /-- `mem X` holds iff the neighbourhood `X` belongs to the filter `x`. -/
  mem : Set α → Prop
  /-- `x` is a subfamily of `𝒟`. -/
  sub : ∀ {X}, mem X → V.mem X
  /-- (i) `Δ ∈ x`. -/
  master_mem : mem V.master
  /-- (ii) `X, Y ∈ x ⟹ X ∩ Y ∈ x`. -/
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  /-- (iii) `X ∈ x` and `X ⊆ Y ∈ 𝒟 ⟹ Y ∈ x`. -/
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- IsPositive.lean
namespace DomainTheory.NeighbourhoodSystems

/- concordance: source L468 EXERCISE 1.19 positive neighbourhood systems -/
/-- **Exercise 1.19 (Scott 1981, PRG-19) — positivity, condition (ii′).** A neighbourhood
system is *positive* when Scott's (ii) is strengthened to the biconditional **(ii′)**: for
`X, Y ∈ 𝒟`, the intersection `X ∩ Y` is a neighbourhood **iff** it is non-empty. -/
def NeighborhoodSystem.IsPositive {α : Type*} (V : NeighborhoodSystem α) : Prop :=
  ∀ ⦃X Y : Set α⦄, V.mem X → V.mem Y → (V.mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)

end DomainTheory.NeighbourhoodSystems
end

section
-- NestedOrDisjoint.lean
namespace DomainTheory.NeighbourhoodSystems

/-- Scott's *"very special circumstance"* (the prose after Examples 1.2–1.4): a family `𝒟`
is **nested-or-disjoint** when any two of its members are either nested (one included in the
other) or disjoint. -/
def NestedOrDisjoint {α : Type*} (mem : Set α → Prop) : Prop :=
  ∀ ⦃X Y : Set α⦄, mem X → mem Y → X ⊆ Y ∨ Y ⊆ X ∨ X ∩ Y = ∅

end DomainTheory.NeighbourhoodSystems
end

section
-- interUpTo.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection `⋂_{i < n} Xᵢ` of the first `n` terms of a sequence of
/- concordance: source L131 FACTOID 1.1a empty intersection is delta -/
neighbourhoods, defined by Scott's recursive convention (**Factoid 1.1a / 1.1b**):

* `n = 0` : the empty intersection is `Δ` (`master`);
* `n + 1` : `(⋂_{i < n} Xᵢ) ∩ Xₙ`.

(See `interUpTo_zero` and `interUpTo_succ` for the two defining equations as lemmas.) -/
def interUpTo (V : NeighborhoodSystem α) (X : ℕ → Set α) : ℕ → Set α
  | 0 => V.master
  | (n + 1) => interUpTo V X n ∩ X n

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- interUpTo_zero.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Factoid 1.1a.** The intersection of the empty sequence of neighbourhoods is `Δ`:
`⋂_{i < 0} Xᵢ = Δ`. -/
@[simp] theorem interUpTo_zero (X : ℕ → Set α) : V.interUpTo X 0 = V.master := rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- interUpTo_succ.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L135 FACTOID 1.1b recursive finite intersection -/
/-- **Factoid 1.1b.** The intersection of the first `n + 1` neighbourhoods peels off the
last factor: `⋂_{i < n+1} Xᵢ = (⋂_{i < n} Xᵢ) ∩ Xₙ`. -/
@[simp] theorem interUpTo_succ (X : ℕ → Set α) (n : ℕ) :
    V.interUpTo X (n + 1) = V.interUpTo X n ∩ X n := rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Consistent.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- A finite sequence `X₀, …, Xₙ₋₁` of neighbourhoods is *consistent in* `𝒟` when it has a
common lower bound inside `𝒟`: some `Z ∈ 𝒟` contained in the intersection `⋂_{i < n} Xᵢ`
(equivalently, contained in every `Xⱼ`, `j < n`). This is Scott's notion of consistency,
generalized from pairs to finite sequences. -/
def Consistent (X : ℕ → Set α) (n : ℕ) : Prop :=
  ∃ Z, V.mem Z ∧ Z ⊆ V.interUpTo X n

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- element_le.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Filter-inclusion order on elements (Scott's approximation order, Definition 1.8).
Named so Palomar can lock the `PartialOrder` relation without inlining it. -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- element_le_refl.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Reflexivity of the filter-inclusion order. Named so Palomar can lock the
`PartialOrder` instance without a generated `._proof_N`. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X :=
  fun _ h => h

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- element_le_trans.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X :=
  fun X h => hyz X (hxy X h)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- ext.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Two elements with the same membership predicate are equal (the remaining fields are `Prop`s). -/
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩
  rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X)
  subst hmem
  rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- element_le_antisymm.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y :=
  @Element.ext α V x y fun X => ⟨hxy X, hyx X⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- BasicInst22.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Elements are ordered by inclusion of their membership predicates (Scott's approximation
order, Definition 1.8). -/
instance : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- SeqEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Two sequences of neighbourhoods are **equivalent** ("each goes equally deep as the other"):
for every `Yₘ` some `Xₙ ⊆ Yₘ`, and for every `Xₙ` some `Yₘ ⊆ Xₙ`. -/
def SeqEquiv (X Y : ℕ → Set α) : Prop :=
  (∀ m, ∃ n, X n ⊆ Y m) ∧ (∀ n, ∃ m, Y m ⊆ X n)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- limitFamily.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The **limit family** of a sequence of neighbourhoods (Scott, the prose before Definition
1.6): `x = {Z ∈ 𝒟 ∣ Xₙ ⊆ Z for some n}` — the family of all neighbourhoods eventually reached
by `⟨Xₙ⟩`. This is the construction Scott uses to motivate the (ideal) elements of `|𝒟|`. -/
def limitFamily (X : ℕ → Set α) : Set (Set α) := {Z | V.mem Z ∧ ∃ n, X n ⊆ Z}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- ofNestedOrDisjoint.lean
namespace DomainTheory.NeighbourhoodSystems

/- concordance: source L206 FACTOID 1.4a nested or disjoint -/
/-- **Factoid 1.4a (Scott 1981, PRG-19).** "In these systems two neighbourhoods are either
disjoint or one is included in the other": a family containing `Δ` whose members are pairwise
nested-or-disjoint **is** a neighbourhood system. This uniformly explains why Examples 1.2,
1.3 and 1.4 satisfy Definition 1.1.

The verification of condition (ii) needs no choice: if `X, Y` are nested then `X ∩ Y` is the
smaller (already in `𝒟`); if they are disjoint then the consistency witness `Z ⊆ X ∩ Y = ∅`
forces `Z = ∅`, whence `X ∩ Y = ∅ = Z ∈ 𝒟`. The caller supplies `master_nonempty`
(Scott's standing `Δ ≠ ∅` assumption) and `sub_master` (`𝒟 ⊆ 𝒫(Δ)`) directly. -/
def NeighborhoodSystem.ofNestedOrDisjoint {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master) (hnd : NestedOrDisjoint mem)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master) : NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases hnd hX hY with h | h | h
    · rwa [Set.inter_eq_left.mpr h]
    · rwa [Set.inter_eq_right.mpr h]
    · rw [h]
      rw [h] at hZsub
      rwa [← Set.subset_empty_iff.mp hZsub]

end DomainTheory.NeighbourhoodSystems
end

section
-- ofPositive.lean
namespace DomainTheory.NeighbourhoodSystems

/-- **Exercise 1.19 — a positive system is a neighbourhood system.** Scott: "*prove that a
positive neighbourhood system is indeed a neighbourhood system*". From the raw data — (i)
`Δ ∈ 𝒟`, `𝒟 ⊆ 𝒫(Δ)`, and the positivity axiom (ii′) — condition (ii) follows: a consistency
witness `Z ⊆ X ∩ Y` with `Z ∈ 𝒟` is itself non-empty (apply (ii′) to `Z ∩ Z = Z`), so
`X ∩ Y ⊇ Z` is non-empty, whence `X ∩ Y ∈ 𝒟` by (ii′). Choice-free. -/
def NeighborhoodSystem.ofPositive {α : Type*} (mem : Set α → Prop) (master : Set α)
    (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    NeighborhoodSystem α where
  mem := mem
  master := master
  master_nonempty := master_nonempty
  master_mem := master_mem
  sub_master := sub_master
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hZZ : mem (Z ∩ Z) := by rwa [Set.inter_self]
    have hZne : (Z ∩ Z).Nonempty := (pos hZ hZ).mp hZZ
    rw [Set.inter_self] at hZne
    exact (pos hX hY).mpr (hZne.mono hZsub)

end DomainTheory.NeighbourhoodSystems
end

section
-- principal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L256 DEFINITION 1.7 principal filter -/
/-- **Definition 1.7 (Scott 1981, PRG-19).** The *principal filter* `↑X` determined by a
neighbourhood `X ∈ 𝒟`:

`↑X = {Y ∈ 𝒟 ∣ X ⊆ Y}`.

These are Scott's *finite elements* of `|𝒟|`. The four filter conditions:

* `sub` is the first projection (`Y ∈ ↑X ⟹ Y ∈ 𝒟`);
* `master_mem` needs `X ⊆ Δ`, supplied by `V.sub_master` (Scott's `𝒟 ⊆ 𝒫(Δ)`);
* `inter_mem` uses `Set.subset_inter` (from `X ⊆ Y₁`, `X ⊆ Y₂`) with `X` itself as the
  consistency witness for `V.inter_mem`;
* `up_mem` is transitivity of `⊆`. -/
def principal {X : Set α} (hX : V.mem X) : V.Element where
  mem Y := V.mem Y ∧ X ⊆ Y
  sub h := h.1
  master_mem := ⟨V.master_mem, V.sub_master hX⟩
  inter_mem h1 h2 :=
    ⟨V.inter_mem h1.1 h2.1 hX (Set.subset_inter h1.2 h2.2), Set.subset_inter h1.2 h2.2⟩
  up_mem h hY hsub := ⟨hY, h.2.trans hsub⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- mem_principal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_principal {X Y : Set α} (hX : V.mem X) :
    (V.principal hX).mem Y ↔ V.mem Y ∧ X ⊆ Y := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- bot.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L282 DEFINITION 1.8 approximation and totality -/
/-- **Definition 1.8 (Scott 1981, PRG-19) — `⊥`.** The least defined element `⊥ = {Δ}`,
"read: *bottom*". It is the principal filter of the master neighbourhood `Δ`: `⊥ = ↑Δ`. -/
def bot : V.Element := V.principal V.master_mem

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- mem_bot.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.8 — `⊥ = {Δ}` literally.** Scott's `⊥` is the *singleton* `{Δ}`: a
neighbourhood `Y` belongs to `⊥` iff `Y = Δ`.

`→`: `Y ∈ ⊥ = ↑Δ` gives `Y ∈ 𝒟` and `Δ ⊆ Y`; `V.sub_master` gives the reverse `Y ⊆ Δ`, so
`Y = Δ` by antisymmetry. `←`: `Δ ∈ 𝒟` and `Δ ⊆ Δ`. -/
@[simp] theorem mem_bot {Y : Set α} : V.bot.mem Y ↔ Y = V.master := by
  constructor
  · rintro ⟨hY, hΔY⟩
    exact Set.Subset.antisymm (V.sub_master hY) hΔY
  · rintro rfl
    exact ⟨V.master_mem, subset_rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- bot_le.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L282 FACTOID 1.8a2 bottom is least -/
/- concordance: source L282 FACTOID 1.8a1 bottom element -/
/-- **Factoid 1.8a (Scott 1981, PRG-19).** "The element that approximates all others, `{Δ}`,
is called `⊥`": `⊥` is the least element of `|𝒟|`, `⊥ ⊑ x` for every `x`.

Given `Y ∈ ⊥`, i.e. `Y = Δ`, membership `Δ ∈ x` is filter condition (i) (`x.master_mem`). -/
theorem bot_le (x : V.Element) : V.bot ≤ x := by
  intro Y hY
  rw [mem_bot] at hY
  subst hY
  exact x.master_mem

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- BasicInst34.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Factoid 1.8a, packaged.** `⊥` is an `OrderBot` for the approximation order, so the `⊥`
notation refers to `{Δ}`. Constructive (`bot_le` is `[propext, Quot.sound]`). -/
instance : OrderBot V.Element where
  bot := V.bot
  bot_le := V.bot_le

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- DomainIso.lean
namespace DomainTheory.NeighbourhoodSystems

/- concordance: source L326 DEFINITION 1.9 isomorphic domains -/
/-- **Definition 1.9 (Scott 1981, PRG-19).** Two neighbourhood systems `𝒟₀` and `𝒟₁` (over possibly
*different* token types) *determine isomorphic domains* iff there is a one-one, inclusion-preserving
correspondence between `|𝒟₀|` and `|𝒟₁|`. We package "one-one + preserves inclusion (both ways)" as
mathlib's order-isomorphism `≃o`: an `OrderIso` is automatically a bijection that *reflects* as well
as preserves `⊑` (`map_rel_iff`), which is exactly Scott's requirement. -/
abbrev DomainIso {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Type _ :=
  V₀.Element ≃o V₁.Element

end DomainTheory.NeighbourhoodSystems
end

section
-- IsTotal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.8 (Scott 1981, PRG-19) — *total* elements.** "Elements maximal with respect
to the approximation relation are called *total elements*." `x` is total iff it is maximal: any
`y` it approximates approximates it back. This is the *predicate* only; the *existence* of total
elements above a given `x` (Exercise 1.24) is choice-dependent and out of scope here. -/
def IsTotal (x : V.Element) : Prop := ∀ y, x ≤ y → y ≤ x

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems

/-- Scott's `𝒟₀ ≅ 𝒟₁`: the domains are isomorphic (there *exists* a `DomainIso`). -/
def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

end DomainTheory.NeighbourhoodSystems
end

section
-- Basic/notation40.lean
namespace DomainTheory.NeighbourhoodSystems

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

end DomainTheory.NeighbourhoodSystems
end

section
-- Basic.lean
namespace DomainTheory.NeighbourhoodSystems


/-- The system built by `ofPositive` is indeed positive. -/
theorem NeighborhoodSystem.ofPositive_isPositive {α : Type*} (mem : Set α → Prop)
    (master : Set α) (master_nonempty : master.Nonempty) (master_mem : mem master)
    (sub_master : ∀ {X : Set α}, mem X → X ⊆ master)
    (pos : ∀ ⦃X Y : Set α⦄, mem X → mem Y → (mem (X ∩ Y) ↔ (X ∩ Y).Nonempty)) :
    (NeighborhoodSystem.ofPositive mem master master_nonempty master_mem sub_master pos).IsPositive :=
  pos

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The finite intersection is contained in each of its factors: `⋂_{i < n} Xᵢ ⊆ Xⱼ` for
`j < n`. (Supporting lemma: this is what makes `⋂_{i < n} Xᵢ` a common lower bound of the
sequence, the intuition behind consistency.) -/
theorem interUpTo_subset (X : ℕ → Set α) :
    ∀ {n j : ℕ}, j < n → V.interUpTo X n ⊆ X j := by
  intro n
  induction n with
  | zero => intro j h; exact absurd h (Nat.not_lt_zero j)
  | succ n ih =>
    intro j h
    rw [interUpTo_succ]
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp h) with h' | h'
    · subst h'; exact Set.inter_subset_right
    · exact Set.inter_subset_left.trans (ih h')


/-- **Theorem 1.1c (extension of the intersection property).** Scott: "from (ii), we can
extend the intersection property to any finite sequence." If `Xᵢ ∈ 𝒟` for every `i < n`
and the sequence is consistent, then the finite intersection `⋂_{i < n} Xᵢ` is again a
neighbourhood (`∈ 𝒟`). Proved by induction on `n`; the inductive step is one application of
condition (ii). -/
theorem interUpTo_mem (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → V.mem (X i)) → V.Consistent X n →
      V.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _ _; exact V.master_mem
  | succ n ih =>
    intro hX hcons
    obtain ⟨Z, hZmem, hZsub⟩ := hcons
    have hZsub' : Z ⊆ V.interUpTo X n ∩ X n := by rwa [interUpTo_succ] at hZsub
    -- The same witness `Z` shows the length-`n` prefix is consistent.
    have hconsn : V.Consistent X n :=
      ⟨Z, hZmem, hZsub'.trans Set.inter_subset_left⟩
    have hmemn : V.mem (V.interUpTo X n) :=
      ih (fun i hi => hX i (Nat.lt_succ_of_lt hi)) hconsn
    have hXn : V.mem (X n) := hX n (Nat.lt_succ_self n)
    rw [interUpTo_succ]
    exact V.inter_mem hmemn hXn hZmem hZsub'

/-- **Theorem 1.1c (consistency characterization).** "Consequently, `X₀, …, Xₙ₋₁` is
consistent in `𝒟` iff `⋂_{i < n} Xᵢ ∈ 𝒟`." (Given `Xᵢ ∈ 𝒟` for all `i < n`.)

* `→` is the extension property `interUpTo_mem`;
* `←` is immediate: the intersection is its own common lower bound. -/
theorem consistent_iff_interUpTo_mem (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ V.mem (V.interUpTo X n) := by
  constructor
  · exact V.interUpTo_mem X hX
  · intro h; exact ⟨V.interUpTo X n, h, Set.Subset.refl _⟩


/-- A filter (`Element`) is closed under the finite intersection `⋂_{i<n} Xᵢ`: if every factor
`Xᵢ` (`i < n`) lies in the filter `x`, so does `interUpTo X n`. Used in Exercises 1.18 and 1.21.
Base case `x.master_mem`; inductive step one `x.inter_mem`. -/
theorem Element.mem_interUpTo {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) :
    ∀ {n : ℕ}, (∀ i, i < n → x.mem (X i)) → x.mem (V.interUpTo X n) := by
  intro n
  induction n with
  | zero => intro _; exact x.master_mem
  | succ n ih =>
    intro h
    rw [interUpTo_succ]
    exact x.inter_mem (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

/-- Membership of the finite intersection in a filter, as a biconditional (given all factors
are neighbourhoods). `→` is upward closure along `interUpTo X n ⊆ Xᵢ` (`interUpTo_subset`); `←`
is `Element.mem_interUpTo`. -/
theorem Element.mem_interUpTo_iff {α : Type*} {V : NeighborhoodSystem α} (x : V.Element)
    (X : ℕ → Set α) {n : ℕ} (hX : ∀ i, i < n → V.mem (X i)) :
    x.mem (V.interUpTo X n) ↔ ∀ i, i < n → x.mem (X i) := by
  constructor
  · intro h i hi
    exact x.up_mem h (hX i hi) (V.interUpTo_subset X hi)
  · exact x.mem_interUpTo X


/- concordance: source L238 FACTOID 1.5b equivalent sequences same limit -/
/-- **Factoid 1.5b (Scott 1981, PRG-19).** "It is easy to prove that … the two families are
*equal* if and only if the sequences are *equivalent*." Given that every term of each sequence
is a neighbourhood, the limit families coincide exactly when the sequences are equivalent. -/
theorem limitFamily_eq_iff (X Y : ℕ → Set α)
    (hX : ∀ n, V.mem (X n)) (hY : ∀ m, V.mem (Y m)) :
    V.limitFamily X = V.limitFamily Y ↔ SeqEquiv X Y := by
  constructor
  · intro hEq
    refine ⟨fun m => ?_, fun n => ?_⟩
    · have hmem : Y m ∈ V.limitFamily Y := ⟨hY m, m, subset_rfl⟩
      rw [← hEq] at hmem
      obtain ⟨_, n, hn⟩ := hmem
      exact ⟨n, hn⟩
    · have hmem : X n ∈ V.limitFamily X := ⟨hX n, n, subset_rfl⟩
      rw [hEq] at hmem
      obtain ⟨_, m, hm⟩ := hmem
      exact ⟨m, hm⟩
  · rintro ⟨h1, h2⟩
    apply Set.ext
    intro Z
    constructor
    · rintro ⟨hZ, n, hn⟩
      obtain ⟨m, hm⟩ := h2 n
      exact ⟨hZ, m, hm.trans hn⟩
    · rintro ⟨hZ, m, hm⟩
      obtain ⟨n, hn⟩ := h1 m
      exact ⟨hZ, n, hn.trans hm⟩


/- concordance: source L267 FACTOID 1.7a2 inclusion-reversing principals -/
/- concordance: source L264 FACTOID 1.7a1 principals are one-one -/
/-- **Factoid 1.7a (Scott 1981, PRG-19) — inclusion-*reversing*.** "It is obvious that the
correspondence between `X` and `↑X` is one-one and inclusion *reversing*." The order on `↑`:
`↑X ⊑ ↑Y ↔ Y ⊆ X` (equivalently Scott's `X ⊆ Y ↔ ↑Y ⊑ ↑X`).

`→` tests at `Z = X` (`X ∈ ↑X` since `X ⊆ X`), reading off `Y ⊆ X` from `X ∈ ↑Y`; `←` chains
`Y ⊆ X ⊆ Z`. -/
theorem principal_le_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.principal hX ≤ V.principal hY ↔ Y ⊆ X := by
  constructor
  · intro h
    exact (h X ⟨hX, subset_rfl⟩).2
  · intro hYX Z hZ
    exact ⟨hZ.1, hYX.trans hZ.2⟩

/-- **Factoid 1.7a (Scott 1981, PRG-19) — one-one.** The correspondence `X ↦ ↑X` is injective:
`↑X = ↑Y ⟹ X = Y`. Antisymmetry applied to `principal_le_iff` in both directions. -/
theorem principal_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.principal hX = V.principal hY) : X = Y := by
  have hYX : Y ⊆ X := (V.principal_le_iff hX hY).mp (le_of_eq h)
  have hXY : X ⊆ Y := (V.principal_le_iff hY hX).mp (le_of_eq h.symm)
  exact Set.Subset.antisymm hXY hYX

/- concordance: source L273 FACTOID 1.7b union of principal filters -/
/-- **Factoid 1.7b (Scott 1981, PRG-19).** "It is also obvious from the definitions that for each
`x ∈ |𝒟|`, `x = ⋃ {↑X ∣ X ∈ x}`." In membership form (the union over a `Set (Set α)` made
concrete): a neighbourhood `Z` is in `x` iff `Z` lies in the principal filter `↑X` of *some*
member `X` of `x`.

`→` uses `X = Z` (`Z ∈ ↑Z` as `Z ⊆ Z`); `←` is upward closure `up_mem` (`X ⊆ Z`, `Z ∈ 𝒟`). -/
theorem eq_iUnion_principal (x : V.Element) {Z : Set α} :
    x.mem Z ↔ ∃ X, ∃ hX : x.mem X, (V.principal (x.sub hX)).mem Z := by
  constructor
  · intro hZ
    exact ⟨Z, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨X, hX, hVZ, hXZ⟩
    exact x.up_mem hX hVZ hXZ


/- concordance: source L284 FACTOID 1.8b finite filters are principal -/
/- concordance: source L284 EXAMPLES 1.2–1.5 finite examples revisited -/
/-- **Factoid 1.8b (Scott 1981, PRG-19) — "Examples 1.2–1.5 revisited".** "Any explicitly given
filter `x` is principal … the minimal `X ∈ x` tells us all we need to know." Stated honestly: if
the filter `x` has a `⊆`-minimum member `X` (one contained in every member of `x`), then `x` is
exactly the principal filter `↑X`. In a *finite* system every filter has such a minimum (the
intersection of its finitely many members, itself in `x` by closure), so every element is
principal; that finiteness step is the only classical ingredient and is left implicit here — this
constructive core captures the content.

`⊆`: any `Z ∈ x` satisfies `X ⊆ Z` by minimality, so `Z ∈ ↑X`. `⊇`: `Z ∈ ↑X` means `Z ∈ 𝒟` and
`X ⊆ Z`, so `Z ∈ x` by upward closure from `X ∈ x`. -/
theorem eq_principal_of_isMin (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZmem, hXZ⟩
    exact x.up_mem hX hZmem hXZ

end NeighborhoodSystem


/-- `≅ᴰ` is reflexive (`OrderIso.refl`). -/
theorem Isomorphic.refl {α : Type*} (V : NeighborhoodSystem α) : V ≅ᴰ V :=
  ⟨OrderIso.refl _⟩

/-- `≅ᴰ` is symmetric (`OrderIso.symm`). -/
theorem Isomorphic.symm {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (h : V₀ ≅ᴰ V₁) : V₁ ≅ᴰ V₀ :=
  h.elim fun e => ⟨e.symm⟩

/-- `≅ᴰ` is transitive (`OrderIso.trans`). -/
theorem Isomorphic.trans {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} (h₀ : V₀ ≅ᴰ V₁) (h₁ : V₁ ≅ᴰ V₂) : V₀ ≅ᴰ V₂ :=
  h₀.elim fun e₀ => h₁.elim fun e₁ => ⟨e₀.trans e₁⟩

end DomainTheory.NeighbourhoodSystems
end

section
-- Example12/Token.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- Tokens for Example 1.2: `Δ = {0, 1}`. -/
abbrev Token := Fin 2

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/master.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- The master neighbourhood `Δ = {0, 1}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/inter_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/master_inter.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/one.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- The neighbourhood `{1}`. -/
def one : Set Token := {1}

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/master_not_subset_one.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem master_not_subset_one : ¬master ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [master])
  simp [one] at this

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/zero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- The neighbourhood `{0}`. -/
def zero : Set Token := {0}

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/master_not_subset_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem master_not_subset_zero : ¬master ⊆ zero := by
  intro h
  have : (1 : Token) ∈ zero := h (by simp [master])
  simp [zero] at this

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/memSet.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- The three neighbourhoods of Example 1.2. -/
def memSet : Set (Set Token) := {master, zero, one}

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- Membership in the neighbourhood system `𝒟` of Example 1.2. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/mem_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem mem_master : mem master := by simp [mem, memSet, master, zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/mem_one.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem mem_one : mem one := by simp [mem, memSet, master, zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/mem_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem mem_zero : mem zero := by simp [mem, memSet, master, zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/mem_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/-- A neighbourhood of Example 1.2 is exactly one of `Δ`, `{0}`, or `{1}`. -/
theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = zero ∨ X = one := by
  constructor
  · intro h
    simp [mem, memSet, master, zero, one] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_zero
    · exact mem_one

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/eq_of_master_subset.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp h with rfl | hzero | hone
  · rfl
  · exact absurd hzero (fun h' => master_not_subset_zero (h' ▸ hsub))
  · exact absurd hone (fun h' => master_not_subset_one (h' ▸ hsub))

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/not_mem_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h
  · rw [master] at h; exact Set.empty_ne_univ h
  · simp [zero] at h
  · simp [one] at h

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/one_inter_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem one_inter_zero : one ∩ zero = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/one_not_subset_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem one_not_subset_zero : ¬one ⊆ zero := by
  intro h
  have : (1 : Token) ∈ zero := h (by simp [one])
  simp [zero] at this

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/zero_inter_one.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem zero_inter_one : zero ∩ one = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/inter_eq.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem inter_eq (X Y : Set Token) (h : mem X) (h' : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = zero ∨ X ∩ Y = one ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp h with rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp h' with rfl | rfl | rfl
  · exact Or.inl (master_inter _)
  · exact Or.inr (Or.inl (master_inter _))
  · exact Or.inr (Or.inr (Or.inl (master_inter _)))
  · exact Or.inr (Or.inl (inter_master _))
  · exact Or.inr (Or.inl (Set.inter_self _))
  · exact Or.inr (Or.inr (Or.inr zero_inter_one))
  · exact Or.inr (Or.inr (Or.inl (inter_master _)))
  · exact Or.inr (Or.inr (Or.inr one_inter_zero))
  · exact Or.inr (Or.inr (Or.inl (Set.inter_self _)))

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/neighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

/- concordance: source L146 EXAMPLE 1.2 two-token domain -/
/-- **Example 1.2.** The neighbourhood system on `Δ = {0, 1}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_zero
    · rw [h]; exact mem_one
    · rw [h] at hZsub
      have hz : Z = (∅ : Set Token) := Set.subset_empty_iff.mp hZsub
      subst hz
      exact absurd hZ not_mem_empty

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/bot.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The bottom element `⊥ = {Δ}`. -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    intro X Y hX hY
    rw [hX, hY, master_inter]
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/elemOne.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element determined by `{1}`. -/
def elemOne : neighborhoodSystem.Element where
  mem X := X = master ∨ X = one
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_one
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd hXY one_not_subset_zero
      · exact Or.inr rfl

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/zero_not_subset_one.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

theorem zero_not_subset_one : ¬zero ⊆ one := by
  intro h
  have : (0 : Token) ∈ one := h (by simp [zero])
  simp [one] at this

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/elemZero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element determined by `{0}`. -/
def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = zero
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_zero
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hXY zero_not_subset_one

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


theorem zero_ne_master : zero ≠ master := by
  intro h
  have : (1 : Token) ∈ zero := h ▸ (by simp [master])
  simp [zero] at this

theorem one_ne_master : one ≠ master := by
  intro h
  have : (0 : Token) ∈ one := h ▸ (by simp [master])
  simp [one] at this


namespace neighborhoodSystem

open NeighborhoodSystem


theorem mem_zero_of_mem (x : neighborhoodSystem.Element) (h : x.mem zero) :
    x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · exact Or.inr hzero
    · have hxone : x.mem one := hone ▸ hx
      have := x.inter_mem h hxone
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

theorem mem_one_of_mem (x : neighborhoodSystem.Element) (h : x.mem one) :
    x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · exact Or.inl rfl
    · have hxzero : x.mem zero := hzero ▸ hx
      have := x.inter_mem hxzero h
      rw [zero_inter_one] at this
      exact absurd (x.sub this) not_mem_empty
    · exact Or.inr hone
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact h

theorem zero_ne_one : zero ≠ (one : Set Token) := by
  intro h
  have h0 : (0 : Token) ∈ zero := by simp [zero]
  rw [h] at h0
  simp [one] at h0
end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/bot_lt_elemOne.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem one := h one (Or.inr rfl)
    have hm : one = master := this
    exact one_ne_master hm

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/bot_lt_elemZero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


/-- The bottom filter is the only partial element: it is strictly below both total elements. -/
theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; exact Or.inl hx
  · intro h
    have : bot.mem zero := h zero (Or.inr rfl)
    have hm : zero = master := this
    exact zero_ne_master hm

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/element_classification.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


/-- Every element of Example 1.2 is one of the three filters `⊥`, `{0}`-total, `{1}`-total. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne := by
  by_cases h0 : x.mem zero
  · exact Or.inr (Or.inl (mem_zero_of_mem x h0))
  by_cases h1 : x.mem one
  · exact Or.inr (Or.inr (mem_one_of_mem x h1))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hzero | hone
    · rfl
    · exact absurd (hzero ▸ hx) h0
    · exact absurd (hone ▸ hx) h1
  · intro hx
    rw [hx]
    exact x.master_mem

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/bot_is_unique_partial.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_is_unique_partial (x : neighborhoodSystem.Element) :
    x ≠ elemZero → x ≠ elemOne → x = bot := by
  intro hne0 hne1
  rcases element_classification x with hx | hx | hx
  · exact hx
  · exact (hne0 hx).elim
  · exact (hne1 hx).elim

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/not_elemOne_le_elemZero.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


theorem not_elemOne_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h one (Or.inr rfl) with h' | h'
  · exact one_ne_master h'
  · exact zero_ne_one h'.symm

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/not_elemZero_le_elemOne.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


/-- **`elemZero` and `elemOne` are incomparable.** Neither total element approximates the other:
if it did, its finite neighbourhood `{i}` would have to belong to the other's filter too, which
is neither `Δ` nor its own singleton `{1-i}`. Used to show `⊥` is the *only* common lower bound
of `elemZero` and `elemOne` (Exercise 2.16's uniqueness argument for the parity map). -/
theorem not_elemZero_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h zero (Or.inr rfl) with h' | h'
  · exact zero_ne_master h'
  · exact zero_ne_one h'

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example12/eq_bot_of_le_elemZero_of_le_elemOne.lean
namespace DomainTheory.NeighbourhoodSystems.Example12


namespace neighborhoodSystem

open NeighborhoodSystem


/-- **`⊥` is the unique common lower bound of `elemZero` and `elemOne`.** Any element approximated
by *both* total elements is exactly `⊥`: `element_classification` puts it at `bot`, `elemZero`, or
`elemOne`, and the latter two are excluded by incomparability. This is the order-theoretic
ingredient (continuity/flatness of `𝒯`) behind the uniqueness half of Exercise 2.16. -/
theorem eq_bot_of_le_elemZero_of_le_elemOne {a : neighborhoodSystem.Element}
    (h0 : a ≤ elemZero) (h1 : a ≤ elemOne) : a = bot := by
  rcases element_classification a with rfl | rfl | rfl
  · rfl
  · exact absurd h1 not_elemZero_le_elemOne
  · exact absurd h0 not_elemOne_le_elemZero

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example12
end

section
-- Example13/Token.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- Tokens for Example 1.3: `Δ = {0, 1, 2}`. -/
abbrev Token := Fin 3

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/master.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The master neighbourhood `Δ = {0, 1, 2}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/inter_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/master_inter.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/twelve.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The neighbourhood `{1, 2}`. -/
def twelve : Set Token := (insert 2 {1} : Set Token)

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/master_not_subset_twelve.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem master_not_subset_twelve : ¬master ⊆ twelve := by
  intro h
  have : (0 : Token) ∈ twelve := h (by simp [master])
  simp [twelve] at this

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/two.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The neighbourhood `{2}`. -/
def two : Set Token := {2}

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/master_not_subset_two.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem master_not_subset_two : ¬master ⊆ two := by
  intro h
  have : (0 : Token) ∈ two := h (by simp [master])
  simp [two] at this

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/memSet.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- The three neighbourhoods of Example 1.3. -/
def memSet : Set (Set Token) := {master, twelve, two}

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- Membership in the neighbourhood system `𝒟` of Example 1.3. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/mem_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem mem_master : mem master := by simp [mem, memSet, master, twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/mem_twelve.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem mem_twelve : mem twelve := by simp [mem, memSet, master, twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/mem_two.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem mem_two : mem two := by simp [mem, memSet, master, twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/mem_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/-- A neighbourhood of Example 1.3 is exactly one of `Δ`, `{1,2}`, or `{2}`. -/
theorem mem_iff (X : Set Token) : mem X ↔ X = master ∨ X = twelve ∨ X = two := by
  constructor
  · intro h
    simp [mem, memSet, master, twelve, two] at h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · intro h
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/eq_of_master_subset.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem eq_of_master_subset {Y : Set Token} (h : mem Y) (hsub : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp h with rfl | htwelve | htwo
  · rfl
  · exact absurd htwelve (fun h' => master_not_subset_twelve (h' ▸ hsub))
  · exact absurd htwo (fun h' => master_not_subset_two (h' ▸ hsub))

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/twelve_inter_two.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem twelve_inter_two : twelve ∩ two = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/twelve_not_subset_two.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem twelve_not_subset_two : ¬twelve ⊆ two := by
  intro h
  have : (1 : Token) ∈ two := h (by simp [twelve])
  simp [two] at this

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/two_inter_twelve.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem two_inter_twelve : two ∩ twelve = two := by
  ext t
  fin_cases t <;> simp [twelve, two]

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/inter_eq.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

theorem inter_eq (X Y : Set Token) (h : mem X) (h' : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = twelve ∨ X ∩ Y = two := by
  rcases (mem_iff X).mp h with rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp h' with rfl | rfl | rfl
  · exact Or.inl (master_inter _)
  · exact Or.inr (Or.inl (master_inter _))
  · exact Or.inr (Or.inr (master_inter _))
  · exact Or.inr (Or.inl (inter_master _))
  · exact Or.inr (Or.inl (Set.inter_self _))
  · exact Or.inr (Or.inr (twelve_inter_two))
  · exact Or.inr (Or.inr (inter_master _))
  · exact Or.inr (Or.inr (two_inter_twelve))
  · exact Or.inr (Or.inr (Set.inter_self _))

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/neighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

/- concordance: source L160 EXAMPLE 1.3 three-step chain -/
/-- **Example 1.3.** The neighbourhood system on `Δ = {0, 1, 2}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_twelve
    · rw [h]; exact mem_two

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/bot.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The bottom element `⊥ = {Δ}`. -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    intro X Y hX hY
    rw [hX, hY, master_inter]
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/elemTwelve.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The intermediate partial element `{Δ, {1,2}}`. -/
def elemTwelve : neighborhoodSystem.Element where
  mem X := X = master ∨ X = twelve
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_twelve
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hXY twelve_not_subset_two

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/elemTwo.lean
namespace DomainTheory.NeighbourhoodSystems.Example13

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, {1,2}, {2}}`. -/
def elemTwo : neighborhoodSystem.Element where
  mem X := X = master ∨ X = twelve ∨ X = two
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_twelve
    · exact mem_two
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr (twelve_inter_two))
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr (two_inter_twelve))
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Example13


theorem twelve_ne_master : twelve ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ twelve := by
    rw [h]
    simp [master]
  simp [twelve] at hmem

theorem two_ne_master : two ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ two := by
    rw [h]
    simp [master]
  simp [two] at hmem

theorem two_ne_twelve : two ≠ twelve := by
  intro h
  have hmem : (1 : Token) ∈ two := by
    rw [h]
    simp [twelve]
  simp [two] at hmem


namespace neighborhoodSystem

open NeighborhoodSystem


theorem two_subset_twelve : two ⊆ twelve := by
  intro t ht
  fin_cases t <;> simp [two, twelve] at ht ⊢

theorem mem_two_of_mem (x : neighborhoodSystem.Element) (h : x.mem two) :
    x = elemTwo := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hX12 | htwo
    · exact Or.inl rfl
    · rw [hX12]; exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr htwo)
  · intro hx
    rcases hx with rfl | hx | hx
    · exact x.master_mem
    · rw [hx]; exact x.up_mem h mem_twelve two_subset_twelve
    · rw [hx]; exact h

theorem mem_twelve_of_mem (x : neighborhoodSystem.Element) (htwelve : x.mem twelve)
    (htwo : ¬x.mem two) : x = elemTwelve := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | hX12 | hX2
    · exact Or.inl rfl
    · exact Or.inr hX12
    · have hxo : x.mem two := hX2 ▸ hx
      have := x.inter_mem htwelve hxo
      rw [twelve_inter_two] at this
      exact absurd this htwo
  · intro hx
    rcases hx with rfl | hx
    · exact x.master_mem
    · rw [hx]; exact htwelve
end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/bot_lt_elemTwelve.lean
namespace DomainTheory.NeighbourhoodSystems.Example13


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_lt_elemTwelve : bot < elemTwelve := by
  constructor
  · intro X hx
    rw [hx]
    exact Or.inl rfl
  · intro h
    have : bot.mem twelve := h twelve (Or.inr rfl)
    exact twelve_ne_master this

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/elemTwelve_lt_elemTwo.lean
namespace DomainTheory.NeighbourhoodSystems.Example13


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemTwelve_lt_elemTwo : elemTwelve < elemTwo := by
  constructor
  · intro X hx
    rcases hx with rfl | hX12
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hX12)
  · intro h
    exfalso
    have ht := h two (Or.inr (Or.inr rfl))
    rcases ht with h1 | h2
    · exact absurd h1 two_ne_master
    · exact two_ne_twelve h2

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/element_classification.lean
namespace DomainTheory.NeighbourhoodSystems.Example13


namespace neighborhoodSystem

open NeighborhoodSystem


/-- Every element of Example 1.3 is one of the three filters in the linear chain. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemTwelve ∨ x = elemTwo := by
  by_cases htwo : x.mem two
  · exact Or.inr (Or.inr (mem_two_of_mem x htwo))
  by_cases htwelve : x.mem twelve
  · exact Or.inr (Or.inl (mem_twelve_of_mem x htwelve htwo))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | htwelve' | htwo'
    · rfl
    · exact absurd (htwelve' ▸ hx) htwelve
    · exact absurd (htwo' ▸ hx) htwo
  · intro hx
    rw [hx]
    exact x.master_mem

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example13/elemTwo_maximal.lean
namespace DomainTheory.NeighbourhoodSystems.Example13


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemTwo_maximal (x : neighborhoodSystem.Element) (h : elemTwo ≤ x) : x = elemTwo := by
  rcases element_classification x with rfl | rfl | rfl
  · exfalso
    have : bot.mem twelve := h twelve (Or.inr (Or.inl rfl))
    exact twelve_ne_master this
  · exfalso
    have ht := h two (Or.inr (Or.inr rfl))
    rcases ht with h1 | h2
    · exact absurd h1 two_ne_master
    · exact two_ne_twelve h2
  · rfl

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example13
end

section
-- Example14/Token.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Tokens for Example 1.4: the binary tree `Δ = {Λ,0,1,00,01,10,11}`, encoded as `Fin 7`
(`Λ=0, 0=1, 1=2, 00=3, 01=4, 10=5, 11=6`). -/
abbrev Token := Fin 7

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The leaf `{00} = {3}`. -/
def leaf00 : Set Token := {3}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The leaf `{01} = {4}`. -/
def leaf01 : Set Token := {4}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00_inter_leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_leaf01 : leaf00 ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01_inter_leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_leaf00 : leaf01 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf01

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The leaf `{10} = {5}`. -/
def leaf10 : Set Token := {5}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00_inter_leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_leaf10 : leaf00 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf10]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01_inter_leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_leaf10 : leaf01 ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf10]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10_inter_leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_leaf00 : leaf10 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10_inter_leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_leaf01 : leaf10 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The leaf `{11} = {6}`. -/
def leaf11 : Set Token := {6}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00_inter_leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_leaf11 : leaf00 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf00, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01_inter_leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_leaf11 : leaf01 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf01, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10_inter_leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_leaf11 : leaf10 ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11_inter_leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_inter_leaf00 : leaf11 ∩ leaf00 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf00_inter_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11_inter_leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_inter_leaf01 : leaf11 ∩ leaf01 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf01_inter_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11_inter_leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_inter_leaf10 : leaf11 ∩ leaf10 = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact leaf10_inter_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The left subtree `{0, 00, 01} = {1, 3, 4}`. -/
def left : Set Token := {1, 3, 4}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left_inter_leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf00 : left ∩ leaf00 = leaf00 := by
  ext t; fin_cases t <;> simp [left, leaf00]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00_inter_left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_left : leaf00 ∩ left = leaf00 := by
  rw [Set.inter_comm]; exact left_inter_leaf00

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left_inter_leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf01 : left ∩ leaf01 = leaf01 := by
  ext t; fin_cases t <;> simp [left, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01_inter_left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_left : leaf01 ∩ left = leaf01 := by
  rw [Set.inter_comm]; exact left_inter_leaf01

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left_inter_leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf10 : left ∩ leaf10 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf10]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10_inter_left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_left : leaf10 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left_inter_leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_leaf11 : left ∩ leaf11 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11_inter_left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_inter_left : leaf11 ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/master.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The master neighbourhood `Δ` (the whole tree). -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/inter_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem inter_master (A : Set Token) : A ∩ master = A := by
  rw [master]; exact Set.inter_univ A

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/master_inter.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem master_inter (A : Set Token) : master ∩ A = A := by
  rw [master]; exact Set.univ_inter A

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The right subtree `{1, 10, 11} = {2, 5, 6}`. -/
def right : Set Token := {2, 5, 6}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left_inter_right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_inter_right : left ∩ right = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [left, right]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/memSet.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- The seven neighbourhoods of Example 1.4. -/
def memSet : Set (Set Token) := {master, left, right, leaf00, leaf01, leaf10, leaf11}

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Membership in the neighbourhood system `𝒟` of Example 1.4. -/
def mem (X : Set Token) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_leaf00 : mem leaf00 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_leaf01 : mem leaf01 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_leaf10 : mem leaf10 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_leaf11 : mem leaf11 := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_left : mem left := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_master : mem master := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem mem_right : mem right := by
  simp [mem, memSet, master, left, right, leaf00, leaf01, leaf10, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/mem_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- A neighbourhood of Example 1.4 is exactly one of the seven. -/
theorem mem_iff (X : Set Token) :
    mem X ↔ X = master ∨ X = left ∨ X = right ∨ X = leaf00 ∨ X = leaf01 ∨ X = leaf10 ∨ X = leaf11 := by
  constructor
  · intro h
    simpa [mem, memSet] using h
  · intro h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_right
    · exact mem_leaf00
    · exact mem_leaf01
    · exact mem_leaf10
    · exact mem_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/eq_of_master_subset.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem eq_of_master_subset {Y : Set Token} (hY : mem Y) (h : master ⊆ Y) : Y = master := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [left])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [right])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf00])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf01])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf10])
  · exact absurd (h (show (0 : Token) ∈ master by simp [master])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00_subset_cases.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf00 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf00 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [right])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [leaf01])
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [leaf10])
  · exact absurd (h (show (3 : Token) ∈ leaf00 by simp [leaf00])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01_subset_cases.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf01 ⊆ Y) :
    Y = master ∨ Y = left ∨ Y = leaf01 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [right])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf00])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf10])
  · exact absurd (h (show (4 : Token) ∈ leaf01 by simp [leaf01])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10_subset_cases.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf10 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf10 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [left])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf00])
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf01])
  · exact Or.inr (Or.inr rfl)
  · exact absurd (h (show (5 : Token) ∈ leaf10 by simp [leaf10])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11_subset_cases.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_subset_cases {Y : Set Token} (hY : mem Y) (h : leaf11 ⊆ Y) :
    Y = master ∨ Y = right ∨ Y = leaf11 := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [left])
  · exact Or.inr (Or.inl rfl)
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [leaf00])
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [leaf01])
  · exact absurd (h (show (6 : Token) ∈ leaf11 by simp [leaf11])) (by simp [leaf10])
  · exact Or.inr (Or.inr rfl)

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/left_subset_cases.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem left_subset_cases {Y : Set Token} (hY : mem Y) (h : left ⊆ Y) :
    Y = master ∨ Y = left := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [right])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf00])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf01])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf10])
  · exact absurd (h (show (1 : Token) ∈ left by simp [left])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/not_mem_empty.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem not_mem_empty : ¬mem (∅ : Set Token) := by
  intro h
  rcases (mem_iff (∅ : Set Token)).mp h with h | h | h | h | h | h | h
  · have : (0 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [master]
    simp at this
  · have : (1 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [left]
    simp at this
  · have : (2 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [right]
    simp at this
  · have : (3 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf00]
    simp at this
  · have : (4 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf01]
    simp at this
  · have : (5 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf10]
    simp at this
  · have : (6 : Token) ∈ (∅ : Set Token) := by rw [h]; simp [leaf11]
    simp at this

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right_inter_leaf00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf00 : right ∩ leaf00 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf00]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf00_inter_right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf00_inter_right : leaf00 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf00

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right_inter_leaf01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf01 : right ∩ leaf01 = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [right, leaf01]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf01_inter_right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf01_inter_right : leaf01 ∩ right = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact right_inter_leaf01

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right_inter_leaf10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf10 : right ∩ leaf10 = leaf10 := by
  ext t; fin_cases t <;> simp [right, leaf10]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf10_inter_right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf10_inter_right : leaf10 ∩ right = leaf10 := by
  rw [Set.inter_comm]; exact right_inter_leaf10

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right_inter_leaf11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_leaf11 : right ∩ leaf11 = leaf11 := by
  ext t; fin_cases t <;> simp [right, leaf11]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/leaf11_inter_right.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem leaf11_inter_right : leaf11 ∩ right = leaf11 := by
  rw [Set.inter_comm]; exact right_inter_leaf11

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right_inter_left.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_inter_left : right ∩ left = (∅ : Set Token) := by
  rw [Set.inter_comm]; exact left_inter_right

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/inter_eq.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/-- Every binary intersection of two neighbourhoods is again a neighbourhood, or is empty
(the tree's "nested-or-disjoint" property). -/
theorem inter_eq (X Y : Set Token) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = left ∨ X ∩ Y = right ∨ X ∩ Y = leaf00 ∨
      X ∩ Y = leaf01 ∨ X ∩ Y = leaf10 ∨ X ∩ Y = leaf11 ∨ X ∩ Y = (∅ : Set Token) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [master_inter, inter_master, Set.inter_self,
      left_inter_right, right_inter_left, left_inter_leaf10, leaf10_inter_left,
      left_inter_leaf11, leaf11_inter_left, right_inter_leaf00, leaf00_inter_right,
      right_inter_leaf01, leaf01_inter_right, leaf00_inter_leaf01, leaf01_inter_leaf00,
      leaf00_inter_leaf10, leaf10_inter_leaf00, leaf00_inter_leaf11, leaf11_inter_leaf00,
      leaf01_inter_leaf10, leaf10_inter_leaf01, leaf01_inter_leaf11, leaf11_inter_leaf01,
      leaf10_inter_leaf11, leaf11_inter_leaf10,
      left_inter_leaf00, leaf00_inter_left, left_inter_leaf01, leaf01_inter_left,
      right_inter_leaf10, leaf10_inter_right, right_inter_leaf11, leaf11_inter_right,
      true_or, or_true]

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/neighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

/- concordance: source L177 EXAMPLE 1.4 finite binary tree -/
/-- **Example 1.4.** The binary-tree neighbourhood system on `Δ = {Λ,0,1,00,01,10,11}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h | h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_left
    · rw [h]; exact mem_right
    · rw [h]; exact mem_leaf00
    · rw [h]; exact mem_leaf01
    · rw [h]; exact mem_leaf10
    · rw [h]; exact mem_leaf11
    · rw [h] at hZsub
      have hz : Z = (∅ : Set Token) := Set.subset_empty_iff.mp hZsub
      subst hz
      exact absurd hZ not_mem_empty

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/bot.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The bottom element `⊥ = {Δ}` (node `Λ`). -/
def bot : neighborhoodSystem.Element where
  mem X := X = master
  sub h := by rw [h]; exact mem_master
  master_mem := rfl
  inter_mem := by
    intro X Y hX hY
    rw [hX, hY, master_inter]
  up_mem := by
    intro X Y hX hY hXY
    rw [hX] at hXY
    exact eq_of_master_subset hY hXY

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, left, leaf00}` (leaf `00`). -/
def elem00 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf00
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf00
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf00)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf00_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf00_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, left, leaf01}` (leaf `01`). -/
def elem01 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left ∨ X = leaf01
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_left
    · exact mem_leaf01
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr left_inter_leaf01)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf01_inter_left)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf01_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elemZero.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The partial element `{Δ, left}` (node `0`): the left branch is decided. -/
def elemZero : neighborhoodSystem.Element where
  mem X := X = master ∨ X = left
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_left
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases left_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr h

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/right_subset_cases.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

theorem right_subset_cases {Y : Set Token} (hY : mem Y) (h : right ⊆ Y) :
    Y = master ∨ Y = right := by
  rcases (mem_iff Y).mp hY with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [left])
  · exact Or.inr rfl
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf00])
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf01])
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf10])
  · exact absurd (h (show (2 : Token) ∈ right by simp [right])) (by simp [leaf11])

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, right, leaf10}` (leaf `10`). -/
def elem10 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf10
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf10
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf10)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf10_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf10_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The total element `{Δ, right, leaf11}` (leaf `11`). -/
def elem11 : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right ∨ X = leaf11
  sub h := by
    rcases h with rfl | rfl | rfl
    · exact mem_master
    · exact mem_right
    · exact mem_leaf11
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (Or.inl (master_inter _))
    · exact Or.inr (Or.inr (master_inter _))
    · exact Or.inr (Or.inl (inter_master _))
    · exact Or.inr (Or.inl (Set.inter_self _))
    · exact Or.inr (Or.inr right_inter_leaf11)
    · exact Or.inr (Or.inr (inter_master _))
    · exact Or.inr (Or.inr leaf11_inter_right)
    · exact Or.inr (Or.inr (Set.inter_self _))
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases leaf11_subset_cases hY hXY with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elemOne.lean
namespace DomainTheory.NeighbourhoodSystems.Example14

namespace neighborhoodSystem

open NeighborhoodSystem

/-- The partial element `{Δ, right}` (node `1`): the right branch is decided. -/
def elemOne : neighborhoodSystem.Element where
  mem X := X = master ∨ X = right
  sub h := by
    rcases h with rfl | rfl
    · exact mem_master
    · exact mem_right
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact Or.inl (master_inter _)
    · exact Or.inr (master_inter _)
    · exact Or.inr (inter_master _)
    · exact Or.inr (Set.inter_self _)
  up_mem := by
    intro X Y hX hY hXY
    rcases hX with rfl | rfl
    · exact Or.inl (eq_of_master_subset hY hXY)
    · rcases right_subset_cases hY hXY with h | h
      · exact Or.inl h
      · exact Or.inr h

end neighborhoodSystem

end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


theorem left_ne_master : left ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ left := by rw [h]; simp [master]
  simp [left] at hmem

theorem right_ne_master : right ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ right := by rw [h]; simp [master]
  simp [right] at hmem

theorem leaf00_ne_master : leaf00 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf00 := by rw [h]; simp [master]
  simp [leaf00] at hmem

theorem leaf01_ne_master : leaf01 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf01 := by rw [h]; simp [master]
  simp [leaf01] at hmem

theorem leaf10_ne_master : leaf10 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf10 := by rw [h]; simp [master]
  simp [leaf10] at hmem

theorem leaf11_ne_master : leaf11 ≠ master := by
  intro h
  have hmem : (0 : Token) ∈ leaf11 := by rw [h]; simp [master]
  simp [leaf11] at hmem

theorem leaf00_ne_left : leaf00 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf00 := by rw [h]; simp [left]
  simp [leaf00] at hmem

theorem leaf01_ne_left : leaf01 ≠ left := by
  intro h
  have hmem : (1 : Token) ∈ leaf01 := by rw [h]; simp [left]
  simp [leaf01] at hmem

theorem leaf10_ne_right : leaf10 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf10 := by rw [h]; simp [right]
  simp [leaf10] at hmem

theorem leaf11_ne_right : leaf11 ≠ right := by
  intro h
  have hmem : (2 : Token) ∈ leaf11 := by rw [h]; simp [right]
  simp [leaf11] at hmem

theorem leaf00_subset_left : leaf00 ⊆ left := by
  intro t ht; fin_cases t <;> simp [leaf00, left] at ht ⊢

private theorem leaf01_subset_left : leaf01 ⊆ left := by
  intro t ht; fin_cases t <;> simp [leaf01, left] at ht ⊢

private theorem leaf10_subset_right : leaf10 ⊆ right := by
  intro t ht; fin_cases t <;> simp [leaf10, right] at ht ⊢

private theorem leaf11_subset_right : leaf11 ⊆ right := by
  intro t ht; fin_cases t <;> simp [leaf11, right] at ht ⊢


namespace neighborhoodSystem

open NeighborhoodSystem


theorem mem_leaf00_imp (x : neighborhoodSystem.Element) (h : x.mem leaf00) :
    x = elem00 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf00_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (right ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf01, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf10, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf11, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h

theorem mem_leaf01_imp (x : neighborhoodSystem.Element) (h : x.mem leaf01) :
    x = elem01 := by
  have hleft : x.mem left := x.up_mem h mem_left leaf01_subset_left
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (right ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf00, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf10, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf11, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hleft
    · exact h

theorem mem_leaf10_imp (x : neighborhoodSystem.Element) (h : x.mem leaf10) :
    x = elem10 := by
  have hright : x.mem right := x.up_mem h mem_right leaf10_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (left ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf00, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf01, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf11 ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf11, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h

theorem mem_leaf11_imp (x : neighborhoodSystem.Element) (h : x.mem leaf11) :
    x = elem11 := by
  have hright : x.mem right := x.up_mem h mem_right leaf11_subset_right
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (left ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf00 ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf00, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf01 ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf01, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hx h
      rw [show (leaf10 ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [leaf10, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr (Or.inr rfl)
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact x.master_mem
    · exact hright
    · exact h

theorem mem_left_imp (x : neighborhoodSystem.Element) (hl : x.mem left)
    (h00 : ¬x.mem leaf00) (h01 : ¬x.mem leaf01) : x = elemZero := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ right : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, right]] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h00
    · exact absurd hx h01
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ leaf10 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf10]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hl hx
      rw [show (left ∩ leaf11 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [left, leaf11]] at hi
      exact not_mem_empty (x.sub hi)
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hl

theorem mem_right_imp (x : neighborhoodSystem.Element) (hr : x.mem right)
    (h10 : ¬x.mem leaf10) (h11 : ¬x.mem leaf11) : x = elemOne := by
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ left : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, left]] at hi
      exact not_mem_empty (x.sub hi)
    · exact Or.inr rfl
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ leaf00 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf00]] at hi
      exact not_mem_empty (x.sub hi)
    · exfalso
      have hi := x.inter_mem hr hx
      rw [show (right ∩ leaf01 : Set Token) = ∅ from by ext t; fin_cases t <;> simp [right, leaf01]] at hi
      exact not_mem_empty (x.sub hi)
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rcases hx with rfl | rfl
    · exact x.master_mem
    · exact hr

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/bot_lt_elemOne.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_lt_elemOne : bot < elemOne := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact right_ne_master (h right (Or.inr rfl))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/bot_lt_elemZero.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem bot_lt_elemZero : bot < elemZero := by
  constructor
  · intro X hx; rw [hx]; exact Or.inl rfl
  · intro h
    exact left_ne_master (h left (Or.inr rfl))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem00_maximal.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem00_maximal (x : neighborhoodSystem.Element) (h : elem00 ≤ x) : x = elem00 :=
  mem_leaf00_imp x (h leaf00 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem01_maximal.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem01_maximal (x : neighborhoodSystem.Element) (h : elem01 ≤ x) : x = elem01 :=
  mem_leaf01_imp x (h leaf01 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem10_maximal.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem10_maximal (x : neighborhoodSystem.Element) (h : elem10 ≤ x) : x = elem10 :=
  mem_leaf10_imp x (h leaf10 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elem11_maximal.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elem11_maximal (x : neighborhoodSystem.Element) (h : elem11 ≤ x) : x = elem11 :=
  mem_leaf11_imp x (h leaf11 (Or.inr (Or.inr rfl)))

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elemOne_lt_elem10.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemOne_lt_elem10 : elemOne < elem10 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf10 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf10_ne_master h1
    · exact leaf10_ne_right h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elemOne_lt_elem11.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemOne_lt_elem11 : elemOne < elem11 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf11 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf11_ne_master h1
    · exact leaf11_ne_right h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elemZero_lt_elem00.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemZero_lt_elem00 : elemZero < elem00 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf00 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf00_ne_master h1
    · exact leaf00_ne_left h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/elemZero_lt_elem01.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


theorem elemZero_lt_elem01 : elemZero < elem01 := by
  constructor
  · intro X hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · intro h
    rcases h leaf01 (Or.inr (Or.inr rfl)) with h1 | h1
    · exact leaf01_ne_master h1
    · exact leaf01_ne_left h1

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example14/element_classification.lean
namespace DomainTheory.NeighbourhoodSystems.Example14


namespace neighborhoodSystem

open NeighborhoodSystem


/-- **Example 1.4 classification.** Every filter is one of the seven: the bottom `⊥`, the two
branch partials `elemZero`/`elemOne`, or one of the four total leaf elements. -/
theorem element_classification (x : neighborhoodSystem.Element) :
    x = bot ∨ x = elemZero ∨ x = elemOne ∨ x = elem00 ∨ x = elem01 ∨ x = elem10 ∨ x = elem11 := by
  by_cases h00 : x.mem leaf00
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf00_imp x h00))))
  by_cases h01 : x.mem leaf01
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf01_imp x h01)))))
  by_cases h10 : x.mem leaf10
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (mem_leaf10_imp x h10))))))
  by_cases h11 : x.mem leaf11
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (mem_leaf11_imp x h11))))))
  by_cases hl : x.mem left
  · exact Or.inr (Or.inl (mem_left_imp x hl h00 h01))
  by_cases hr : x.mem right
  · exact Or.inr (Or.inr (Or.inl (mem_right_imp x hr h10 h11)))
  apply Or.inl
  apply Element.ext
  intro X
  constructor
  · intro hx
    rcases (mem_iff X).mp (x.sub hx) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hx hl
    · exact absurd hx hr
    · exact absurd hx h00
    · exact absurd hx h01
    · exact absurd hx h10
    · exact absurd hx h11
  · intro hx
    rw [hx]
    exact x.master_mem

end neighborhoodSystem
end DomainTheory.NeighbourhoodSystems.Example14
end

section
-- Example15/Token.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Tokens for Example 1.5: `Δ = {0, 1, 2, 3}`. -/
abbrev Token := Fin 4

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/P4Mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Membership: the non-empty subsets of `Δ`. -/
def P4Mem (X : Set Token) : Prop := X.Nonempty

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/P4_inter_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- A non-empty witness inside `X ∩ Y` shows the intersection is a neighbourhood. -/
theorem P4_inter_mem {X Y Z : Set Token} (_hX : P4Mem X) (_hY : P4Mem Y)
    (hZ : P4Mem Z) (hZsub : Z ⊆ X ∩ Y) : P4Mem (X ∩ Y) :=
  hZ.mono hZsub

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/master.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- The master neighbourhood `Δ = {0, 1, 2, 3}`. -/
def master : Set Token := Set.univ

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/P4_master_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- `Δ` is non-empty. -/
theorem P4_master_mem : P4Mem master := by
  rw [master]; exact Set.univ_nonempty

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/P4_master_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- The master token set itself is non-empty. -/
theorem P4_master_nonempty : master.Nonempty := by
  exact ⟨0, Set.mem_univ 0⟩

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/P4_sub_master.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/-- Every neighbourhood is a subset of `Δ`. -/
theorem P4_sub_master {X : Set Token} (_h : P4Mem X) : X ⊆ master :=
  Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/neighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem

/- concordance: source L208 EXAMPLE 1.5 all nonempty subsets -/
/-- **Example 1.5.** The neighbourhood system of all non-empty subsets of `Δ = {0,1,2,3}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := P4Mem
  master := master
  master_nonempty := P4_master_nonempty
  master_mem := P4_master_mem
  inter_mem := P4_inter_mem
  sub_master := P4_sub_master

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem


/-- The neighbourhoods of Example 1.5 are a finite family, hence countable. -/
instance P4_countable : Countable {S : Set Token // neighborhoodSystem.mem S} :=
  inferInstance
end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/consistent_iff_inter_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem


/- concordance: source L210 FACTOID 1.5a consistent iff nonempty -/
/-- **Factoid 1.5a (Scott 1981, PRG-19).** In Example 1.5, "sets are consistent in `𝒟` iff they
have a non-empty intersection": a finite prefix `X₀, …, Xₙ₋₁` is consistent exactly when its
intersection `⋂_{i<n} Xᵢ` is non-empty. -/
theorem consistent_iff_inter_nonempty (X : ℕ → Set Token) (n : ℕ) :
    neighborhoodSystem.Consistent X n ↔ (neighborhoodSystem.interUpTo X n).Nonempty := by
  constructor
  · rintro ⟨Z, hZ, hsub⟩
    obtain ⟨z, hz⟩ := hZ
    exact ⟨z, hsub hz⟩
  · intro h
    exact ⟨_, h, subset_rfl⟩

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- Example15/mem_iff_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems.Example15

open NeighborhoodSystem


/-- The neighbourhoods of Example 1.5 are exactly the non-empty subsets. -/
theorem mem_iff_nonempty (X : Set Token) : neighborhoodSystem.mem X ↔ X.Nonempty := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Example15
end

section
-- ExampleB/Str.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The token type `Σ* = List Bool` (finite binary strings); `Λ = []`. -/
abbrev Str := List Bool

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/cone.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The neighbourhood `σΣ*`: all *extensions* of `σ` (sequences with `σ` as an initial segment). -/
def cone (σ : Str) : Set Str := {w | σ <+: w}

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/mem_cone.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_cone {σ w : Str} : w ∈ cone σ ↔ σ <+: w := Iff.rfl

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/cone_nil.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `ΛΣ* = Σ*`: the cone of the empty string is everything (Scott's `Δ`). -/
theorem cone_nil : cone [] = Set.univ := by
  ext w; simp [cone]

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/cone_subset_cone.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Cones reverse the prefix order.** `σΣ* ⊆ τΣ*` iff `τ` is an initial segment of `σ`: a longer
prefix carves out a *smaller* cone. (`→` tests at `σ ∈ σΣ*`; `←` is transitivity of `<+:`.) -/
theorem cone_subset_cone {σ τ : Str} : cone σ ⊆ cone τ ↔ τ <+: σ := by
  constructor
  · intro h
    exact h (show σ ∈ cone σ from List.prefix_rfl)
  · intro hτσ w hw
    exact hτσ.trans hw

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/cone_trichotomy.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Prefix trichotomy for cones.** Any two cones are nested-or-disjoint: either one contains the
other, or they are disjoint (incomparable prefixes have no common extension). Choice-free: the
prefix relation on `List Bool` is decidable. -/
theorem cone_trichotomy (σ τ : Str) :
    cone σ ⊆ cone τ ∨ cone τ ⊆ cone σ ∨ cone σ ∩ cone τ = ∅ :=
  if hστ : σ <+: τ then Or.inr (Or.inl (cone_subset_cone.mpr hστ))
  else if hτσ : τ <+: σ then Or.inl (cone_subset_cone.mpr hτσ)
  else Or.inr (Or.inr (by
    ext w
    simp only [Set.mem_inter_iff, mem_cone, Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hστ h
    · exact hτσ h))

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/memB.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership in Scott's binary neighbourhood system `B`: `X ∈ B` iff `X = σΣ*` for some `σ`. -/
def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/nestedOrDisjoint.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise ("`B` is a neighbourhood system").** The family `B = {σΣ* ∣ σ ∈ Σ*}` is pairwise
nested-or-disjoint, by `cone_trichotomy`. -/
theorem nestedOrDisjoint : NestedOrDisjoint memB := by
  rintro X Y ⟨σ, rfl⟩ ⟨τ, rfl⟩
  exact cone_trichotomy σ τ

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/B.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Example 1.B (Scott 1981, PRG-19).** The binary neighbourhood system `B` on `Δ = Σ*`. -/
def B : NeighborhoodSystem Str :=
  NeighborhoodSystem.ofNestedOrDisjoint memB Set.univ
    ⟨[], Set.mem_univ _⟩ ⟨[], cone_nil.symm⟩ nestedOrDisjoint
    (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/B_mem.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem B_mem {X : Set Str} : B.mem X ↔ memB X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/B_master.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem B_master : B.master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/memB_cone.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Every cone is a neighbourhood of `B`. -/
theorem memB_cone (σ : Str) : B.mem (cone σ) := ⟨σ, rfl⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/prepend.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Scott's `σX = {στ ∣ τ ∈ X}` (prepend the prefix `σ` to every member of `X`). -/
def prepend (σ : Str) (X : Set Str) : Set Str := {w | ∃ τ, τ ∈ X ∧ w = σ ++ τ}

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/mem_prepend.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_prepend {σ : Str} {X : Set Str} {w : Str} :
    w ∈ prepend σ X ↔ ∃ τ, τ ∈ X ∧ w = σ ++ τ := Iff.rfl

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/prepend_cone.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **`σ(τΣ*) = (στ)Σ*`.** Prepending `σ` to a cone yields the cone of the concatenation — this is
why `σx` lands back in `B` and why `σ⊥` is again a finite element. -/
theorem prepend_cone (σ ρ : Str) : prepend σ (cone ρ) = cone (σ ++ ρ) := by
  ext w
  simp only [mem_prepend, mem_cone]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact (List.prefix_append_right_inj σ).mpr hτ
  · rintro ⟨t, ht⟩
    exact ⟨ρ ++ t, List.prefix_append ρ t, by rw [← ht, List.append_assoc]⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/memB_prepend.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Prepending preserves membership in `B` (`σ` applied to a cone is a cone). -/
theorem memB_prepend (σ : Str) {X : Set Str} (hX : B.mem X) : B.mem (prepend σ X) := by
  obtain ⟨ρ, rfl⟩ := hX
  exact ⟨σ ++ ρ, prepend_cone σ ρ⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/prepend_nil.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem prepend_nil (X : Set Str) : prepend [] X = X := by
  ext w; simp [mem_prepend]

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/sigmaBot.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **`σ⊥`, a finite element of `|B|`.** The principal filter `↑(σΣ*)` of the cone of `σ`; its
minimal neighbourhood is `σΔ = σΣ*` (Scott). These are exactly the finite elements of `|B|`. -/
def sigmaBot (σ : Str) : B.Element := B.principal (memB_cone σ)

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/sigmaElt.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise (`σx ∈ |B|`).** For `x ∈ |B|` and `σ ∈ Σ*`, Scott's
`σx = {Y ∣ σX ⊆ Y for some X ∈ x}` is again an element of `|B|`.

The filter laws: `master` uses `X = Δ ∈ x` (`σΔ ⊆ Δ` trivially); `inter` takes `X₁ ∩ X₂ ∈ x` and
the consistency witness `σ(X₁∩X₂)`, which is a *cone* (hence in `B`, by `memB_prepend`) contained in
both `Y₁` and `Y₂`; `up` reuses the same `X`. -/
def sigmaElt (σ : Str) (x : B.Element) : B.Element where
  mem Y := B.mem Y ∧ ∃ X, x.mem X ∧ prepend σ X ⊆ Y
  sub h := h.1
  master_mem := ⟨B.master_mem, B.master, x.master_mem, Set.subset_univ _⟩
  inter_mem := by
    intro Y₁ Y₂ h1 h2
    obtain ⟨hY₁, X₁, hX₁, hsub₁⟩ := h1
    obtain ⟨hY₂, X₂, hX₂, hsub₂⟩ := h2
    have hXinter : x.mem (X₁ ∩ X₂) := x.inter_mem hX₁ hX₂
    have hsub : prepend σ (X₁ ∩ X₂) ⊆ Y₁ ∩ Y₂ := by
      rintro w ⟨τ, ⟨hτ₁, hτ₂⟩, rfl⟩
      exact ⟨hsub₁ ⟨τ, hτ₁, rfl⟩, hsub₂ ⟨τ, hτ₂, rfl⟩⟩
    have hZmem : B.mem (prepend σ (X₁ ∩ X₂)) := memB_prepend σ (x.sub hXinter)
    exact ⟨B.inter_mem hY₁ hY₂ hZmem hsub, X₁ ∩ X₂, hXinter, hsub⟩
  up_mem := by
    intro X Y hX hY hXY
    obtain ⟨_, X', hX', hsub'⟩ := hX
    exact ⟨hY, X', hX', hsub'.trans hXY⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/cone_injective.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Cones are one-one in the prefix.** `cone σ = cone τ ⟹ σ = τ`: from the two inclusions we get
`τ <+: σ` and `σ <+: τ`, and a prefix-antisymmetry (equal lengths) finishes. Used by the approximable
maps `B → T` / `B → B` (Examples 2.3, 2.4) to read off the unique generating prefix of a cone. -/
theorem cone_injective {σ τ : Str} (h : cone σ = cone τ) : σ = τ := by
  have h1 : τ <+: σ := cone_subset_cone.mp (le_of_eq h)
  have h2 : σ <+: τ := cone_subset_cone.mp (le_of_eq h.symm)
  exact h2.eq_of_length (h2.length_le.antisymm h1.length_le)

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/bot_mem_cone_iff.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **`⊥` sits only in the cone of the empty prefix.** `⊥.mem(σΣ*) ↔ σ = Λ`: `⊥`'s only
neighbourhood is `Δ = ΛΣ*` (`cone_nil`), and a cone determines its prefix (`cone_injective`).
(Used by Exercise 2.17's base case, where `g(1)=⊥` is stated only at the input `⊥`.) -/
theorem bot_mem_cone_iff {σ : Str} : B.bot.mem (cone σ) ↔ σ = [] := by
  rw [mem_bot, B_master, ← cone_nil]
  constructor
  · exact cone_injective
  · intro h; rw [h]

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/mem_iff_exists_sigmaBot.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/- concordance: source L317 FACTOID 1.8d union of finite approximations -/
/-- **Factoid (Scott 1981, PRG-19).** "`x = ⋃ₙ σₙ⊥`": every `x ∈ |B|` is the union of the finite
elements `σ⊥` whose generating cone `σΣ*` lies in `x`. In membership form, a neighbourhood `Z`
belongs to `x` iff `Z` lies in some `σ⊥ = ↑(σΣ*)` with `σΣ* ∈ x`.

This is the concrete "an element is uniquely determined by its finite approximations" in `|B|`
(`Basic.eq_iUnion_principal` specialized to `B`, where every neighbourhood is a cone). The further
arrangement of the `σ` into a single increasing chain `σ₀ ⪯ σ₁ ⪯ …` requires choice/enumeration and
is left to Scott's prose. -/
theorem mem_iff_exists_sigmaBot (x : B.Element) {Z : Set Str} :
    x.mem Z ↔ ∃ σ, x.mem (cone σ) ∧ (sigmaBot σ).mem Z := by
  constructor
  · intro hZ
    obtain ⟨σ, rfl⟩ := x.sub hZ
    exact ⟨σ, hZ, x.sub hZ, subset_rfl⟩
  · rintro ⟨σ, hcone, hZmem, hsub⟩
    exact x.up_mem hcone hZmem hsub

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/prepend_append.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Prepending is associative.** `σ(τX) = (στ)X`: prepending `σ` after `τ` is the same as
prepending the concatenation `σ ++ τ` in one step (used to compose `sigmaElt`, `Exercise216`). -/
theorem prepend_append (σ τ : Str) (X : Set Str) :
    prepend σ (prepend τ X) = prepend (σ ++ τ) X := by
  ext w
  simp only [mem_prepend]
  constructor
  · rintro ⟨ρ, ⟨ρ', hρ', rfl⟩, rfl⟩
    exact ⟨ρ', hρ', by rw [List.append_assoc]⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨τ ++ ρ, ⟨ρ, hρ, rfl⟩, by rw [List.append_assoc]⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/prepend_mono.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Prepending is monotone.** `X' ⊆ X → σX' ⊆ σX` (Exercise 2.16's `sigmaMap` uses this for
its `mono` clause; `sigmaElt_append` uses it to transport the up-closure through composition). -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/prepend_univ.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `σΣ* = σ·Σ*`: prepending `σ` to the whole space recovers the cone of `σ`. -/
theorem prepend_univ (σ : Str) : prepend σ Set.univ = cone σ := by
  ext w
  simp only [mem_prepend, Set.mem_univ, true_and, mem_cone]
  constructor
  · rintro ⟨τ, rfl⟩
    exact List.prefix_append σ τ
  · rintro ⟨t, ht⟩
    exact ⟨t, ht.symm⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/sigmaBot_le_iff.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/- concordance: source L312 FACTOID 1.8c prefix order -/
/-- **Factoid (Scott 1981, PRG-19).** "`σ₀⊥ ⊆ σ₁⊥` if and only if `σ₀` is an *initial segment* of
the sequence `σ₁`." The approximation order on finite elements is exactly the prefix order:
`σ₀⊥ ⊑ σ₁⊥ ↔ σ₀ <+: σ₁`. (Via `principal_le_iff` — reversal — composed with `cone_subset_cone` —
reversal again — which cancel to give the prefix order directly.) -/
theorem sigmaBot_le_iff (σ₀ σ₁ : Str) :
    sigmaBot σ₀ ≤ sigmaBot σ₁ ↔ σ₀ <+: σ₁ := by
  rw [sigmaBot, sigmaBot, B.principal_le_iff, cone_subset_cone]

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/sigmaElt_append.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **`σ` and `τ` prepend in sequence, like concatenation.** `(στ)x = σ(τx)`: applying the
prefix `σ ++ τ` in one step agrees with applying `τ` first and then `σ`. (Used in Exercise 2.16's
second half — the uniqueness of the parity map — to unfold `f(σ₁σ₂ … σₙx)` one token at a time.) -/
theorem sigmaElt_append (σ τ : Str) (x : B.Element) :
    sigmaElt (σ ++ τ) x = sigmaElt σ (sigmaElt τ x) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    refine ⟨hY, prepend τ X, ⟨memB_prepend τ (x.sub hX), X, hX, subset_rfl⟩, ?_⟩
    rw [prepend_append]; exact hsub
  · rintro ⟨hY, X, ⟨_, X', hX', hsub'⟩, hsub⟩
    refine ⟨hY, X', hX', ?_⟩
    rw [← prepend_append]
    exact (prepend_mono σ hsub').trans hsub

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/sigmaElt_bot.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **`σ⊥` really is `σ` applied to `⊥`.** `sigmaElt σ ⊥ = sigmaBot σ`, justifying the `σ⊥`
notation: applying `σ` to the least element produces the finite element `↑(σΣ*)`. -/
theorem sigmaElt_bot (σ : Str) : sigmaElt σ B.bot = sigmaBot σ := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [B.mem_bot] at hX
    subst hX
    rw [B_master, prepend_univ] at hsub
    exact ⟨hY, hsub⟩
  · rintro ⟨hY, hcone⟩
    refine ⟨hY, B.master, B.mem_bot.mpr rfl, ?_⟩
    rw [B_master, prepend_univ]
    exact hcone

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
-- ExampleB/sigmaElt_nil.lean
namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Prepending the empty prefix fixes every element.** `Λx = x` — the identity case of
`sigmaElt`, matching `prepend_nil` on neighbourhoods. -/
theorem sigmaElt_nil (x : B.Element) : sigmaElt [] x = x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    rw [prepend_nil] at hsub
    exact x.up_mem hX hY hsub
  · intro hY
    exact ⟨x.sub hY, Y, hY, by rw [prepend_nil]⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
end

section
/- concordance: source L444 EXERCISES — Lecture I exercises -/
-- Exercise112/tail.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The final segment (tail) `tail n = {m ∣ n ≤ m}`; the neighbourhood "all integers `≥ n`". -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/mem_tail.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem mem_tail {n m : ℕ} : m ∈ tail n ↔ n ≤ m := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership in the final-segment system: `X` is a neighbourhood iff `X = tail n` for some `n`. -/
def mem (X : Set ℕ) : Prop := ∃ n, X = tail n

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/tail_inter.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `tail n ∩ tail m = tail (max n m)` (the intersection of two tails is the shorter one). -/
theorem tail_inter (n m : ℕ) : tail n ∩ tail m = tail (max n m) := by
  ext k
  simp only [Set.mem_inter_iff, mem_tail]
  omega

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/tail_subset_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- A longer tail is a *smaller* set: `tail n ⊆ tail m ↔ m ≤ n`. -/
theorem tail_subset_iff {n m : ℕ} : tail n ⊆ tail m ↔ m ≤ n := by
  constructor
  · intro h
    exact h (show n ∈ tail n from le_refl n)
  · intro hmn k hk
    exact le_trans hmn hk

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/nestedOrDisjoint.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem nestedOrDisjoint : NestedOrDisjoint mem := by
  rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases le_total n m with h | h
  · exact Or.inr (Or.inl (tail_subset_iff.mpr h))
  · exact Or.inl (tail_subset_iff.mpr h)

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/neighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/- concordance: source L446 EXERCISE 1.12 final segments of integers -/
/-- **Exercise 1.12.** The final-segment neighbourhood system on `ℕ` (master `Δ = tail 0 = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint mem (tail 0) ⟨0, Nat.zero_le 0⟩ ⟨0, rfl⟩ nestedOrDisjoint
    (fun {X} hX => by obtain ⟨n, rfl⟩ := hX; exact tail_subset_iff.mpr (Nat.zero_le n))

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/ns_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ ∃ n, X = tail n := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/mem_tail_nbhd.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem mem_tail_nbhd (n : ℕ) : neighborhoodSystem.mem (tail n) := ⟨n, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/fin.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The finite element `fin n = ↑(tail n)` (principal filter of the tail). -/
def fin (n : ℕ) : neighborhoodSystem.Element := neighborhoodSystem.principal (mem_tail_nbhd n)

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/top.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The **limit element** `top`: the filter of *all* tails (Scott's single limit node). -/
def top : neighborhoodSystem.Element where
  mem X := neighborhoodSystem.mem X
  sub h := h
  master_mem := neighborhoodSystem.master_mem
  inter_mem := by
    rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨max n m, tail_inter n m⟩
  up_mem _ hY _ := hY

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


@[simp] theorem mem_top {X : Set ℕ} : top.mem X ↔ neighborhoodSystem.mem X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/element_eq.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Exercise 1.12 (classification).** Every element is either a finite element `fin n` or the
single limit element `top`. *Classical*: it decides whether the indices present in `x` are bounded.
(Hint realized: "there is only one limit element.") -/
theorem element_eq (x : neighborhoodSystem.Element) :
    (∃ n, x = fin n) ∨ x = top := by
  classical
  by_cases h : ∀ n, x.mem (tail n)
  · refine Or.inr ?_
    apply Element.ext
    intro X
    constructor
    · intro hx; exact x.sub hx
    · rintro ⟨n, rfl⟩; exact h n
  · refine Or.inl ?_
    have h' : ∃ n, ¬ x.mem (tail n) := not_forall.mp h
    have hpos : ∀ n, ¬ x.mem (tail n) → 0 < n := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · exact absurd x.master_mem hn
      · exact hp
    have hspec : ¬ x.mem (tail (Nat.find h')) := Nat.find_spec h'
    have hmin : ∀ j, j < Nat.find h' → x.mem (tail j) := by
      intro j hj
      by_contra hc
      exact Nat.find_min h' hj hc
    have hn₀ : 0 < Nat.find h' := hpos _ hspec
    refine ⟨Nat.find h' - 1, ?_⟩
    apply Element.ext
    intro X
    have key : ∀ j, x.mem (tail j) ↔ j ≤ Nat.find h' - 1 := by
      intro j
      constructor
      · intro hj
        by_contra hc
        have hle : Nat.find h' ≤ j := by omega
        exact hspec (x.up_mem hj (mem_tail_nbhd (Nat.find h')) (tail_subset_iff.mpr hle))
      · intro hj
        exact hmin j (by omega)
    constructor
    · intro hx
      obtain ⟨j, rfl⟩ := x.sub hx
      exact ⟨mem_tail_nbhd j, tail_subset_iff.mpr ((key j).mp hx)⟩
    · rintro ⟨hX, hsub⟩
      obtain ⟨j, rfl⟩ := hX
      exact (key j).mpr (tail_subset_iff.mp hsub)

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

set_option linter.unusedVariables false

theorem example_112 : ∀
  (x :
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
      DomainTheory.NeighbourhoodSystems.Exercise112.neighborhoodSystem),
  Or
    (∃ (n : Nat),
      @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
          DomainTheory.NeighbourhoodSystems.Exercise112.neighborhoodSystem)
        x (DomainTheory.NeighbourhoodSystems.Exercise112.fin n))
    (@Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Nat
        DomainTheory.NeighbourhoodSystems.Exercise112.neighborhoodSystem)
      x DomainTheory.NeighbourhoodSystems.Exercise112.top) :=
  DomainTheory.NeighbourhoodSystems.Exercise112.element_eq

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/fin_le_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- The finite elements form an ascending chain: `fin n ⊑ fin m ↔ n ≤ m`. -/
theorem fin_le_iff (n m : ℕ) : fin n ≤ fin m ↔ n ≤ m := by
  rw [fin, fin, neighborhoodSystem.principal_le_iff, tail_subset_iff]

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/fin_strictMono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- The chain `fin 0 ⊏ fin 1 ⊏ ⋯` is strictly increasing. -/
theorem fin_strictMono : StrictMono fin := by
  intro n m hnm
  refine lt_of_le_of_ne ((fin_le_iff n m).mpr hnm.le) ?_
  intro heq
  have : m ≤ n := (fin_le_iff m n).mp (le_of_eq heq.symm)
  exact absurd (le_antisymm hnm.le this) (Nat.ne_of_lt hnm)

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/le_top.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `top` is the greatest element of `|𝒟|`: every element approximates it. -/
theorem le_top (x : neighborhoodSystem.Element) : x ≤ top :=
  fun _ hX => x.sub hX

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/top_isTotal.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `top` is a total (maximal) element. -/
theorem top_isTotal : neighborhoodSystem.IsTotal top :=
  fun y _ => le_top y

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise112/isTotal_iff_top.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise112

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `top` is the **unique** total element: an element is total iff it equals `top`. -/
theorem isTotal_iff_top (x : neighborhoodSystem.Element) :
    neighborhoodSystem.IsTotal x ↔ x = top := by
  constructor
  · intro h
    exact le_antisymm (le_top x) (h top (le_top x))
  · rintro rfl; exact top_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise112
end

section
-- Exercise114/mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership: `X` is a neighbourhood iff `X = ℕ` (the master `Δ`) or `X` is finite and non-empty. -/
def mem (X : Set ℕ) : Prop := X = Set.univ ∨ (X.Finite ∧ X.Nonempty)

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/nonempty_of_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem nonempty_of_mem {X : Set ℕ} (h : mem X) : X.Nonempty := by
  rcases h with rfl | h
  · exact Set.univ_nonempty
  · exact h.2

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/neighborhoodSystem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/- concordance: source L456 EXERCISE 1.14 finite nonempty subsets -/
/-- **Exercise 1.14.** The neighbourhood system of finite non-empty subsets of `ℕ` (plus `Δ = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ where
  mem := mem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hne : (X ∩ Y).Nonempty := (nonempty_of_mem hZ).mono hZsub
    rcases hX with hX | hX
    · rw [hX, Set.univ_inter]; exact hY
    · rcases hY with hY | hY
      · rw [hY, Set.inter_univ]; exact Or.inr hX
      · exact Or.inr ⟨hX.1.inter_of_left Y, hne⟩
  sub_master := fun _ => Set.subset_univ _

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/ns_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ mem X := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/bot.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `⊥ = ↑Δ = ↑ℕ`, the least element. -/
def bot : neighborhoodSystem.Element := neighborhoodSystem.bot

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/fin.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The finite element `↑X` for a neighbourhood `X` (Scott's finite elements). -/
def fin {X : Set ℕ} (h : neighborhoodSystem.mem X) : neighborhoodSystem.Element :=
  neighborhoodSystem.principal h

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/empty_not_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem empty_not_mem : ¬ mem (∅ : Set ℕ) := by
  rintro (h | ⟨_, h⟩)
  · exact Set.empty_ne_univ h
  · exact Set.not_nonempty_empty h

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/mem_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem mem_singleton (n : ℕ) : mem {n} :=
  Or.inr ⟨Set.finite_singleton n, Set.singleton_nonempty n⟩

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114/singleton_isTotal.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Exercise 1.14 (total elements).** The principal filter of a *singleton* `{n}` is a total
(maximal) element: any `y` it approximates approximates it back. (A `y ⊋ ↑{n}` would contain some
`W ∌ n`; then `{n} ∩ W = ∅ ∈ y ⊆ 𝒟`, impossible.) These are exactly the total elements. -/
theorem singleton_isTotal (n : ℕ) :
    neighborhoodSystem.IsTotal (neighborhoodSystem.principal (mem_singleton n)) := by
  intro y hy W hW
  have hn : y.mem {n} := hy {n} ⟨mem_singleton n, subset_rfl⟩
  refine ⟨y.sub hW, ?_⟩
  by_contra hc
  rw [Set.singleton_subset_iff] at hc
  have hempty : ({n} : Set ℕ) ∩ W = (∅ : Set ℕ) := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, hk⟩
    exact hc hk
  have hi := y.inter_mem hn hW
  rw [hempty] at hi
  exact empty_not_mem (y.sub hi)

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise114.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise114

set_option linter.unusedVariables false

theorem example_114 : ∀ (n : Nat),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
    DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Nat
      DomainTheory.NeighbourhoodSystems.Exercise114.neighborhoodSystem
      (@Singleton.singleton Nat (Set Nat) (@Set.instSingletonSet Nat) n)
      (DomainTheory.NeighbourhoodSystems.Exercise114.mem_singleton n)) :=
  DomainTheory.NeighbourhoodSystems.Exercise114.singleton_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise114
end

section
-- Exercise115/flatMem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Neighbourhoods of the flat domain: `Δ = ℕ` together with all singletons. -/
def flatMem (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/singleton_disjoint.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- `{n} ∩ {m} = ∅` for `n ≠ m`. -/
theorem singleton_disjoint {n m : ℕ} (h : n ≠ m) : ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h2⟩
  exact h h2

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flatNOD.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem flatNOD : NestedOrDisjoint flatMem := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 1.15 — the flat domain.** `𝒟 = {ℕ} ∪ {{n}}`. -/
def flat : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint flatMem Set.univ Set.univ_nonempty
    (Or.inl rfl) flatNOD (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem flat_mem {X : Set ℕ} : flat.mem X ↔ X = Set.univ ∨ ∃ n, X = {n} := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_master.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

@[simp] theorem flat_master : flat.master = Set.univ := rfl

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stemMem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Neighbourhoods of the stem domain: `Δ = ℕ`, the pair `{0,1}`, and all singletons. -/
def stemMem (X : Set ℕ) : Prop := X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n}

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stemNOD.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem stemNOD : NestedOrDisjoint stemMem := by
  have pair_single : ∀ m : ℕ, ({m} : Set ℕ) ⊆ {0, 1} ∨ ({0, 1} : Set ℕ) ∩ {m} = ∅ := by
    intro m
    by_cases h : m = 0 ∨ m = 1
    · refine Or.inl ?_
      rcases h with rfl | rfl <;> intro k hk <;> simp_all
    · refine Or.inr ?_
      ext k
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro (rfl | rfl) rfl <;> simp_all
  rintro X Y (rfl | rfl | ⟨n, rfl⟩) (rfl | rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · exact Or.inl (subset_refl _)
  · rcases pair_single m with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Set.subset_univ _)
  · rcases pair_single n with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 1.15 — the stem domain.** `𝒟 = {ℕ, {0,1}} ∪ {{n}}`. -/
def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ Set.univ_nonempty
    (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/Basic.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


@[simp] theorem stem_mem {X : Set ℕ} :
    stem.mem X ↔ X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n} := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_empty_not_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem flat_empty_not_mem : ¬ flat.mem (∅ : Set ℕ) := by
  rintro (h | ⟨n, h⟩)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty n)

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_mem_singleton.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- The atom `↑{n}` (a finite element). -/
theorem flat_mem_singleton (n : ℕ) : flat.mem {n} := Or.inr ⟨n, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_classify.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Flat classification.** Every element is `⊥` or an atom `↑{n}`. *Classical.* -/
theorem flat_classify (x : flat.Element) :
    x = flat.bot ∨ ∃ n, x = flat.principal (flat_mem_singleton n) := by
  classical
  by_cases h : ∃ n, x.mem {n}
  · obtain ⟨n, hn⟩ := h
    refine Or.inr ⟨n, ?_⟩
    have huniq : ∀ m, x.mem {m} → m = n := by
      intro m hm
      by_contra hmn
      have hi : x.mem (({m} : Set ℕ) ∩ {n}) := x.inter_mem hm hn
      rw [singleton_disjoint hmn] at hi
      exact flat_empty_not_mem (x.sub hi)
    apply Element.ext
    intro W
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · exact ⟨Or.inl rfl, Set.subset_univ _⟩
      · obtain rfl := huniq k hx
        exact ⟨flat_mem_singleton k, subset_rfl⟩
    · rintro ⟨hWmem, hsub⟩
      exact x.up_mem hn hWmem hsub
  · refine Or.inl ?_
    apply Element.ext
    intro W
    rw [flat.mem_bot]
    constructor
    · intro hx
      rcases (x.sub hx) with rfl | ⟨k, rfl⟩
      · rfl
      · exact absurd ⟨k, hx⟩ h
    · rintro rfl
      exact x.master_mem

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_all_finite.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **All elements of `flat` are finite** (principal). -/
theorem flat_all_finite (x : flat.Element) : ∃ (X : Set ℕ) (h : flat.mem X), x = flat.principal h := by
  rcases flat_classify x with rfl | ⟨n, rfl⟩
  · exact ⟨flat.master, flat.master_mem, rfl⟩
  · exact ⟨{n}, flat_mem_singleton n, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_atom_maximal.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Flat: every atom is maximal (total).** -/
theorem flat_atom_maximal (n : ℕ) (y : flat.Element)
    (hle : flat.principal (flat_mem_singleton n) ≤ y) :
    y = flat.principal (flat_mem_singleton n) := by
  rcases flat_classify y with rfl | ⟨m, rfl⟩
  · exfalso
    have hmem : flat.bot.mem {n} := hle {n} ⟨flat_mem_singleton n, subset_rfl⟩
    rw [flat.mem_bot, flat_master] at hmem
    have : (n + 1) ∈ ({n} : Set ℕ) := by rw [hmem]; exact Set.mem_univ _
    simp at this
  · have hsub : ({m} : Set ℕ) ⊆ {n} :=
      (flat.principal_le_iff (flat_mem_singleton n) (flat_mem_singleton m)).mp hle
    obtain rfl : m = n := Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp hsub)
    rfl

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_infinite.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- `flat` is infinite: the atoms `↑{n}` are pairwise distinct. -/
theorem flat_infinite : Function.Injective (fun n => flat.principal (flat_mem_singleton n)) := by
  intro n m h
  have := flat.principal_injective (flat_mem_singleton n) (flat_mem_singleton m) h
  exact Set.singleton_injective this

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_no_three_chain.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Flat has no strict 3-chain** (`a ⊏ b ⊏ c` is impossible): `⊥` is least and atoms are maximal. -/
theorem flat_no_three_chain : ¬ ∃ a b c : flat.Element, a < b ∧ b < c := by
  rintro ⟨a, b, c, hab, hbc⟩
  rcases flat_classify b with rfl | ⟨n, rfl⟩
  · exact absurd (le_antisymm hab.le (flat.bot_le a)) (ne_of_lt hab)
  · exact (ne_of_lt hbc) (flat_atom_maximal n c hbc.le).symm

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/flat_no_infinite_chain.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Flat has no infinite ascending chain.** -/
theorem flat_no_infinite_chain : ¬ ∃ f : ℕ → flat.Element, StrictMono f := by
  rintro ⟨f, hf⟩
  exact flat_no_three_chain
    ⟨f 0, f 1, f 2, hf (by norm_num), hf (by norm_num)⟩

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stem_mem_pair.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem stem_mem_pair : stem.mem {0, 1} := Or.inr (Or.inl rfl)
end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stem_mem_univ.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem stem_mem_univ : stem.mem Set.univ := Or.inl rfl
end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stem_mem_zero.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


theorem stem_mem_zero : stem.mem {0} := Or.inr (Or.inr ⟨0, rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stem_principal_lt.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- A strict step between principal filters of `stem`: `Y ⊊ X` (proper) gives `↑X ⊏ ↑Y`. -/
theorem stem_principal_lt {X Y : Set ℕ} (hX : stem.mem X) (hY : stem.mem Y)
    (hYX : Y ⊆ X) (hne : X ≠ Y) : stem.principal hX < stem.principal hY := by
  rw [lt_iff_le_and_ne]
  refine ⟨(stem.principal_le_iff hX hY).mpr hYX, ?_⟩
  intro he
  exact hne (stem.principal_injective hX hY he)

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/stem_three_chain.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Stem contains a strict 3-chain** `⊥ = ↑ℕ ⊏ ↑{0,1} ⊏ ↑{0}` — the structural feature that
distinguishes it from `flat`. -/
theorem stem_three_chain : ∃ a b c : stem.Element, a < b ∧ b < c := by
  refine ⟨stem.principal stem_mem_univ, stem.principal stem_mem_pair,
    stem.principal stem_mem_zero, ?_, ?_⟩
  · refine stem_principal_lt stem_mem_univ stem_mem_pair (Set.subset_univ _) ?_
    intro h
    have : (2 : ℕ) ∈ ({0, 1} : Set ℕ) := h ▸ Set.mem_univ 2
    simp at this
  · refine stem_principal_lt stem_mem_pair stem_mem_zero
      (Set.singleton_subset_iff.mpr (by simp)) ?_
    intro h
    have : (1 : ℕ) ∈ ({0} : Set ℕ) := h ▸ (by simp : (1 : ℕ) ∈ ({0, 1} : Set ℕ))
    simp at this

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115/not_isomorphic.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/- concordance: source L458 EXERCISE 1.15 finite elements without chains -/
/-- **Exercise 1.15.** `flat` and `stem` are *not* isomorphic: an order-isomorphism would transport
`stem`'s strict 3-chain `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` back to a strict 3-chain in `flat`, which has none. -/
theorem not_isomorphic : ¬ (flat ≅ᴰ stem) := by
  rintro ⟨e⟩
  obtain ⟨a, b, c, hab, hbc⟩ := stem_three_chain
  exact flat_no_three_chain
    ⟨e.symm a, e.symm b, e.symm c, e.symm.lt_iff_lt.mpr hab, e.symm.lt_iff_lt.mpr hbc⟩

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise115.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise115

set_option linter.unusedVariables false

theorem example_115 : Not
  (@DomainTheory.NeighbourhoodSystems.Isomorphic Nat Nat DomainTheory.NeighbourhoodSystems.Exercise115.flat
    DomainTheory.NeighbourhoodSystems.Exercise115.stem) :=
  DomainTheory.NeighbourhoodSystems.Exercise115.not_isomorphic

end DomainTheory.NeighbourhoodSystems.Exercise115
end

section
-- Exercise116/cofiniteSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/- concordance: source L462 EXERCISE 1.16 cofinite integer subsets -/
/-- **Exercise 1.16 — the cofinite neighbourhood system on `ℕ`.** `X ∈ 𝒟 ⟺ Xᶜ` finite;
closed under finite intersection since `(X∩Y)ᶜ = Xᶜ ∪ Yᶜ`. -/
def cofiniteSystem : NeighborhoodSystem ℕ where
  mem X := Xᶜ.Finite
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := by rw [Set.compl_univ]; exact Set.finite_empty
  inter_mem := by
    intro X Y _ hX hY _ _
    rw [Set.compl_inter]
    exact hX.union hY
  sub_master := fun _ => Set.subset_univ _

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/cofiniteSystem_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem cofiniteSystem_mem {X : Set ℕ} : cofiniteSystem.mem X ↔ Xᶜ.Finite := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/ofExcluded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- The filter generated by an arbitrary set `E ⊆ ℕ` of "excluded points":
`ofExcluded E = {Y cofinite ∣ Yᶜ ⊆ E}`. This is a filter for *every* `E`. -/
def ofExcluded (E : Set ℕ) : cofiniteSystem.Element where
  mem Y := Yᶜ.Finite ∧ Yᶜ ⊆ E
  sub h := h.1
  master_mem := by
    show (Set.univ : Set ℕ)ᶜ.Finite ∧ (Set.univ : Set ℕ)ᶜ ⊆ E
    rw [Set.compl_univ]
    exact ⟨Set.finite_empty, Set.empty_subset E⟩
  inter_mem := by
    rintro Y1 Y2 ⟨hf1, hs1⟩ ⟨hf2, hs2⟩
    rw [Set.compl_inter]
    exact ⟨hf1.union hf2, Set.union_subset hs1 hs2⟩
  up_mem := by
    rintro Y1 Y2 ⟨_, hs1⟩ hY2 hsub
    exact ⟨hY2, (Set.compl_subset_compl.mpr hsub).trans hs1⟩

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/mem_ofExcluded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem mem_ofExcluded {E Y : Set ℕ} :
    (ofExcluded E).mem Y ↔ Yᶜ.Finite ∧ Yᶜ ⊆ E := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/toExcluded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- The set of points *excluded* by a filter `x`: `toExcluded x = {n ∣ {n}ᶜ ∈ x}`. -/
def toExcluded (x : cofiniteSystem.Element) : Set ℕ := {n | x.mem ({n}ᶜ)}

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/mem_toExcluded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

@[simp] theorem mem_toExcluded {x : cofiniteSystem.Element} {n : ℕ} :
    n ∈ toExcluded x ↔ x.mem ({n}ᶜ) := Iff.rfl

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/fullSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Exercise 1.16 (second example).** All subsets of `ℕ` form a neighbourhood system, trivially
closed under *all* finite intersections. Unlike `cofiniteSystem` it is **not** positive (`∅` is a
neighbourhood). Every neighbourhood is a finite element via `principal`; its total elements are
the principal filters of singletons (the system is "flat"). -/
def fullSystem : NeighborhoodSystem ℕ where
  mem _ := True
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := trivial
  inter_mem := fun _ _ _ _ => trivial
  sub_master := fun _ => Set.subset_univ _

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/mem_compl_of_finite.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Reconstruction lemma.** For finite `F` of points each of whose single-deletion `{n}ᶜ`
is in the filter `x`, the intersection `⋂_{n∈F} {n}ᶜ = Fᶜ` is also in `x`. -/
theorem mem_compl_of_finite (x : cofiniteSystem.Element) {F : Set ℕ} (hF : F.Finite) :
    (∀ n ∈ F, x.mem ({n}ᶜ)) → x.mem (Fᶜ) := by
  induction F, hF using Set.Finite.induction_on with
  | empty => intro _; rw [Set.compl_empty]; exact x.master_mem
  | @insert a s _ _ ih =>
    intro h
    rw [Set.insert_eq, Set.compl_union]
    exact x.inter_mem (h a (Set.mem_insert a s))
      (ih (fun n hn => h n (Set.mem_insert_of_mem a hn)))

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/mem_compl_singleton.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- Each `{n}ᶜ` is a neighbourhood (its complement `{n}` is finite). -/
theorem mem_compl_singleton (n : ℕ) : cofiniteSystem.mem (({n} : Set ℕ)ᶜ) := by
  rw [cofiniteSystem_mem, compl_compl]
  exact Set.finite_singleton n

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/subset_compl_singleton.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- For `n ∉ Y`, the neighbourhood `Y` is contained in `{n}ᶜ`. -/
theorem subset_compl_singleton {Y : Set ℕ} {n : ℕ} (hn : n ∈ Yᶜ) : Y ⊆ ({n} : Set ℕ)ᶜ := by
  intro m hm
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  rintro rfl
  exact hn hm

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/ofExcluded_toExcluded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

theorem ofExcluded_toExcluded (x : cofiniteSystem.Element) :
    ofExcluded (toExcluded x) = x := by
  apply Element.ext
  intro Y
  rw [mem_ofExcluded]
  constructor
  · rintro ⟨hfin, hsub⟩
    have h := mem_compl_of_finite x hfin (fun n hn => mem_toExcluded.mp (hsub hn))
    rwa [compl_compl] at h
  · intro hxY
    refine ⟨x.sub hxY, ?_⟩
    intro n hn
    rw [mem_toExcluded]
    exact x.up_mem hxY (mem_compl_singleton n) (subset_compl_singleton hn)

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/toExcluded_ofExcluded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

theorem toExcluded_ofExcluded (E : Set ℕ) : toExcluded (ofExcluded E) = E := by
  ext n
  rw [mem_toExcluded, mem_ofExcluded]
  simp [compl_compl, Set.finite_singleton, Set.singleton_subset_iff]

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/cofiniteIso.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem

/-- **Exercise 1.16 — `|𝒟| ≅ (𝒫(ℕ), ⊆)`.** The filter `x` corresponds to its excluded-point
set `toExcluded x`; inclusion of filters matches inclusion of excluded sets. -/
def cofiniteIso : cofiniteSystem.Element ≃o Set ℕ where
  toFun := toExcluded
  invFun := ofExcluded
  left_inv := ofExcluded_toExcluded
  right_inv := toExcluded_ofExcluded
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h Y hY
      have hfin : Yᶜ.Finite := x.sub hY
      have hsub : Yᶜ ⊆ toExcluded x' := by
        intro n hn
        have hx : x.mem (({n} : Set ℕ)ᶜ) :=
          x.up_mem hY (mem_compl_singleton n) (subset_compl_singleton hn)
        exact h (mem_toExcluded.mpr hx)
      have h2 := mem_compl_of_finite x' hfin (fun n hn => mem_toExcluded.mp (hsub hn))
      rwa [compl_compl] at h2
    · intro h n hn
      exact mem_toExcluded.mpr (h _ (mem_toExcluded.mp hn))

end Cofinite

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/le_ofExcluded_univ.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem


/-- Every filter is `⊑ ofExcluded ℕ` (the whole family `𝒟`; every cofinite `Y` has `Yᶜ ⊆ ℕ`). -/
theorem le_ofExcluded_univ (x : cofiniteSystem.Element) :
    x ≤ ofExcluded Set.univ := by
  intro Y hY
  exact ⟨x.sub hY, Set.subset_univ _⟩

end Cofinite
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116/ofExcluded_univ_isTotal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Cofinite

open NeighborhoodSystem


/-- **Exercise 1.16 — the unique total element.** `ofExcluded ℕ` (matching the greatest
element `ℕ ∈ 𝒫(ℕ)`) is total: it is `⊑`-maximal. -/
theorem ofExcluded_univ_isTotal : cofiniteSystem.IsTotal (ofExcluded Set.univ) :=
  fun y _ => le_ofExcluded_univ y

end Cofinite
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise116.lean
namespace DomainTheory.NeighbourhoodSystems.Cofinite

set_option linter.unusedVariables false

theorem example_116 : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Nat
  DomainTheory.NeighbourhoodSystems.Cofinite.cofiniteSystem
  (DomainTheory.NeighbourhoodSystems.Cofinite.ofExcluded (@Set.univ Nat)) :=
  DomainTheory.NeighbourhoodSystems.Cofinite.ofExcluded_univ_isTotal

end DomainTheory.NeighbourhoodSystems.Cofinite
end

section
-- Exercise117/ratIntervalMem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- A neighbourhood of `ratIntervalSystem`: either `Δ = ℝ`, or a non-empty open interval with
rational endpoints. -/
def ratIntervalMem (X : Set ℝ) : Prop :=
  X = Set.univ ∨ ∃ a b : ℚ, a < b ∧ X = Set.Ioo (a : ℝ) (b : ℝ)

end RatInterval

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/inter_mem'.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/- concordance: source L464 EXERCISE 1.17 rational open intervals -/
/-- **Exercise 1.17 — intersections.** The intersection of two neighbourhoods that share a point
is again a neighbourhood: `Ioo a b ∩ Ioo c d = Ioo (max a c) (min b d)`, with rational endpoints,
non-empty because it contains the shared point. -/
theorem inter_mem' {X Y : Set ℝ} (hX : ratIntervalMem X) (hY : ratIntervalMem Y)
    (hne : (X ∩ Y).Nonempty) : ratIntervalMem (X ∩ Y) := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · rw [Set.univ_inter]; exact hY
  · rcases hY with rfl | ⟨c, d, hcd, rfl⟩
    · rw [Set.inter_univ]; exact Or.inr ⟨a, b, hab, rfl⟩
    · obtain ⟨z, ⟨hza, hzb⟩, hzc, hzd⟩ := hne
      have had : a < d := by exact_mod_cast hza.trans hzd
      have hcb : c < b := by exact_mod_cast hzc.trans hzb
      have hlt : max a c < min b d := by
        simp only [max_lt_iff, lt_min_iff]
        exact ⟨⟨hab, hcb⟩, had, hcd⟩
      have hset : Set.Ioo (a : ℝ) b ∩ Set.Ioo (c : ℝ) d
          = Set.Ioo ((max a c : ℚ) : ℝ) ((min b d : ℚ) : ℝ) := by
        rw [Set.Ioo_inter_Ioo, Rat.cast_max, Rat.cast_min]
      exact Or.inr ⟨max a c, min b d, hlt, hset⟩

end RatInterval

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/ratIntervalMem_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- Every neighbourhood is non-empty (`Δ`, or `Ioo a b` with `a < b`). -/
theorem ratIntervalMem_nonempty {X : Set ℝ} (hX : ratIntervalMem X) : X.Nonempty := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · exact ⟨0, Set.mem_univ 0⟩
  · rw [Set.nonempty_Ioo]; exact_mod_cast hab

end RatInterval

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/ratIntervalSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- **Exercise 1.17 — the rational-interval neighbourhood system over `ℝ`.** -/
def ratIntervalSystem : NeighborhoodSystem ℝ where
  mem := ratIntervalMem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    exact inter_mem' hX hY ((ratIntervalMem_nonempty hZ).mono hZsub)
  sub_master := fun _ => Set.subset_univ _

end RatInterval

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/ratIntervalSystem_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

@[simp] theorem ratIntervalSystem_mem {X : Set ℝ} :
    ratIntervalSystem.mem X ↔ ratIntervalMem X := Iff.rfl

end RatInterval

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/filterAt.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- **Exercise 1.17 — the point filter `{X ∈ 𝒟 ∣ t ∈ X}`.** For any real `t` this is a filter:
closure under `∩` uses `inter_mem'` with `t` itself as the shared point. -/
def filterAt (t : ℝ) : ratIntervalSystem.Element where
  mem X := ratIntervalMem X ∧ t ∈ X
  sub h := h.1
  master_mem := ⟨Or.inl rfl, Set.mem_univ t⟩
  inter_mem := by
    rintro X Y ⟨hX, htX⟩ ⟨hY, htY⟩
    exact ⟨inter_mem' hX hY ⟨t, htX, htY⟩, htX, htY⟩
  up_mem := by
    rintro X Y ⟨_, htX⟩ hY hXY
    exact ⟨hY, hXY htX⟩

end RatInterval

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem


@[simp] theorem mem_filterAt {t : ℝ} {X : Set ℝ} :
    (filterAt t).mem X ↔ ratIntervalMem X ∧ t ∈ X := Iff.rfl
end RatInterval
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117/filterAt_injective.lean
namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem


/-- **Exercise 1.17 — `ℝ ↪ |𝒟|`.** Distinct reals give distinct point filters: between any two
reals lies a rational interval separating them. -/
theorem filterAt_injective {s t : ℝ} (h : filterAt s = filterAt t) : s = t := by
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt t
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have htmem : (filterAt t).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [← h] at htmem
    exact absurd htmem.2.1 (not_lt.mpr ha1.le)
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt s
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have hsmem : (filterAt s).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [h] at hsmem
    exact absurd hsmem.2.1 (not_lt.mpr ha1.le)

end RatInterval
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise117.lean
namespace DomainTheory.NeighbourhoodSystems.RatInterval

set_option linter.unusedVariables false

theorem example_117 : And
  (∀ {s t : Real},
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Real
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalSystem)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt s)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt t) →
      @Eq Real s t)
  (∀ {X Y : Set Real},
    DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem X →
      DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem Y →
        @Set.Nonempty Real (@Inter.inter (Set Real) (@Set.instInter Real) X Y) →
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem
            (@Inter.inter (Set Real) (@Set.instInter Real) X Y)) :=
  @And.intro
  (∀ {s t : Real},
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Real
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalSystem)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt s)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt t) →
      @Eq Real s t)
  (∀ {X Y : Set Real},
    DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem X →
      DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem Y →
        @Set.Nonempty Real (@Inter.inter (Set Real) (@Set.instInter Real) X Y) →
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem
            (@Inter.inter (Set Real) (@Set.instInter Real) X Y))
  @DomainTheory.NeighbourhoodSystems.RatInterval.filterAt_injective
  @DomainTheory.NeighbourhoodSystems.RatInterval.inter_mem'

end DomainTheory.NeighbourhoodSystems.RatInterval
end

section
-- Exercise118/A.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `A = {0,1}`. -/
def A : Set (Fin 3) := {0, 1}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/B.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `B = {1,2}`. -/
def B : Set (Fin 3) := {1, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/Cc.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- `Cc = {0,2}`. -/
def Cc : Set (Fin 3) := {0, 2}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/FinitelyConsistent.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L466 EXERCISE 1.18 consistency of neighbourhood families -/
/-- **Exercise 1.18 — consistent subset.** `C ⊆ 𝒟` is *finitely consistent* iff every finite
sequence drawn from `C` is `Consistent` in `𝒟`. -/
def FinitelyConsistent (C : Set (Set α)) : Prop :=
  ∀ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) → V.Consistent X n

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/appendSeq.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- Concatenation of two finite sequences: the first `n1` entries are `X1 0, …, X1 (n1-1)`,
then `X2 0, X2 1, …`. -/
def appendSeq {α : Type*} (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) : ℕ → Set α :=
  fun i => if i < n1 then X1 i else X2 (i - n1)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/appendSeq_mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- Each entry of `appendSeq X1 n1 X2` below `n1 + n2` is drawn from `C`. -/
theorem appendSeq_mem {α : Type*} {C : Set (Set α)} {X1 : ℕ → Set α} {n1 : ℕ}
    {X2 : ℕ → Set α} {n2 : ℕ} (h1 : ∀ i, i < n1 → X1 i ∈ C) (h2 : ∀ i, i < n2 → X2 i ∈ C) :
    ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := by
  intro i hi
  simp only [appendSeq]
  by_cases h : i < n1
  · rw [ite_eq_left h]; exact h1 i h
  · rw [ite_eq_right h]; exact h2 (i - n1) (by omega)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/family.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- The three-member family `C = {A, B, Cc}`. -/
def family : Set (Set (Fin 3)) := {A, B, Cc}

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/interUpTo_appendSeq_left.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- For a prefix length `k ≤ n1`, `interUpTo` of the appended sequence agrees with `interUpTo`
of the first sequence. -/
theorem interUpTo_appendSeq_left (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {k : ℕ}, k ≤ n1 → V.interUpTo (appendSeq X1 n1 X2) k = V.interUpTo X1 k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [interUpTo_succ, interUpTo_succ, ih (Nat.le_of_succ_le hk)]
    have happ : appendSeq X1 n1 X2 k = X1 k := by
      simp only [appendSeq, ite_eq_left (Nat.lt_of_succ_le hk)]
    rw [happ]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/interUpTo_subset_master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is contained in the master neighbourhood (its first factor). -/
theorem interUpTo_subset_master (X : ℕ → Set α) : ∀ n, V.interUpTo X n ⊆ V.master := by
  intro n
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact Set.inter_subset_left.trans ih

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/interUpTo_appendSeq.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The key identity: `⋂_{i<n1+n2} (X1 ⧺ X2)ᵢ = (⋂_{i<n1} X1ᵢ) ∩ (⋂_{i<n2} X2ᵢ)`. -/
theorem interUpTo_appendSeq (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) :
    ∀ {j : ℕ}, V.interUpTo (appendSeq X1 n1 X2) (n1 + j)
      = V.interUpTo X1 n1 ∩ V.interUpTo X2 j := by
  intro j
  induction j with
  | zero =>
    rw [Nat.add_zero, V.interUpTo_appendSeq_left X1 n1 X2 (le_refl n1), interUpTo_zero]
    exact (Set.inter_eq_left.mpr (V.interUpTo_subset_master X1 n1)).symm
  | succ j ih =>
    rw [Nat.add_succ, interUpTo_succ, ih]
    have happ : appendSeq X1 n1 X2 (n1 + j) = X2 j := by
      simp only [appendSeq, ite_eq_right (by omega : ¬ n1 + j < n1)]
      congr 1
      omega
    rw [happ, interUpTo_succ, Set.inter_assoc]

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/leastFilter.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.18 — the least filter containing a consistent `C`.**
`leastFilter C = {Y ∈ 𝒟 ∣ ⋂_{i<n} Xᵢ ⊆ Y for some finite sequence ⟨Xᵢ⟩ from C}`. The
intersection law concatenates two finite sequences (`interUpTo_appendSeq`) and uses finite
consistency to keep their combined intersection in `𝒟`. -/
def leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) : V.Element where
  mem Y := V.mem Y ∧ ∃ (n : ℕ) (X : ℕ → Set α), (∀ i, i < n → X i ∈ C) ∧ V.interUpTo X n ⊆ Y
  sub h := h.1
  master_mem :=
    ⟨V.master_mem, 0, (fun _ => V.master), (fun i hi => absurd hi (Nat.not_lt_zero i)),
      V.interUpTo_subset_master _ 0⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n1, X1, hX1C, hX1sub⟩ ⟨hYmem, n2, X2, hX2C, hX2sub⟩
    have hmemC : ∀ i, i < n1 + n2 → appendSeq X1 n1 X2 i ∈ C := appendSeq_mem hX1C hX2C
    have hintermem : V.mem (V.interUpTo (appendSeq X1 n1 X2) (n1 + n2)) :=
      (V.consistent_iff_interUpTo_mem _ (fun i hi => hCsub _ (hmemC i hi))).mp
        (hC _ _ hmemC)
    have hsub : V.interUpTo (appendSeq X1 n1 X2) (n1 + n2) ⊆ X ∩ Y := by
      rw [V.interUpTo_appendSeq X1 n1 X2]
      exact Set.inter_subset_inter hX1sub hX2sub
    exact ⟨V.inter_mem hXmem hYmem hintermem hsub, n1 + n2, appendSeq X1 n1 X2, hmemC, hsub⟩
  up_mem := by
    rintro X Y ⟨_, n, Xs, hXC, hsub⟩ hY hXY
    exact ⟨hY, n, Xs, hXC, hsub.trans hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/sInf.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.18 — the intersection of a non-empty family of filters is a filter.**
`sInf F = {X ∣ ∀ x ∈ F, X ∈ x}`. -/
def sInf (F : Set V.Element) (hF : F.Nonempty) : V.Element where
  mem X := ∀ x ∈ F, x.mem X
  sub h := hF.elim (fun x hx => x.sub (h x hx))
  master_mem := fun x _ => x.master_mem
  inter_mem h1 h2 := fun x hx => x.inter_mem (h1 x hx) (h2 x hx)
  up_mem h hY hXY := fun x hx => x.up_mem (h x hx) hY hXY

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triSys.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- All non-empty subsets of `Δ = {0,1,2}` (a positive neighbourhood system). -/
def triSys : NeighborhoodSystem (Fin 3) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (⟨0, Set.mem_univ 0⟩) (⟨0, Set.mem_univ 0⟩)
    (fun {_} _ => Set.subset_univ _) (fun _ _ _ _ => Iff.rfl)

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triple.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

namespace triSys

/-- The triple `A, B, Cc` as a finite sequence. -/
def triple : ℕ → Set (Fin 3) := fun i => if i = 0 then A else if i = 1 then B else Cc

end triSys

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/family_pairwise_nonempty.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


/-- Every pair of members of `family` has non-empty intersection, hence (in the all-non-empty
system `triSys`) every pair is consistent. -/
theorem family_pairwise_nonempty :
    ∀ X ∈ family, ∀ Y ∈ family, (X ∩ Y).Nonempty := by
  intro X hX Y hY
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff] at hX hY
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨1, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩
  · exact ⟨2, by simp [A, B, Cc]⟩
  · exact ⟨0, by simp [A, B, Cc]⟩

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/le_sInf.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `sInf F` is the **greatest** lower bound of `F`. -/
theorem le_sInf (F : Set V.Element) (hF : F.Nonempty) (y : V.Element) (h : ∀ x ∈ F, y ≤ x) :
    y ≤ V.sInf F hF :=
  fun _ hX x hx => h x hx _ hX

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/leastFilter_le.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.18 — `leastFilter` is least.** Any filter `z` with `C ⊆ z` contains
`leastFilter C`. -/
theorem leastFilter_le (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) (z : V.Element) (hz : ∀ W ∈ C, z.mem W) :
    V.leastFilter C hCsub hC ≤ z := by
  rintro Y ⟨hYmem, n, X, hXC, hsub⟩
  exact z.up_mem (z.mem_interUpTo X (fun i hi => hz (X i) (hXC i hi))) hYmem hsub

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/sInf_le.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `sInf F ⊑ x` for every `x ∈ F`. -/
theorem sInf_le (F : Set V.Element) (hF : F.Nonempty) {x : V.Element} (hx : x ∈ F) :
    V.sInf F hF ≤ x :=
  fun _ h => h x hx

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/subset_leastFilter.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `C ⊆ leastFilter C`: every member of `C` is in the least filter. -/
theorem subset_leastFilter (C : Set (Set α)) (hCsub : ∀ X ∈ C, V.mem X)
    (hC : V.FinitelyConsistent C) {W : Set α} (hW : W ∈ C) :
    (V.leastFilter C hCsub hC).mem W := by
  refine ⟨hCsub W hW, 1, (fun _ => W), (fun _ _ => hW), ?_⟩
  rw [interUpTo_succ, interUpTo_zero]
  exact Set.inter_subset_right

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triSys_master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


theorem triSys_master : triSys.master = (Set.univ : Set (Fin 3)) := rfl

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triple_interUpTo_empty.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


theorem triple_interUpTo_empty : triSys.interUpTo triple 3 = (∅ : Set (Fin 3)) := by
  simp only [NeighborhoodSystem.interUpTo_succ, NeighborhoodSystem.interUpTo_zero, triSys_master]
  ext x
  fin_cases x <;> simp [triple, A, B, Cc]

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/triple_mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


theorem triple_mem : ∀ i, i < 3 → triple i ∈ family := by
  intro i hi
  simp only [family, Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118/not_finitelyConsistent.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems


namespace triSys


/-- **Exercise 1.18 — `family` is pairwise consistent but not consistent.** Its full triple has
empty intersection, so no `Z ∈ 𝒟` (i.e. no non-empty `Z`) lies below it. -/
theorem not_finitelyConsistent : ¬ triSys.FinitelyConsistent family := by
  intro h
  obtain ⟨Z, hZmem, hZsub⟩ := h 3 triple triple_mem
  have hZne : Z.Nonempty := hZmem
  rw [triple_interUpTo_empty, Set.subset_empty_iff] at hZsub
  rw [hZsub] at hZne
  exact Set.not_nonempty_empty hZne

end triSys
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise118.lean
namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_118.{u_1} : And
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (C : Set (Set α))
    (hCsub :
      ∀ (X : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
    (hC : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent α V C)
    (z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    (∀ (W : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C W →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V z W) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter α V C hCsub hC) z)
  (Not
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent
      (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) DomainTheory.NeighbourhoodSystems.triSys
      DomainTheory.NeighbourhoodSystems.triSys.family)) :=
  @And.intro
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (C : Set (Set α))
    (hCsub :
      ∀ (X : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
    (hC : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent α V C)
    (z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    (∀ (W : Set α),
        @Membership.mem (Set α) (Set (Set α)) (@Set.instMembership (Set α)) C W →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem α V z W) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter α V C hCsub hC) z)
  (Not
    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.FinitelyConsistent
      (Fin (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) DomainTheory.NeighbourhoodSystems.triSys
      DomainTheory.NeighbourhoodSystems.triSys.family))
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.leastFilter_le)
  DomainTheory.NeighbourhoodSystems.triSys.not_finitelyConsistent

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise119/Tok.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Tokens `Δ = {0, 1, 2}`. -/
abbrev Tok := Fin 3

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/a.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The neighbourhood `{0, 1}`. -/
def a : Set Tok := {0, 1}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/b.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The neighbourhood `{1, 2}`. -/
def b : Set Tok := {1, 2}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- The master neighbourhood `Δ`. -/
def master : Set Tok := Set.univ

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/memSet.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- `𝒟 = {Δ, {0,1}, {1,2}}`. -/
def memSet : Set (Set Tok) := {master, a, b}

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Membership in `𝒟`. -/
def mem (X : Set Tok) : Prop := X ∈ memSet

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_iff.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_iff (X : Set Tok) : mem X ↔ X = master ∨ X = a ∨ X = b := by
  simp only [mem, memSet, Set.mem_insert_iff, Set.mem_singleton_iff]

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/inter_eq.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- Classification of binary intersections in `𝒟`. -/
theorem inter_eq (X Y : Set Tok) (hX : mem X) (hY : mem Y) :
    X ∩ Y = master ∨ X ∩ Y = a ∨ X ∩ Y = b ∨ X ∩ Y = ({1} : Set Tok) := by
  rcases (mem_iff X).mp hX with rfl | rfl | rfl
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inl (by ext x; fin_cases x <;> simp [master, a, b])
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b]))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [master, a, b])))
  · rcases (mem_iff Y).mp hY with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))
    · exact Or.inr (Or.inr (Or.inr (by ext x; fin_cases x <;> simp [master, a, b])))
    · exact Or.inr (Or.inr (Or.inl (by ext x; fin_cases x <;> simp [master, a, b])))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_a.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_a : mem a := (mem_iff _).mpr (Or.inr (Or.inl rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_b.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_b : mem b := (mem_iff _).mpr (Or.inr (Or.inr rfl))

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/mem_master.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

theorem mem_master : mem master := (mem_iff _).mpr (Or.inl rfl)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/not_mem_sub_one.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- No neighbourhood is contained in `{1}` (each contains a token other than `1`). This is why
the overlapping pair `{0,1}`, `{1,2}` never triggers condition (ii). -/
theorem not_mem_sub_one {Z : Set Tok} (hZ : mem Z) (hsub : Z ⊆ ({1} : Set Tok)) : False := by
  rcases (mem_iff Z).mp hZ with rfl | rfl | rfl
  · exact absurd (hsub (show (0 : Tok) ∈ master by simp [master])) (by simp)
  · exact absurd (hsub (show (0 : Tok) ∈ a by simp [a])) (by simp)
  · exact absurd (hsub (show (2 : Tok) ∈ b by simp [b])) (by simp)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/notPositiveSystem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- **Exercise 1.19 — the non-positive example is a neighbourhood system.** The only intersection
that is not already a neighbourhood is `{0,1} ∩ {1,2} = {1}`, and that case is impossible: a
consistency witness `Z ⊆ {1}` with `Z ∈ 𝒟` does not exist (`not_mem_sub_one`). -/
def notPositiveSystem : NeighborhoodSystem Tok where
  mem := mem
  master := master
  master_nonempty := Set.univ_nonempty
  master_mem := mem_master
  sub_master := fun _ => Set.subset_univ _
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    rcases inter_eq X Y hX hY with h | h | h | h
    · rw [h]; exact mem_master
    · rw [h]; exact mem_a
    · rw [h]; exact mem_b
    · rw [h] at hZsub; exact (not_mem_sub_one hZ hZsub).elim

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/positiveExample.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems

/-- All non-empty subsets of `Fin 2` form a *positive* neighbourhood system: there `X ∩ Y ∈ 𝒟`
literally **is** `(X ∩ Y).Nonempty`, so (ii′) is `Iff.rfl`. -/
def positiveExample : NeighborhoodSystem (Fin 2) :=
  NeighborhoodSystem.ofPositive (fun X => X.Nonempty) Set.univ
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩)
    (by exact ⟨(0 : Fin 2), Set.mem_univ 0⟩) (by intro X _; exact Set.subset_univ X)
    (by intro X Y _ _; exact Iff.rfl)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/a_inter_b.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- `{0,1} ∩ {1,2} = {1}`. -/
theorem a_inter_b : a ∩ b = ({1} : Set Tok) := by ext x; fin_cases x <;> simp [a, b]

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/one_not_mem.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- `{1}` is not a neighbourhood (it is neither `Δ`, `{0,1}`, nor `{1,2}`). -/
theorem one_not_mem : ¬ mem ({1} : Set Tok) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h
  · have h0 : (0 : Tok) ∈ master := by simp [master]
    rw [← h] at h0; simp at h0
  · have h0 : (0 : Tok) ∈ a := by simp [a]
    rw [← h] at h0; simp at h0
  · have h2 : (2 : Tok) ∈ b := by simp [b]
    rw [← h] at h2; simp at h2

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/not_isPositive.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- **Exercise 1.19 — the example is not positive.** `{0,1}` and `{1,2}` are neighbourhoods whose
intersection `{1}` is non-empty but is *not* a neighbourhood, contradicting (ii′). -/
theorem not_isPositive : ¬ notPositiveSystem.IsPositive := by
  intro h
  have hab := h (X := a) (Y := b) mem_a mem_b
  rw [a_inter_b] at hab
  exact one_not_mem (hab.mpr ⟨1, rfl⟩)

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise119

set_option linter.unusedVariables false

theorem example_119 : Not
  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive DomainTheory.NeighbourhoodSystems.Exercise119.Tok
    DomainTheory.NeighbourhoodSystems.Exercise119.notPositiveSystem) :=
  DomainTheory.NeighbourhoodSystems.Exercise119.not_isPositive

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise119/positiveExample_isPositive.lean
set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


theorem positiveExample_isPositive : positiveExample.IsPositive := by
  intro X Y _ _
  exact Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise119
end

section
-- Exercise120/upSet.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Exercise 1.20's `↑X = {Y ∈ 𝒟 ∣ Y ⊆ X}` (the up-set of `X` *inside* `𝒟`). -/
def upSet (X : Set α) : Set (Set α) := {Y | V.mem Y ∧ Y ⊆ X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/mem_upSet.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_upSet {X Y : Set α} : Y ∈ V.upSet X ↔ V.mem Y ∧ Y ⊆ X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/upSet_inter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `↑X ∩ ↑Y = ↑(X ∩ Y)` — a set identity (no membership hypotheses). -/
theorem upSet_inter (X Y : Set α) : V.upSet X ∩ V.upSet Y = V.upSet (X ∩ Y) := by
  ext Z
  simp only [Set.mem_inter_iff, mem_upSet, Set.subset_inter_iff]
  tauto

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/upSet_subset_iff.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `X ↦ ↑X` is inclusion-**preserving**: `↑X ⊆ ↑Y ↔ X ⊆ Y` (for `X ∈ 𝒟`).
`→` tests at `X ∈ ↑X`; `←` is transitivity of `⊆`. -/
theorem upSet_subset_iff {X Y : Set α} (hX : V.mem X) : V.upSet X ⊆ V.upSet Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h ⟨hX, subset_rfl⟩).2
  · intro hXY Z hZ
    exact ⟨hZ.1, hZ.2.trans hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/powerSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L472 EXERCISE 1.20 upward closed neighbourhoods -/
/-- **Exercise 1.20 — the power system `𝒟' = {↑X ∣ X ∈ 𝒟}`** over the tokens `Δ' = 𝒟`. The
master is `↑Δ`; the intersection law uses the consistency witness `Z ∈ ↑Z ⊆ ↑X ∩ ↑Y` to get
`Z ⊆ X ∩ Y`, hence `X ∩ Y ∈ 𝒟` and `↑X ∩ ↑Y = ↑(X∩Y)`. -/
def powerSystem : NeighborhoodSystem (Set α) where
  mem S := ∃ X, V.mem X ∧ S = V.upSet X
  master := V.upSet V.master
  master_nonempty := ⟨V.master, V.master_mem, subset_rfl⟩
  master_mem := ⟨V.master, V.master_mem, rfl⟩
  inter_mem := by
    rintro S T W ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ ⟨Z, hZ, rfl⟩ hWsub
    have hZin : Z ∈ V.upSet X ∩ V.upSet Y := hWsub ⟨hZ, subset_rfl⟩
    obtain ⟨⟨_, hZX⟩, _, hZY⟩ := hZin
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hZ (Set.subset_inter hZX hZY)
    exact ⟨X ∩ Y, hXY, V.upSet_inter X Y⟩
  sub_master := by
    intro S hS
    obtain ⟨X, hX, rfl⟩ := hS
    exact (V.upSet_subset_iff hX).mpr (V.sub_master hX)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/powerSystem_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem powerSystem_mem {S : Set (Set α)} :
    V.powerSystem.mem S ↔ ∃ X, V.mem X ∧ S = V.upSet X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/ofPower.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The element of `|𝒟|` corresponding to `y ∈ |𝒟'|`: the filter `{W ∣ ↑W ∈ y}`. -/
def ofPower (y : V.powerSystem.Element) : V.Element where
  mem W := V.mem W ∧ y.mem (V.upSet W)
  sub h := h.1
  master_mem := ⟨V.master_mem, y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨hX, hyX⟩ ⟨hY, hyY⟩
    have hyInter : y.mem (V.upSet X ∩ V.upSet Y) := y.inter_mem hyX hyY
    rw [V.upSet_inter] at hyInter
    obtain ⟨W, hW, hWeq⟩ := y.sub hyInter
    have hWin : W ∈ V.upSet (X ∩ Y) := by rw [hWeq]; exact ⟨hW, subset_rfl⟩
    exact ⟨V.inter_mem hX hY hW hWin.2, hyInter⟩
  up_mem := by
    rintro X Y ⟨hX, hyX⟩ hY hXY
    exact ⟨hY, y.up_mem hyX ⟨Y, hY, rfl⟩ ((V.upSet_subset_iff hX).mpr hXY)⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/toPower.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The element of `|𝒟'|` corresponding to `x ∈ |𝒟|`: the filter `{↑W ∣ W ∈ x}`. -/
def toPower (x : V.Element) : V.powerSystem.Element where
  mem S := ∃ W, x.mem W ∧ S = V.upSet W
  sub := by rintro S ⟨W, hW, rfl⟩; exact ⟨W, x.sub hW, rfl⟩
  master_mem := ⟨V.master, x.master_mem, rfl⟩
  inter_mem := by
    rintro S T ⟨W1, hW1, rfl⟩ ⟨W2, hW2, rfl⟩
    exact ⟨W1 ∩ W2, x.inter_mem hW1 hW2, V.upSet_inter W1 W2⟩
  up_mem := by
    rintro S T ⟨W, hW, rfl⟩ hT hsub
    obtain ⟨W', hW', rfl⟩ := hT
    exact ⟨W', x.up_mem hW hW' ((V.upSet_subset_iff (x.sub hW)).mp hsub), rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/upSet_injective.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `X ↦ ↑X` is one-one on `𝒟`. -/
theorem upSet_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.upSet X = V.upSet Y) : X = Y :=
  Set.Subset.antisymm ((V.upSet_subset_iff hX).mp h.subset)
    ((V.upSet_subset_iff hY).mp h.superset)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/powerIso.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.20 (the isomorphism).** `toPower`/`ofPower` are mutually inverse and
preserve/reflect `⊑`, giving `|𝒟| ≃o |𝒟'|`. -/
def powerIso : V.Element ≃o V.powerSystem.Element where
  toFun := V.toPower
  invFun := V.ofPower
  left_inv := by
    intro x
    apply Element.ext
    intro W
    constructor
    · rintro ⟨hW, W', hW', heq⟩
      rw [V.upSet_injective hW (x.sub hW') heq]; exact hW'
    · intro hx
      exact ⟨x.sub hx, W, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨W, ⟨_, hyW⟩, rfl⟩
      exact hyW
    · intro hyS
      obtain ⟨W, hW, rfl⟩ := y.sub hyS
      exact ⟨W, ⟨hW, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hx
      have hmem : (V.toPower x).mem (V.upSet W) := ⟨W, hx, rfl⟩
      obtain ⟨W', hW', heq⟩ := h (V.upSet W) hmem
      rw [V.upSet_injective (x.sub hx) (x'.sub hW') heq]; exact hW'
    · intro h S hS
      obtain ⟨W, hW, rfl⟩ := hS
      exact ⟨W, h W hW, rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/isomorphic_powerSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.20 (statement).** `𝒟` and its power system `𝒟'` are isomorphic. -/
theorem isomorphic_powerSystem : V ≅ᴰ V.powerSystem := ⟨V.powerIso⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/powerSystem_isPositive.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.20 — `𝒟'` is positive.** `↑X ∩ ↑Y = ↑(X∩Y)` is a neighbourhood iff it is
non-empty: a witness `Z ⊆ X ∩ Y` gives `X ∩ Y ∈ 𝒟`; conversely `↑W` always contains `W`. -/
theorem powerSystem_isPositive : V.powerSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.upSet_inter]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨W, hW, subset_rfl⟩
  · rintro ⟨Z, hZmem, hZsub⟩
    exact ⟨X ∩ Y, V.inter_mem hX hY hZmem hZsub, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120/toPower_principal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.20 — tokens ↔ finite elements.** The iso carries the finite element `↑X` of
`|𝒟|` (Def 1.7) to the finite element of `|𝒟'|` generated by the token `↑X`, i.e. the principal
filter of `↑X` in `𝒟'`. Since `X ↦ ↑X` is one-one (`upSet_injective`), tokens of `𝒟'` and its
finite elements are in one-one correspondence. -/
theorem toPower_principal {X : Set α} (hX : V.mem X) :
    V.toPower (V.principal hX) = V.powerSystem.principal ⟨X, hX, rfl⟩ := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨W, ⟨hWmem, hXW⟩, rfl⟩
    exact ⟨⟨W, hWmem, rfl⟩, (V.upSet_subset_iff hX).mpr hXW⟩
  · rintro ⟨⟨W, hWmem, rfl⟩, hsub⟩
    exact ⟨W, ⟨hWmem, (V.upSet_subset_iff hX).mp hsub⟩, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise120.lean
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_120.{u_1} : And
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower α V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
        (@Exists.intro (Set α)
          (fun (X_1 : Set α) =>
            And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X_1)
              (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X_1)))
          X
          (@And.intro (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
            (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            hX (@rfl (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)))))) :=
  @And.intro
  (And
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Eq
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower α V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
        (@Exists.intro (Set α)
          (fun (X_1 : Set α) =>
            And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X_1)
              (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X_1)))
          X
          (@And.intro (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X)
            (@Eq (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))
            hX (@rfl (Set (Set α)) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X))))))
  (@And.intro
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (Set α) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive (Set α)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem α V))
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isomorphic_powerSystem
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.powerSystem_isPositive)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toPower_principal

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end

section
-- Exercise122/basicOpen.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}` (Theorem 1.10 notation): the set of elements of the domain
`|𝒟|` that contain the neighbourhood `X`. These sets are the basic opens of the topology of
Exercise 1.22. -/
def basicOpen (X : Set α) : Set V.Element := {x | x.mem X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/mem_basicOpen.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_basicOpen {X : Set α} {x : V.Element} :
    x ∈ V.basicOpen X ↔ x.mem X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/OpenFilter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- A set `𝒰 ⊆ |𝒟|` is *open* (Exercise 1.22, condition (ii)) when every point `x ∈ 𝒰` has a
basic neighbourhood `[X]` with `X ∈ x` contained in `𝒰`. -/
class OpenFilter (U : Set V.Element) : Prop where
  out : ∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `[X ∩ Y] ⊆ [X]` whenever `X ∈ 𝒟`: a filter containing `X ∩ Y` contains `X` (upward closure).
This (with the symmetric version) is the closure of the basic opens under finite intersection,
i.e. `[X] ∩ [Y] = [X ∩ Y]`, the base condition behind the topology. -/
theorem basicOpen_inter_subset_left {X Y : Set α} (hX : V.mem X) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen X :=
  fun z hz => z.up_mem hz hX Set.inter_subset_left

/-- `[X ∩ Y] ⊆ [Y]` whenever `Y ∈ 𝒟`. -/
theorem basicOpen_inter_subset_right {X Y : Set α} (hY : V.mem Y) :
    V.basicOpen (X ∩ Y) ⊆ V.basicOpen Y :=
  fun z hz => z.up_mem hz hY Set.inter_subset_right


/-- **Exercise 1.22 (the space).** The basic opens `[X]` (`X ∈ 𝒟`) generate a topology on `|𝒟|`:
`𝒰` is open iff it is a union of basic opens (condition (ii)). The three axioms hold because the
base is closed under finite intersection (`basicOpen_inter_subset_left/right`, using that filters
are `∩`-closed and upward closed) with `[Δ] = |𝒟|` covering the space. -/
instance instTopologicalSpaceElement : TopologicalSpace V.Element where
  IsOpen := V.OpenFilter
  isOpen_univ := ⟨fun x _ => ⟨V.master, x.master_mem, Set.subset_univ _⟩⟩
  isOpen_inter := by
    intro U W hU hW
    constructor
    intro x hx
    obtain ⟨hxU, hxW⟩ := hx
    obtain ⟨X, hX, hXU⟩ := hU.out x hxU
    obtain ⟨Y, hY, hYW⟩ := hW.out x hxW
    refine ⟨X ∩ Y, x.inter_mem hX hY, fun z hz => ⟨hXU ?_, hYW ?_⟩⟩
    · exact V.basicOpen_inter_subset_left (x.sub hX) hz
    · exact V.basicOpen_inter_subset_right (x.sub hY) hz
  isOpen_sUnion := by
    intro S hS
    constructor
    intro x hx
    obtain ⟨t, htS, hxt⟩ := hx
    obtain ⟨X, hX, hXt⟩ := (hS t htS).out x hxt
    exact ⟨X, hX, hXt.trans fun _ ha => ⟨t, htS, ha⟩⟩
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/isOpen_basicOpen.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/- concordance: source L492 EXERCISE 1.22 topology of a domain -/
/-- **Exercise 1.22.** Each basic neighbourhood `[X]` is open. -/
theorem isOpen_basicOpen (X : Set α) : IsOpen (V.basicOpen X) :=
  ⟨fun _ hx => ⟨X, hx, subset_rfl⟩⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/isOpen_iff_isOpenFilter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `IsOpen` for `|𝒟|` is exactly Scott's condition (ii). -/
theorem isOpen_iff_isOpenFilter (U : Set V.Element) : IsOpen U ↔ V.OpenFilter U :=
  ⟨fun h => h, fun h => h⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/isOpen_isUpperSet.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.22, condition (i).** Every open set is upward closed under the approximation order
`⊑`: if `x ∈ 𝒰` and `x ⊑ y` then `y ∈ 𝒰`. (This is a *consequence* of (ii): the basic
neighbourhood `[X] ⊆ 𝒰` witnessing `x ∈ 𝒰` also contains every `y ⊒ x`.) -/
theorem isOpen_isUpperSet {U : Set V.Element} (hU : IsOpen U) :
    ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U := by
  intro x y hxU hxy
  obtain ⟨X, hX, hXU⟩ := hU.out x hxU
  exact hXU (hxy X hX)

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/isOpen_iff_upper_basic.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.22 (characterization of open sets).** A subset `𝒰 ⊆ |𝒟|` is open iff
(i) it is upward closed under `⊑`, and (ii) every point of `𝒰` has a basic neighbourhood `[X]`
(`X ∈ x`) contained in `𝒰`. -/
theorem isOpen_iff_upper_basic (U : Set V.Element) :
    IsOpen U ↔
      (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
        (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U) := by
  constructor
  · intro hU
    exact ⟨V.isOpen_isUpperSet hU, hU.out⟩
  · rintro ⟨_, h2⟩
    exact ⟨h2⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/le_iff_isOpen_imp.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.22, condition (iii).** The approximation order is recovered from the topology:
`x ⊑ y` iff every open set containing `x` also contains `y`.

* `→` is upward closure of opens (`isOpen_isUpperSet`);
* `←` tests against the open basic neighbourhood `[X]` for each `X ∈ x`. -/
theorem le_iff_isOpen_imp (x y : V.Element) :
    x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U := by
  constructor
  · intro hxy U hU hxU
    exact V.isOpen_isUpperSet hU hxU hxy
  · intro h
    exact fun X hX => h (V.basicOpen X) (V.isOpen_basicOpen X) hX

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.22 (assembled).** Open sets are upward closed; basic opens are open; opens are
exactly the upper sets covered by basic opens; and `⊑` is specialization in the Scott topology. -/
example :
    (∀ {U : Set V.Element}, IsOpen U → ∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
      (∀ X : Set α, IsOpen (V.basicOpen X)) ∧
      (∀ U : Set V.Element,
        IsOpen U ↔
          (∀ ⦃x y : V.Element⦄, x ∈ U → x ≤ y → y ∈ U) ∧
            (∀ x ∈ U, ∃ X, x.mem X ∧ V.basicOpen X ⊆ U)) ∧
      (∀ x y : V.Element, x ≤ y ↔ ∀ U : Set V.Element, IsOpen U → x ∈ U → y ∈ U) :=
  ⟨V.isOpen_isUpperSet, V.isOpen_basicOpen, V.isOpen_iff_upper_basic, V.le_iff_isOpen_imp⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise122/specializes_iff_le.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- The approximation order `⊑` is the opposite of Mathlib's specialization preorder `⤳`:
`y ⤳ x ↔ x ⊑ y`. (Scott's (iii) says exactly that `⊑` is the specialization order of this
topology.) -/
theorem specializes_iff_le (x y : V.Element) : y ⤳ x ↔ x ≤ y := by
  rw [specializes_iff_forall_open]
  exact (V.le_iff_isOpen_imp x y).symm

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise124/chainUnion.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L532 EXERCISE 1.24 extending partial elements -/
/-- **Exercise 1.24 — the union of a chain of filters is a filter.** For a non-empty chain `C` of
filters, `⋃ C = {X ∣ ∃ x ∈ C, X ∈ x}` is again a filter. The intersection axiom uses chain
totality: given `X ∈ x` and `Y ∈ y` with `x, y ∈ C`, one of `x ⊑ y`, `y ⊑ x` holds, and the larger
filter contains both `X` and `Y`, hence `X ∩ Y`. -/
def chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C) : V.Element where
  mem X := ∃ x ∈ C, x.mem X
  sub := by rintro X ⟨x, _, hxX⟩; exact x.sub hxX
  master_mem := by obtain ⟨x, hxC⟩ := hne; exact ⟨x, hxC, x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ ⟨y, hyC, hyY⟩
    rcases hchain.total hxC hyC with hxy | hyx
    · exact ⟨y, hyC, y.inter_mem (hxy X hxX) hyY⟩
    · exact ⟨x, hxC, x.inter_mem hxX (hyx Y hyY)⟩
  up_mem := by
    rintro X Y ⟨x, hxC, hxX⟩ hY hXY
    exact ⟨x, hxC, x.up_mem hxX hY hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise124/le_chainUnion.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- Every member of the chain approximates the union `⋃ C`. -/
theorem le_chainUnion (C : Set V.Element) (hne : C.Nonempty) (hchain : IsChain (· ≤ ·) C)
    {x : V.Element} (hx : x ∈ C) : x ≤ V.chainUnion C hne hchain :=
  fun _ hX => ⟨x, hx, hX⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise124/exists_total_ge.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.24 — partial elements extend to total ones (AC).** Using Zorn's lemma, every
element `x` admits a *total* element `t` with `x ⊑ t`. The upper bound of any non-empty chain in
`Ici x` is its `chainUnion`, so a maximal element exists; maximality is exactly totality
(`IsMax = IsTotal`). -/
theorem exists_total_ge (x : V.Element) : ∃ t, V.IsTotal t ∧ x ≤ t := by
  obtain ⟨m, hxm, hmax⟩ :=
    zorn_le_nonempty_Ici₀ x
      (fun c _ hchain y hy =>
        ⟨V.chainUnion c ⟨y, hy⟩ hchain, fun z hz => V.le_chainUnion c ⟨y, hy⟩ hchain hz⟩)
      x le_rfl
  exact ⟨m, fun y hy => hmax hy, hxm⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise124.lean
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_124.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  ∃ (t : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
    And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal α V t)
      (@LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        x t) :=
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.exists_total_ge

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end

section
-- Exercise125/upperSet_subset_or.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

/-- In a linear order, any two upper sets are nested. (Hence final segments are
*nested-or-disjoint* — in fact always nested.) -/
theorem upperSet_subset_or {Δ : Type*} [LinearOrder Δ] {X Y : Set Δ}
    (hX : IsUpperSet X) (hY : IsUpperSet Y) : X ⊆ Y ∨ Y ⊆ X := by
  by_cases h : X ⊆ Y
  · exact Or.inl h
  · right
    rw [Set.not_subset] at h
    obtain ⟨a, haX, haY⟩ := h
    intro b hbY
    rcases le_total a b with hab | hba
    · exact hX hab haX
    · exact absurd (hY hba hbY) haY

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/finalSegmentSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

/- concordance: source L536 EXERCISE 1.25 final segments of ordinals -/
/-- **Exercise 1.25 — the final-segment neighbourhood system.** Over a (non-empty) linear order
`Δ`, the non-empty upper sets (final segments) form a neighbourhood system. Built via
`ofNestedOrDisjoint` since any two upper sets are nested (`upperSet_subset_or`). -/
def finalSegmentSystem (Δ : Type*) [LinearOrder Δ] [Nonempty Δ] : NeighborhoodSystem Δ :=
  NeighborhoodSystem.ofNestedOrDisjoint
    (fun X => X.Nonempty ∧ IsUpperSet X)
    Set.univ
    Set.univ_nonempty
    ⟨Set.univ_nonempty, isUpperSet_univ⟩
    (fun _ _ hX hY => (upperSet_subset_or hX.2 hY.2).imp_right Or.inl)
    (fun _ => Set.subset_univ _)

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/mem_def.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

@[simp] theorem mem_def {X : Set Δ} :
    (finalSegmentSystem Δ).mem X ↔ X.Nonempty ∧ IsUpperSet X := Iff.rfl

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/master_eq.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

@[simp] theorem master_eq : (finalSegmentSystem Δ).master = Set.univ := rfl

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/Ici_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

/-- Each `Set.Ici a` is a (non-empty, upper) neighbourhood. -/
theorem Ici_mem (a : Δ) : (finalSegmentSystem Δ).mem (Set.Ici a) :=
  ⟨⟨a, le_refl a⟩, isUpperSet_Ici a⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/exists_Ici_of_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- **Well-order key lemma.** In a well-order, every non-empty upper set is `Set.Ici a`, where `a`
is its least element. -/
theorem exists_Ici_of_mem {X : Set Δ} (hX : (finalSegmentSystem Δ).mem X) :
    ∃ a, X = Set.Ici a := by
  obtain ⟨a, haX, hmin⟩ := wellFounded_lt.has_min X hX.1
  refine ⟨a, Set.ext fun b => ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rcases lt_or_ge b a with hlt | hge
    · exact absurd hlt (hmin b hb)
    · exact hge
  · exact hX.2 (Set.mem_Ici.mp hb) haX

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/lowerSetOf.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- The trace `lowerSetOf x = {a ∣ Ici a ∈ x}` of a filter `x`. -/
def lowerSetOf (x : (finalSegmentSystem Δ).Element) : Set Δ :=
  {a : Δ | x.mem (Set.Ici a)}

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/lowerSetOf_isLowerSet.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

omit [WellFoundedLT Δ] in
theorem lowerSetOf_isLowerSet (x : (finalSegmentSystem Δ).Element) :
    IsLowerSet (lowerSetOf x) := by
  intro a b hba ha
  exact x.up_mem ha (Ici_mem b) (Set.Ici_subset_Ici.mpr hba)

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/lowerSetOf_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

theorem lowerSetOf_nonempty (x : (finalSegmentSystem Δ).Element) : (lowerSetOf x).Nonempty := by
  obtain ⟨a, ha⟩ := exists_Ici_of_mem (X := (Set.univ : Set Δ)) ⟨Set.univ_nonempty, isUpperSet_univ⟩
  refine ⟨a, ?_⟩
  have hu : x.mem (Set.univ) := x.master_mem
  rw [ha] at hu
  exact hu

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/ofLowerSet.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- The filter built from a non-empty lower set `S`: the neighbourhoods that contain some
`Ici a` with `a ∈ S`. -/
def ofLowerSet (S : Set Δ) (hSne : S.Nonempty) (_hS : IsLowerSet S) :
    (finalSegmentSystem Δ).Element where
  mem X := (finalSegmentSystem Δ).mem X ∧ ∃ a ∈ S, Set.Ici a ⊆ X
  sub h := h.1
  master_mem := by
    obtain ⟨a, ha⟩ := hSne
    exact ⟨⟨Set.univ_nonempty, isUpperSet_univ⟩, a, ha, Set.subset_univ _⟩
  inter_mem := by
    rintro X Y ⟨hX, a, haS, haX⟩ ⟨hY, b, hbS, hbY⟩
    have hsub : Set.Ici (max a b) ⊆ X ∩ Y :=
      Set.subset_inter
        ((Set.Ici_subset_Ici.mpr (le_max_left a b)).trans haX)
        ((Set.Ici_subset_Ici.mpr (le_max_right a b)).trans hbY)
    refine ⟨(finalSegmentSystem Δ).inter_mem hX hY (Ici_mem (max a b)) hsub, max a b, ?_, hsub⟩
    rcases max_choice a b with h | h
    · rw [h]; exact haS
    · rw [h]; exact hbS
  up_mem := by
    rintro X Y ⟨_, a, haS, haX⟩ hY hXY
    exact ⟨hY, a, haS, haX.trans hXY⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/lowerSetOf_ofLowerSet.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

omit [WellFoundedLT Δ] in
theorem lowerSetOf_ofLowerSet (S : Set Δ) (hSne : S.Nonempty) (hS : IsLowerSet S) :
    lowerSetOf (ofLowerSet S hSne hS) = S := by
  ext a
  constructor
  · rintro ⟨_, b, hbS, hba⟩
    exact hS (Set.Ici_subset_Ici.mp hba) hbS
  · intro ha
    exact ⟨Ici_mem a, a, ha, subset_rfl⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/ofLowerSet_lowerSetOf.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

theorem ofLowerSet_lowerSetOf (x : (finalSegmentSystem Δ).Element) :
    ofLowerSet (lowerSetOf x) (lowerSetOf_nonempty x) (lowerSetOf_isLowerSet x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · rintro ⟨hX, a, haS, haX⟩
    exact x.up_mem haS hX haX
  · intro hX
    obtain ⟨a, rfl⟩ := exists_Ici_of_mem (x.sub hX)
    exact ⟨x.sub hX, a, hX, subset_rfl⟩

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/finalSegmentClassify.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

/-- **Exercise 1.25 — classification of `|𝒟|`.** For a well-order `Δ`, the domain of non-empty
final segments is order-isomorphic to the poset of **non-empty initial segments** (lower sets) of
`Δ` under inclusion: `x ↦ {a ∣ Ici a ∈ x}`. (So `|𝒟|` is the lattice of cuts of `Δ`.) -/
def finalSegmentClassify :
    (finalSegmentSystem Δ).Element ≃o {S : Set Δ // S.Nonempty ∧ IsLowerSet S} where
  toFun x := ⟨lowerSetOf x, lowerSetOf_nonempty x, lowerSetOf_isLowerSet x⟩
  invFun S := ofLowerSet S.1 S.2.1 S.2.2
  left_inv x := ofLowerSet_lowerSetOf x
  right_inv S := Subtype.ext (lowerSetOf_ofLowerSet S.1 S.2.1 S.2.2)
  map_rel_iff' := by
    intro x y
    constructor
    · intro h X hX
      obtain ⟨a, rfl⟩ := exists_Ici_of_mem (x.sub hX)
      exact h hX
    · intro h a ha
      exact h _ ha

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/topElement.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem

variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]

variable [WellFoundedLT Δ]

omit [WellFoundedLT Δ]

/-- The greatest element: the filter of **all** neighbourhoods. -/
def topElement : (finalSegmentSystem Δ).Element where
  mem X := (finalSegmentSystem Δ).mem X
  sub h := h
  master_mem := ⟨Set.univ_nonempty, isUpperSet_univ⟩
  inter_mem := by
    rintro X Y hX hY
    rcases upperSet_subset_or hX.2 hY.2 with h | h
    · rw [Set.inter_eq_left.mpr h]; exact hX
    · rw [Set.inter_eq_right.mpr h]; exact hY
  up_mem := fun _ hY _ => hY

end FinalSegment

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem


variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]


variable [WellFoundedLT Δ]


omit [WellFoundedLT Δ]


theorem le_topElement (x : (finalSegmentSystem Δ).Element) : x ≤ topElement :=
  fun _ hX => x.sub hX

/-- **Exercise 1.25 — the unique total element.** The filter of all neighbourhoods is total
(`⊑`-maximal). -/
theorem topElement_isTotal : (finalSegmentSystem Δ).IsTotal (topElement (Δ := Δ)) :=
  fun y _ => le_topElement y

/-- It is the *unique* total element: any total `x` equals `topElement`. -/
theorem eq_topElement_of_isTotal {x : (finalSegmentSystem Δ).Element}
    (hx : (finalSegmentSystem Δ).IsTotal x) : x = topElement :=
  le_antisymm (le_topElement x) (hx topElement (le_topElement x))

/-- **Exercise 1.25 — not all elements are finite.** If `Δ` has *no greatest element* (e.g.
`Δ = ℕ = ω`), the total element `topElement` is not a principal filter `↑(Ici a)`: pick `b > a`,
then `Ici b ∈ topElement` but `Ici a ⊄ Ici b`. So `|𝒟|` has a non-finite (limit) element. -/
theorem topElement_not_principal_of_noMax (hnomax : ∀ a : Δ, ∃ b, a < b) (a : Δ) :
    topElement ≠ (finalSegmentSystem Δ).principal (Ici_mem a) := by
  intro h
  obtain ⟨b, hab⟩ := hnomax a
  have hmem : ((finalSegmentSystem Δ).principal (Ici_mem a)).mem (Set.Ici b) := by
    rw [← h]; exact Ici_mem b
  have hsub : Set.Ici a ⊆ Set.Ici b := hmem.2
  exact absurd (Set.Ici_subset_Ici.mp hsub) (not_le.mpr hab)
end FinalSegment
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise125.lean
namespace DomainTheory.NeighbourhoodSystems.FinalSegment

set_option linter.unusedVariables false

theorem example_125.{u_1} : And
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Δ
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1))
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    (∀ (a : Δ),
        ∃ (b : Δ),
          @LT.lt Δ
            (@Preorder.toLT Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst))))))
            a b) →
      ∀ (a : Δ),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1))
          (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
            (@Set.Ici Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst)))))
              a)
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.Ici_mem Δ inst inst_1 a))) :=
  @And.intro
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal Δ
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
      (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1))
  (∀ {Δ : Type u_1} [inst : LinearOrder Δ] [inst_1 : Nonempty Δ],
    (∀ (a : Δ),
        ∃ (b : Δ),
          @LT.lt Δ
            (@Preorder.toLT Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst))))))
            a b) →
      ∀ (a : Δ),
        @Ne
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1))
          (@DomainTheory.NeighbourhoodSystems.FinalSegment.topElement Δ inst inst_1)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal Δ
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.finalSegmentSystem Δ inst inst_1)
            (@Set.Ici Δ
              (@PartialOrder.toPreorder Δ
                (@SemilatticeInf.toPartialOrder Δ
                  (@Lattice.toSemilatticeInf Δ
                    (@DistribLattice.toLattice Δ (@instDistribLatticeOfLinearOrder Δ inst)))))
              a)
            (@DomainTheory.NeighbourhoodSystems.FinalSegment.Ici_mem Δ inst inst_1 a)))
  @DomainTheory.NeighbourhoodSystems.FinalSegment.topElement_isTotal
  @DomainTheory.NeighbourhoodSystems.FinalSegment.topElement_not_principal_of_noMax

end DomainTheory.NeighbourhoodSystems.FinalSegment
end

section
-- Exercise125/principal_Ici_le_iff.lean
namespace DomainTheory.NeighbourhoodSystems

namespace FinalSegment

open NeighborhoodSystem


variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]


/-- The principal finite elements `↑(Ici a)`; the correspondence `a ↦ ↑(Ici a)` is
order-*reversing* (`Ici a ⊆ Ici b ↔ b ≤ a`), one of Scott's "finite elements". -/
theorem principal_Ici_le_iff (a b : Δ) :
    (finalSegmentSystem Δ).principal (Ici_mem a) ≤ (finalSegmentSystem Δ).principal (Ici_mem b)
      ↔ a ≤ b := by
  rw [NeighborhoodSystem.principal_le_iff, Set.Ici_subset_Ici]

end FinalSegment
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/IFamily.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

/- concordance: source L538 EXERCISE 1.26 ideals of a ring -/
/-- **Exercise 1.26 — the basic neighbourhood `I(F)`.** `I(F) = {G ∣ F ⊆ ⟨G⟩}`, the finite sets `G`
whose generated ideal contains `F`. -/
def IFamily (F : Finset A) : Set (Finset A) := {G | (↑F : Set A) ⊆ Ideal.span (↑G : Set A)}

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/mem_IFamily.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

@[simp] theorem mem_IFamily {F G : Finset A} :
    G ∈ IFamily F ↔ (↑F : Set A) ⊆ Ideal.span (↑G : Set A) := Iff.rfl

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/IFamily_inter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- `I(F₁) ∩ I(F₂) = I(F₁ ∪ F₂)`: the system is closed under all binary intersections. -/
theorem IFamily_inter (F₁ F₂ : Finset A) :
    IFamily F₁ ∩ IFamily F₂ = IFamily (F₁ ∪ F₂) := by
  ext G
  simp only [IFamily, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.coe_union, Set.union_subset_iff]

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/IFamily_subset_iff.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

/-- Inclusion of neighbourhoods reversed to ideal generation: `I(F₁) ⊆ I(F₂) ↔ F₂ ⊆ ⟨F₁⟩`. -/
theorem IFamily_subset_iff (F₁ F₂ : Finset A) :
    IFamily F₁ ⊆ IFamily F₂ ↔ (↑F₂ : Set A) ⊆ Ideal.span (↑F₁ : Set A) := by
  constructor
  · intro h
    have hF₁ : F₁ ∈ IFamily F₁ := mem_IFamily.mpr Ideal.subset_span
    exact (h hF₁)
  · intro h G hG
    rw [mem_IFamily] at hG ⊢
    exact h.trans (SetLike.coe_subset_coe.mpr (Ideal.span_le.mpr hG))

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/ringSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- **Exercise 1.26 — the neighbourhood system of a commutative ring.** Tokens are finite subsets
`F ⊆ A`; neighbourhoods are the sets `I(F)`. The master is `I(∅)` (all of `Δ`), and intersections
`I(F₁) ∩ I(F₂) = I(F₁ ∪ F₂)` are always neighbourhoods. -/
def ringSystem : NeighborhoodSystem (Finset A) where
  mem S := ∃ F, S = IFamily F
  master := IFamily ∅
  master_nonempty := ⟨∅, by simp [IFamily]⟩
  master_mem := ⟨∅, rfl⟩
  inter_mem := by
    rintro X Y Z ⟨F₁, rfl⟩ ⟨F₂, rfl⟩ _ _
    exact ⟨F₁ ∪ F₂, IFamily_inter F₁ F₂⟩
  sub_master := by
    rintro X ⟨F, rfl⟩
    exact (IFamily_subset_iff F ∅).mpr (by rw [Finset.coe_empty]; exact Set.empty_subset _)

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/ringSystem_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

@[simp] theorem ringSystem_mem {S : Set (Finset A)} :
    (ringSystem (A := A)).mem S ↔ ∃ F, S = IFamily F := Iff.rfl

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/IFamily_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem IFamily_mem (F : Finset A) : (ringSystem (A := A)).mem (IFamily F) := ⟨F, rfl⟩

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/idealOf.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- **Exercise 1.26 — the ideal of a filter.** `idealOf x = {a ∣ I({a}) ∈ x}`. The closure
properties of an ideal come from the filter axioms: `0` from the master, `+` from `∩`-closure
(`I({a}) ∩ I({b}) = I({a,b}) ⊆ I({a+b})`), and `•` from upward closure (`I({a}) ⊆ I({c·a})`). -/
def idealOf (x : (ringSystem (A := A)).Element) : Ideal A where
  carrier := {a | x.mem (IFamily {a})}
  zero_mem' := by
    show x.mem (IFamily {(0 : A)})
    refine x.up_mem x.master_mem (IFamily_mem {(0 : A)}) ?_
    intro G _
    rw [mem_IFamily, Finset.coe_singleton, Set.singleton_subset_iff]
    exact Submodule.zero_mem _
  add_mem' := by
    intro a b ha hb
    show x.mem (IFamily {a + b})
    have h := x.inter_mem ha hb
    rw [IFamily_inter] at h
    refine x.up_mem h (IFamily_mem {a + b}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_union,
      Finset.coe_singleton, Finset.coe_singleton]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  smul_mem' := by
    intro c a ha
    show x.mem (IFamily {c • a})
    refine x.up_mem ha (IFamily_mem {c • a}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff, Finset.coe_singleton]
    exact Submodule.smul_mem _ c (Ideal.subset_span (Set.mem_singleton a))

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/mem_idealOf.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

@[simp] theorem mem_idealOf {x : (ringSystem (A := A)).Element} {a : A} :
    a ∈ idealOf x ↔ x.mem (IFamily {a}) := Iff.rfl

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/mem_IFamily_of_forall.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- A filter contains `I(F)` whenever it contains `I({a})` for every `a ∈ F` (by `∩`-closure). -/
theorem mem_IFamily_of_forall (x : (ringSystem (A := A)).Element) (F : Finset A)
    (h : ∀ a ∈ F, x.mem (IFamily {a})) : x.mem (IFamily F) := by
  classical
  induction F using Finset.induction with
  | empty => exact x.master_mem
  | @insert a F' _ ih =>
    have hins : (insert a F' : Finset A) = {a} ∪ F' := by
      ext y; simp [Finset.mem_insert]
    rw [hins, ← IFamily_inter]
    exact x.inter_mem (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/ofIdeal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- **Exercise 1.26 — the filter of an ideal.** `ofIdeal J = {I(F) ∣ ↑F ⊆ J}`. -/
def ofIdeal (J : Ideal A) : (ringSystem (A := A)).Element where
  mem S := ∃ F, S = IFamily F ∧ Ideal.span (↑F : Set A) ≤ J
  sub := by rintro S ⟨F, rfl, _⟩; exact ⟨F, rfl⟩
  master_mem := by
    refine ⟨∅, rfl, ?_⟩
    rw [Finset.coe_empty, Ideal.span_empty]
    exact bot_le
  inter_mem := by
    rintro X Y ⟨F₁, rfl, h₁⟩ ⟨F₂, rfl, h₂⟩
    refine ⟨F₁ ∪ F₂, IFamily_inter F₁ F₂, ?_⟩
    rw [Finset.coe_union, Ideal.span_union]
    exact sup_le h₁ h₂
  up_mem := by
    rintro X Y ⟨F, rfl, hF⟩ ⟨F', rfl⟩ hXY
    refine ⟨F', rfl, ?_⟩
    have hsub : (↑F' : Set A) ⊆ Ideal.span (↑F : Set A) := (IFamily_subset_iff F F').mp hXY
    exact (Ideal.span_le.mpr hsub).trans hF

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/ofIdeal_idealOf.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem ofIdeal_idealOf (x : (ringSystem (A := A)).Element) : ofIdeal (idealOf x) = x := by
  apply NeighborhoodSystem.Element.ext
  intro S
  constructor
  · rintro ⟨F, rfl, hF⟩
    refine mem_IFamily_of_forall x F (fun a ha => ?_)
    have haspan : a ∈ Ideal.span (↑F : Set A) := Ideal.subset_span (by simpa using ha)
    exact mem_idealOf.mp (hF haspan)
  · intro hS
    obtain ⟨F, rfl⟩ := x.sub hS
    refine ⟨F, rfl, ?_⟩
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, mem_idealOf]
    refine x.up_mem hS (IFamily_mem {a}) ?_
    apply (IFamily_subset_iff _ _).mpr
    rw [Finset.coe_singleton, Set.singleton_subset_iff]
    exact Ideal.subset_span ha

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/span_eq_of_IFamily_eq.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

theorem span_eq_of_IFamily_eq {F₁ F₂ : Finset A} (h : IFamily F₁ = IFamily F₂) :
    Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A) := by
  have h12 : (↑F₂ : Set A) ⊆ Ideal.span (↑F₁ : Set A) :=
    (IFamily_subset_iff F₁ F₂).mp h.le
  have h21 : (↑F₁ : Set A) ⊆ Ideal.span (↑F₂ : Set A) :=
    (IFamily_subset_iff F₂ F₁).mp h.ge
  exact le_antisymm (Ideal.span_le.mpr h21) (Ideal.span_le.mpr h12)

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/mem_ofIdeal_IFamily.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem mem_ofIdeal_IFamily (J : Ideal A) (F : Finset A) :
    (ofIdeal J).mem (IFamily F) ↔ Ideal.span (↑F : Set A) ≤ J := by
  constructor
  · rintro ⟨F', hF', hle⟩
    rw [span_eq_of_IFamily_eq hF']
    exact hle
  · intro h
    exact ⟨F, rfl, h⟩

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/idealOf_ofIdeal.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem idealOf_ofIdeal (J : Ideal A) : idealOf (ofIdeal J) = J := by
  apply SetLike.ext
  intro a
  rw [mem_idealOf, mem_ofIdeal_IFamily, Finset.coe_singleton, Ideal.span_singleton_le_iff_mem]

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/ringIso.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

/-- **Exercise 1.26 — `|𝒟| ≅ (Ideals A, ⊆)`.** The domain of the ring's neighbourhood system is
order-isomorphic to the ideals of `A` ordered by inclusion, via `x ↦ {a ∣ I({a}) ∈ x}`. -/
def ringIso : (ringSystem (A := A)).Element ≃o Ideal A where
  toFun := idealOf
  invFun := ofIdeal
  left_inv := ofIdeal_idealOf
  right_inv := idealOf_ofIdeal
  map_rel_iff' := by
    intro x y
    constructor
    · intro h S hS
      obtain ⟨F, rfl⟩ := x.sub hS
      refine mem_IFamily_of_forall y F (fun a ha => ?_)
      have hax : a ∈ idealOf x := by
        rw [mem_idealOf]
        exact x.up_mem hS (IFamily_mem {a}) <| (IFamily_subset_iff _ _).mpr <| by
          rw [Finset.coe_singleton, Set.singleton_subset_iff]
          exact Ideal.subset_span (by simpa using ha)
      exact mem_idealOf.mp (h hax)
    · intro h a ha
      exact h (IFamily {a}) ha

end Ring

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126/IFamily_eq_of_span_eq.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]


theorem IFamily_eq_of_span_eq {F₁ F₂ : Finset A}
    (h : Ideal.span (↑F₁ : Set A) = Ideal.span (↑F₂ : Set A)) : IFamily F₁ = IFamily F₂ := by
  apply Set.Subset.antisymm
  · exact (IFamily_subset_iff F₁ F₂).mpr (by rw [h]; exact Ideal.subset_span)
  · exact (IFamily_subset_iff F₂ F₁).mpr (by rw [← h]; exact Ideal.subset_span)

end Ring
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise126.lean
namespace DomainTheory.NeighbourhoodSystems.Ring

set_option linter.unusedVariables false

theorem example_126.{u_1} : ∀ {A : Type u_1} [inst : CommRing A] {F₁ F₂ : Finset A},
  @Eq (@Ideal A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))
      (@Ideal.span A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A) F₁))
      (@Ideal.span A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@SetLike.coe (Finset A) A (@Finset.instSetLike A) F₂)) →
    @Eq (Set (Finset A)) (@DomainTheory.NeighbourhoodSystems.Ring.IFamily A inst F₁)
      (@DomainTheory.NeighbourhoodSystems.Ring.IFamily A inst F₂) :=
  @DomainTheory.NeighbourhoodSystems.Ring.IFamily_eq_of_span_eq

end DomainTheory.NeighbourhoodSystems.Ring
end

section
-- Exercise127/Bounded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L546 EXERCISE 1.27 suprema of bounded sets -/
/-- **Exercise 1.27 — bounded set of elements.** `X ⊆ |𝒟|` is *bounded* iff it has an upper
bound `y ∈ |𝒟|`: `x ⊑ y` for all `x ∈ X`. -/
def Bounded (X : Set V.Element) : Prop := ∃ y : V.Element, ∀ x ∈ X, x ≤ y

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/pairSeq.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The two-term sequence `⟨U, W⟩` as a function `ℕ → Set α` (used to phrase `Consistent`). -/
def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/upperBounds.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The family of upper bounds of `X`: `{y ∣ x ⊑ y for all x ∈ X}`. -/
def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/upperBounds_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- If `X` is bounded then its upper-bound family is non-empty (it contains the witness). -/
theorem upperBounds_nonempty {X : Set V.Element} (hX : V.Bounded X) :
    (V.upperBounds X).Nonempty :=
  hX.imp fun _ hy => hy

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/sSup.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.27 — `⊔X`.** The least upper bound of a bounded `X`, defined à la Scott as the
intersection of all upper bounds: `⊔X = ⋂ {y ∣ x ⊑ y all x∈X}`. Reusing `sInf` from Exercise
1.18 on the (non-empty, because bounded) family of upper bounds. -/
def sSup (X : Set V.Element) (hX : V.Bounded X) : V.Element :=
  V.sInf (V.upperBounds X) (V.upperBounds_nonempty hX)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/bounded_iff_finite_bounded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.27 — boundedness is finitary.** `X ⊆ |𝒟|` is bounded iff every *finite* subset
of `X` is bounded. The forward direction reuses any global bound. The reverse direction is the
content: assemble `C = ⋃_{x∈X} x` (the neighbourhoods of all members of `X`); `C` is finitely
consistent because any finite sequence drawn from `C` comes from finitely many members of `X`,
which form a finite subset, hence bounded — that bound's filter contains the whole finite
sequence, so its intersection lies in `𝒟`. The least filter `leastFilter C` (Exercise 1.18) is
then an upper bound of `X`. -/
theorem bounded_iff_finite_bounded (X : Set V.Element) :
    V.Bounded X ↔ ∀ S : Set V.Element, S ⊆ X → S.Finite → V.Bounded S := by
  constructor
  · rintro ⟨y, hy⟩ S hS _
    exact ⟨y, fun x hx => hy x (hS hx)⟩
  · intro hfin
    set C : Set (Set α) := {Z | ∃ x : V.Element, x ∈ X ∧ x.mem Z} with hCdef
    have hCsub : ∀ Z ∈ C, V.mem Z := by rintro Z ⟨x, _, hxZ⟩; exact x.sub hxZ
    have hCcons : V.FinitelyConsistent C := by
      intro n seq hseqC
      choose g hgX hgmem using hseqC
      set S : Set V.Element := Set.range (fun i : Fin n => g i.1 i.2) with hSdef
      have hSfin : S.Finite := Set.finite_range _
      have hSsub : S ⊆ X := by
        rintro _ ⟨i, rfl⟩
        exact hgX i.1 i.2
      obtain ⟨y, hy⟩ := hfin S hSsub hSfin
      have hseqy : ∀ i, i < n → y.mem (seq i) := by
        intro i hi
        have hle : g i hi ≤ y := hy _ ⟨⟨i, hi⟩, rfl⟩
        exact hle (seq i) (hgmem i hi)
      have hmem : y.mem (V.interUpTo seq n) := y.mem_interUpTo seq hseqy
      exact ⟨V.interUpTo seq n, y.sub hmem, subset_rfl⟩
    refine ⟨V.leastFilter C hCsub hCcons, ?_⟩
    intro x hx Z hZ
    exact V.subset_leastFilter C hCsub hCcons ⟨x, hx, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/interUpTo_pairSeq.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


theorem interUpTo_pairSeq (U W : Set α) :
    V.interUpTo (pairSeq U W) 2 = V.master ∩ U ∩ W := by
  simp only [interUpTo_succ, interUpTo_zero, pairSeq]
  norm_num

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/consistent_pair_iff_bounded.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.27 — "boundedness is for elements what consistency is for neighbourhoods".**
For `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is consistent in `𝒟` iff `{↑U, ↑W}` is bounded in `|𝒟|`.

`→` packages the consistency witness `Z` into the principal filter `↑Z`, which lies above both
`↑U` and `↑W` (via `principal_le_iff`). `←` uses that any bound `y` contains both `U` and `W`,
hence `U ∩ W ∈ y ⊆ 𝒟`, giving `U ∩ W` as the consistency witness. -/
theorem consistent_pair_iff_bounded {U W : Set α} (hU : V.mem U) (hW : V.mem W) :
    V.Consistent (pairSeq U W) 2 ↔ V.Bounded {V.principal hU, V.principal hW} := by
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩
    rw [V.interUpTo_pairSeq] at hZsub
    have hZU : Z ⊆ U := hZsub.trans (Set.inter_subset_left.trans Set.inter_subset_right)
    have hZW : Z ⊆ W := hZsub.trans Set.inter_subset_right
    refine ⟨V.principal hZmem, ?_⟩
    intro x hx
    rcases hx with rfl | rfl
    · exact (V.principal_le_iff hU hZmem).mpr hZU
    · exact (V.principal_le_iff hW hZmem).mpr hZW
  · rintro ⟨y, hy⟩
    have hyU : y.mem U :=
      hy _ (Or.inl rfl) U ⟨hU, subset_rfl⟩
    have hyW : y.mem W :=
      hy _ (Or.inr rfl) W ⟨hW, subset_rfl⟩
    have hyUW : y.mem (U ∩ W) := y.inter_mem hyU hyW
    refine ⟨U ∩ W, y.sub hyUW, ?_⟩
    rw [V.interUpTo_pairSeq]
    intro z hz
    exact ⟨⟨V.sub_master hU hz.1, hz.1⟩, hz.2⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/le_sSup.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.27 — `⊔X` is an upper bound.** Each `x ∈ X` satisfies `x ⊑ ⊔X`. -/
theorem le_sSup (X : Set V.Element) (hX : V.Bounded X) {x : V.Element} (hx : x ∈ X) :
    x ≤ V.sSup X hX :=
  V.le_sInf (V.upperBounds X) (V.upperBounds_nonempty hX) x (fun _ hy => hy x hx)

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127/sSup_le.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.27 — `⊔X` is least.** Any upper bound `z` of `X` satisfies `⊔X ⊑ z`. -/
theorem sSup_le (X : Set V.Element) (hX : V.Bounded X) {z : V.Element}
    (hz : ∀ x ∈ X, x ≤ z) : V.sSup X hX ≤ z :=
  V.sInf_le (V.upperBounds X) (V.upperBounds_nonempty hX) hz

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise127.lean
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_127.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
          @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
            x z) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX) z) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
    (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
    {z : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
    (∀ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
        @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
            (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
          @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
            x z) →
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX) z)
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW))))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
      (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
      {x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V},
      @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
          (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) X x →
        @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
          x (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup α V X hX))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
        (X : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
        Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V X)
          (∀ (S : Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)),
            @LE.le (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)) S X →
              @Set.Finite (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) S →
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V S))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {U W : Set α}
        (hU : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V U)
        (hW : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V W),
        Iff
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.pairSeq α U W)
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Bounded α V
            (@Insert.insert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
              (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Set.instInsert (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V U hU)
              (@Singleton.singleton (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instSingletonSet (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V W hW)))))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bounded_iff_finite_bounded
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_pair_iff_bounded)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.le_sSup)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.sSup_le

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end

section
-- Theorem110/bracket.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Scott's `[X] = {x ∈ |𝒟| ∣ X ∈ x}`: the elements of `|𝒟|` that contain the neighbourhood `X`.
(This is the `basicOpen X` of Exercise 1.22, repeated here to avoid the topology dependency.) -/
def bracket (X : Set α) : Set V.Element := {x | x.mem X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/mem_bracket.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_bracket {X : Set α} {x : V.Element} : x ∈ V.bracket X ↔ x.mem X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/bracket_master.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem bracket_master : V.bracket V.master = Set.univ := by
  ext x; simp only [mem_bracket, Set.mem_univ, iff_true]; exact x.master_mem

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/bracket_inter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.10 (3).** `[X] ∩ [Y] = [X ∩ Y]` for `X, Y ∈ 𝒟`. (`⊆` is filter closure under `∩`;
`⊇` is upward closure along `X ∩ Y ⊆ X`, `X ∩ Y ⊆ Y`.) -/
theorem bracket_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ∩ V.bracket Y = V.bracket (X ∩ Y) := by
  ext x
  simp only [Set.mem_inter_iff, mem_bracket]
  constructor
  · rintro ⟨hx, hy⟩
    exact x.inter_mem hx hy
  · intro hxy
    exact ⟨x.up_mem hxy hX Set.inter_subset_left, x.up_mem hxy hY Set.inter_subset_right⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/principal_mem_bracket.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.10 (4).** `↑X ∈ [X]`: the principal filter of `X` contains `X`. -/
theorem principal_mem_bracket {X : Set α} (hX : V.mem X) : V.principal hX ∈ V.bracket X :=
  ⟨hX, subset_rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/bracket_subset_iff.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **The correspondence `X ↦ [X]` is inclusion-preserving.** `[X] ⊆ [Y] ↔ X ⊆ Y` (for `X,Y ∈ 𝒟`).
`→` tests at `↑X ∈ [X]`, reading `X ⊆ Y` off `↑X ∈ [Y]`; `←` is upward closure. -/
theorem bracket_subset_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.bracket X ⊆ V.bracket Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h (V.principal_mem_bracket hX)).2
  · intro hXY x hx
    exact x.up_mem hx hY hXY

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/bracket_injective.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **The correspondence `X ↦ [X]` is one-one.** `[X] = [Y] ⟹ X = Y` (for `X,Y ∈ 𝒟`). -/
theorem bracket_injective {X Y : Set α} (hX : V.mem X) (hY : V.mem Y)
    (h : V.bracket X = V.bracket Y) : X = Y :=
  Set.Subset.antisymm ((V.bracket_subset_iff hX hY).mp h.subset)
    ((V.bracket_subset_iff hY hX).mp h.superset)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/tokenSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L334 THEOREM 1.10 basic open neighbourhoods -/
/-- **Theorem 1.10.** The *element-token system* `{[X] ∣ X ∈ 𝒟}` over the tokens `|𝒟|`. The two
laws reduce to facts about `[·]`: the master `[Δ] = |𝒟|` is the whole space; the consistency
witness `[W]` for `[X] ∩ [Y]` yields `W ⊆ X ∩ Y` (via `↑W`), so `X ∩ Y ∈ 𝒟` and
`[X] ∩ [Y] = [X ∩ Y]`. -/
def tokenSystem : NeighborhoodSystem V.Element where
  mem S := ∃ X, V.mem X ∧ S = V.bracket X
  master := Set.univ
  master_nonempty := ⟨V.bot, Set.mem_univ _⟩
  master_mem := ⟨V.master, V.master_mem, V.bracket_master.symm⟩
  inter_mem := by
    rintro S T W ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩ ⟨Z, hZ, rfl⟩ hWsub
    have hpz := hWsub (V.principal_mem_bracket hZ)
    obtain ⟨hzX, hzY⟩ := hpz
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hZ (Set.subset_inter hzX.2 hzY.2)
    exact ⟨X ∩ Y, hXY, V.bracket_inter hX hY⟩
  sub_master := fun _ => Set.subset_univ _

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/tokenSystem_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem tokenSystem_mem {S : Set V.Element} :
    V.tokenSystem.mem S ↔ ∃ X, V.mem X ∧ S = V.bracket X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/ofToken.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The element of `|𝒟|` corresponding to `y ∈ |{[X]}|`: the filter `{X ∣ [X] ∈ y}`. -/
def ofToken (y : V.tokenSystem.Element) : V.Element where
  mem X := V.mem X ∧ y.mem (V.bracket X)
  sub h := h.1
  master_mem := ⟨V.master_mem, by rw [V.bracket_master]; exact y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨hX, hyX⟩ ⟨hY, hyY⟩
    have hyInter : y.mem (V.bracket X ∩ V.bracket Y) := y.inter_mem hyX hyY
    obtain ⟨W, hW, hWeq⟩ := y.sub hyInter
    have hpw := V.principal_mem_bracket hW
    rw [← hWeq] at hpw
    obtain ⟨hwX, hwY⟩ := hpw
    have hXY : V.mem (X ∩ Y) := V.inter_mem hX hY hW (Set.subset_inter hwX.2 hwY.2)
    refine ⟨hXY, ?_⟩
    rw [← V.bracket_inter hX hY]
    exact hyInter
  up_mem := by
    rintro X Y ⟨hX, hyX⟩ hY hXY
    exact ⟨hY, y.up_mem hyX ⟨Y, hY, rfl⟩ ((V.bracket_subset_iff hX hY).mpr hXY)⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/toToken.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The element of `|{[X]}|` corresponding to `x ∈ |𝒟|`: the filter `{[X] ∣ X ∈ x}`. -/
def toToken (x : V.Element) : V.tokenSystem.Element where
  mem S := ∃ X, x.mem X ∧ S = V.bracket X
  sub := by rintro S ⟨X, hX, rfl⟩; exact ⟨X, x.sub hX, rfl⟩
  master_mem := ⟨V.master, x.master_mem, V.bracket_master.symm⟩
  inter_mem := by
    rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    exact ⟨X ∩ Y, x.inter_mem hX hY, V.bracket_inter (x.sub hX) (x.sub hY)⟩
  up_mem := by
    rintro S T ⟨X, hX, rfl⟩ hT hsub
    obtain ⟨Y, hYmem, rfl⟩ := hT
    exact ⟨Y, x.up_mem hX hYmem ((V.bracket_subset_iff (x.sub hX) hYmem).mp hsub), rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/tokenIso.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.10 (the isomorphism).** `X ↦ [X]` induces an order-isomorphism `|𝒟| ≃o |{[X]}|`:
`toToken` and `ofToken` are mutually inverse and preserve/reflect `⊑`. -/
def tokenIso : V.Element ≃o V.tokenSystem.Element where
  toFun := V.toToken
  invFun := V.ofToken
  left_inv := by
    intro x
    apply Element.ext
    intro X
    constructor
    · rintro ⟨hX, X', hX', heq⟩
      rw [V.bracket_injective hX (x.sub hX') heq]; exact hX'
    · intro hx
      exact ⟨x.sub hx, X, hx, rfl⟩
  right_inv := by
    intro y
    apply Element.ext
    intro S
    constructor
    · rintro ⟨X, ⟨_, hyX⟩, rfl⟩
      exact hyX
    · intro hyS
      obtain ⟨X, hX, rfl⟩ := y.sub hyS
      exact ⟨X, ⟨hX, hyS⟩, rfl⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h X hx
      have hmem : (V.toToken x).mem (V.bracket X) := ⟨X, hx, rfl⟩
      obtain ⟨X', hX', heq⟩ := h (V.bracket X) hmem
      rw [V.bracket_injective (x.sub hx) (x'.sub hX') heq]; exact hX'
    · intro h S hS
      obtain ⟨X, hX, rfl⟩ := hS
      exact ⟨X, h X hX, rfl⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/bracket_inter_nonempty_iff.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Theorem 1.10 (2).** `X, Y` are consistent in `𝒟` (have a common lower bound `Z ∈ 𝒟`,
`Z ⊆ X ∩ Y`) iff `[X] ∩ [Y] ≠ ∅`. `→` uses `↑Z` (which lies in both `[X]` and `[Y]`); `←` reads a
witness off any common element. -/
theorem bracket_inter_nonempty_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    (V.bracket X ∩ V.bracket Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  constructor
  · rintro ⟨x, hxX, hxY⟩
    exact ⟨X ∩ Y, x.sub (x.inter_mem hxX hxY), subset_rfl⟩
  · rintro ⟨Z, hZ, hZsub⟩
    refine ⟨V.principal hZ, ?_, ?_⟩
    · exact ⟨hX, hZsub.trans Set.inter_subset_left⟩
    · exact ⟨hY, hZsub.trans Set.inter_subset_right⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110/isomorphic_tokenSystem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Theorem 1.10 (statement).** Any neighbourhood system is isomorphic to its element-token
system: `𝒟 ≅ᴰ {[X]}`. -/
theorem isomorphic_tokenSystem : V ≅ᴰ V.tokenSystem := ⟨V.tokenIso⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem110.lean
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem theorem_110.{u_1} : And
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX)) :=
  @And.intro
  (And
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X : Set α}
    (hX : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X),
    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal α V X hX))
  (@And.intro
    (And
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y))))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.Isomorphic α
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) V
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
    (@And.intro
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            Iff
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y)))
              (∃ (Z : Set α),
                And (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Z)
                  (@LE.le (Set α) (@Set.instLE α) Z (@Inter.inter (Set α) (@Set.instInter α) X Y))))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) {X Y : Set α},
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V Y →
            @Eq (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
              (@Inter.inter (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@Set.instInter (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V X)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V Y))
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                (@Inter.inter (Set α) (@Set.instInter α) X Y)))
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket_inter_nonempty_iff
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket_inter)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.isomorphic_tokenSystem)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.principal_mem_bracket

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end

section
-- Exercise121/IsComplete.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- A neighbourhood system `𝒟'` over `β` is **complete** when every filter `y ∈ |𝒟'|` is *fixed
by a unique point* `b ∈ β`: a neighbourhood `S` lies in `y` iff `b ∈ S`. (Scott: "*a filter is
fixed by a point iff it is the filter of all neighbourhoods containing that point*".) -/
def IsComplete {β : Type*} (V' : NeighborhoodSystem β) : Prop :=
  ∀ y : V'.Element, ∃! b : β, ∀ S, V'.mem S → (y.mem S ↔ b ∈ S)

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/filterFixedBy.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The filter of `{[X]}` *fixed by* the point `x ∈ |𝒟|` is `toToken x` (the filter of all
brackets containing `x`). By Theorem 1.10 this is a bijection `|𝒟| ≃ |{[X]}|`, so tokens and
(partial) elements are identified. -/
def filterFixedBy (x : V.Element) : V.tokenSystem.Element := V.toToken x

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/bracket_nonempty_iff.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `[X] ≠ ∅ ⟺ X ∈ 𝒟`. `→` reads `X ∈ 𝒟` off any element of `[X]`; `←` exhibits `↑X`. -/
theorem bracket_nonempty_iff {X : Set α} : (V.bracket X).Nonempty ↔ V.mem X := by
  constructor
  · rintro ⟨x, hx⟩; exact x.sub hx
  · intro hX; exact ⟨V.principal hX, V.principal_mem_bracket hX⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/consistent_iff_bracket_interUpTo_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/- concordance: source L486 EXERCISE 1.21 complete neighbourhood systems -/
/-- **Exercise 1.21 — consistency via the intersection `[⋂]`.** For `X₀, …, Xₙ₋₁ ∈ 𝒟`,
`⟨Xᵢ⟩` is consistent iff `[⋂_{i<n} Xᵢ] ≠ ∅`. Combines Theorem 1.1c
(`consistent_iff_interUpTo_mem`) with `bracket_nonempty_iff`. -/
theorem consistent_iff_bracket_interUpTo_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ (V.bracket (V.interUpTo X n)).Nonempty := by
  rw [V.consistent_iff_interUpTo_mem X hX]
  exact V.bracket_nonempty_iff.symm

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/consistent_iff_iInter_bracket_nonempty.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.21 — consistency `⟺ ⋂_{i<n} [Xᵢ] ≠ ∅`.** The literal form of Scott's
equivalence: `⟨Xᵢ⟩` is consistent iff there is a filter lying in every `[Xᵢ]` (`i < n`). `→`
uses upward closure along `⋂_{i<n} Xᵢ ⊆ Xᵢ`; `←` uses `Element.mem_interUpTo`. -/
theorem consistent_iff_iInter_bracket_nonempty (X : ℕ → Set α) {n : ℕ}
    (hX : ∀ i, i < n → V.mem (X i)) :
    V.Consistent X n ↔ ∃ x : V.Element, ∀ i, i < n → x ∈ V.bracket (X i) := by
  rw [V.consistent_iff_bracket_interUpTo_nonempty X hX]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i hi => x.up_mem hx (hX i hi) (V.interUpTo_subset X hi)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, x.mem_interUpTo X (fun i hi => hx i hi)⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/tokenSystem_complete.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.21 — the token system is complete.** Every filter `y` of `{[X]}` is fixed by
the unique point `ofToken y ∈ |𝒟|`: `[W] ∈ y ↔ ofToken y ∈ [W]`. Uniqueness is `Element.ext`
applied through the brackets. -/
theorem tokenSystem_complete : V.tokenSystem.IsComplete := by
  intro y
  refine ⟨V.ofToken y, ?_, ?_⟩
  · rintro S ⟨W, hW, rfl⟩
    constructor
    · intro hyW; exact ⟨hW, hyW⟩
    · rintro ⟨_, hyW⟩; exact hyW
  · intro b hb
    apply Element.ext
    intro W
    by_cases hW : V.mem W
    · have hb' := hb (V.bracket W) ⟨W, hW, rfl⟩
      constructor
      · intro hbW; exact ⟨hW, hb'.mpr hbW⟩
      · intro hxW; exact hb'.mp hxW.2
    · constructor
      · intro hbW; exact absurd (b.sub hbW) hW
      · intro hxW; exact absurd ((V.ofToken y).sub hxW) hW

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/tokenSystem_isPositive.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.21 — the token system is positive.** `[X] ∩ [Y] = [X ∩ Y]` is a neighbourhood
iff non-empty: a common element `x` gives `X ∩ Y ∈ 𝒟` (via `x.sub (x.inter_mem …)`); conversely
`[W]` always contains the principal filter `↑W`. -/
theorem tokenSystem_isPositive : V.tokenSystem.IsPositive := by
  rintro S T ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
  rw [V.bracket_inter hX hY]
  constructor
  · rintro ⟨W, hW, hWeq⟩
    rw [hWeq]
    exact ⟨V.principal hW, V.principal_mem_bracket hW⟩
  · rintro ⟨x, hx⟩
    exact ⟨X ∩ Y, x.sub hx, rfl⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121/tokenSystem_toToken_bijective.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- **Exercise 1.21 — tokens ↔ elements.** `toToken : |𝒟| → |{[X]}|` is a bijection (it is the
underlying map of the order-iso `tokenIso`), so a complete system identifies tokens with
(partial) elements under a one-one correspondence. -/
theorem tokenSystem_toToken_bijective : Function.Bijective V.toToken :=
  V.tokenIso.bijective

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise121.lean
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem example_121.{u_1} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Function.Bijective (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toToken α V)) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
  (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
    @Function.Bijective (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.toToken α V))
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V)))
    (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsPositive
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
    (@And.intro
      (And
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x)))
      (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsComplete
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem α V))
      (@And.intro
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.interUpTo α V X n))))
        (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (X : Nat → Set α) {n : Nat},
          (∀ (i : Nat),
              @LT.lt Nat instLTNat i n → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (X i)) →
            Iff (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V X n)
              (∃ (x : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
                ∀ (i : Nat),
                  @LT.lt Nat instLTNat i n →
                    @Membership.mem (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
                      (Set (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@Set.instMembership (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V))
                      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.bracket α V (X i)) x))
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_iff_bracket_interUpTo_nonempty
        @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.consistent_iff_iInter_bracket_nonempty)
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem_complete)
    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem_isPositive)
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.tokenSystem_toToken_bijective

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end

section
-- Theorem111/iInter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/- concordance: source L372 THEOREM 1.11 intersections and directed unions -/
/-- **Theorem 1.11 (i).** The intersection `⋂ₙ xₙ = {X ∣ ∀ n, X ∈ xₙ}` of a sequence of elements is
again an element of `|𝒟|`. (No proviso: all of 1.6(i)–(iii) are pointwise.) -/
def iInter (x : ℕ → V.Element) : V.Element where
  mem X := ∀ n, (x n).mem X
  sub h := (x 0).sub (h 0)
  master_mem n := (x n).master_mem
  inter_mem h1 h2 n := (x n).inter_mem (h1 n) (h2 n)
  up_mem h hY hXY n := (x n).up_mem (h n) hY hXY

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111/mem_iInter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem mem_iInter (x : ℕ → V.Element) {X : Set α} :
    (V.iInter x).mem X ↔ ∀ n, (x n).mem X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111/iUnion.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.11 (ii).** For an **ascending** sequence `x₀ ⊑ x₁ ⊑ ⋯`, the union
`⋃ₙ xₙ = {X ∣ ∃ n, X ∈ xₙ}` is again an element of `|𝒟|`. The proviso (`Monotone x`) is used only in
the intersection law: `X ∈ xₙ`, `Y ∈ xₘ` ⟹ both in `x_{max n m}`. -/
def iUnion (x : ℕ → V.Element) (hmono : Monotone x) : V.Element where
  mem X := ∃ n, (x n).mem X
  sub := by rintro X ⟨n, hn⟩; exact (x n).sub hn
  master_mem := ⟨0, (x 0).master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, (x (max n m)).inter_mem ?_ ?_⟩
    · exact hmono (le_max_left n m) X hn
    · exact hmono (le_max_right n m) Y hm
  up_mem := by
    rintro X Y ⟨n, hn⟩ hY hXY
    exact ⟨n, (x n).up_mem hn hY hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111/Basic.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


@[simp] theorem mem_iUnion (x : ℕ → V.Element) (hmono : Monotone x) {X : Set α} :
    (V.iUnion x hmono).mem X ↔ ∃ n, (x n).mem X := Iff.rfl
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111/iInter_le.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `⋂ₙ xₙ ⊑ xₙ`: the intersection approximates every member of the sequence. -/
theorem iInter_le (x : ℕ → V.Element) (n : ℕ) : V.iInter x ≤ x n :=
  fun _ h => h n

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111/iUnion_le.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `⋃ₙ xₙ` is the **least** upper bound: anything approximated by all `xₙ` approximates the
union from above. -/
theorem iUnion_le (x : ℕ → V.Element) (hmono : Monotone x) (y : V.Element)
    (h : ∀ n, x n ≤ y) : V.iUnion x hmono ≤ y := by
  rintro X ⟨n, hn⟩
  exact h n X hn

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111.lean
namespace DomainTheory.NeighbourhoodSystems.NeighborhoodSystem

set_option linter.unusedVariables false

theorem theorem_111.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (x : Nat → @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
  (hmono :
    @Monotone Nat (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V) Nat.instPreorder
      (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V))
      x)
  (y : @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V),
  (∀ (n : Nat),
      @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
        (x n) y) →
    @LE.le (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
      (@Preorder.toLE (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
        (@PartialOrder.toPreorder (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.instPartialOrderElement α V)))
      (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.iUnion α V x hmono) y :=
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.iUnion_le

end DomainTheory.NeighbourhoodSystems.NeighborhoodSystem
end

section
-- Exercise113/prefixSeq.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The length-`n` initial segment `p ↾ n = ⟨p 0, …, p (n-1)⟩` of an infinite path `p`. -/
def prefixSeq (p : ℕ → Bool) : ℕ → Str
  | 0 => []
  | (n + 1) => prefixSeq p n ++ [p n]

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/prefixSeq_length.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

@[simp] theorem prefixSeq_length (p : ℕ → Bool) (n : ℕ) : (prefixSeq p n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [prefixSeq, ih]

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/branchSeq.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- The finite approximations `σₙ⊥ = (p ↾ n)⊥` along the path `p`. -/
def branchSeq (p : ℕ → Bool) (n : ℕ) : B.Element := sigmaBot (prefixSeq p n)

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/prefixSeq_prefix_succ.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem prefixSeq_prefix_succ (p : ℕ → Bool) (n : ℕ) :
    prefixSeq p n <+: prefixSeq p (n + 1) := ⟨[p n], rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/prefixSeq_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem prefixSeq_mono (p : ℕ → Bool) {n m : ℕ} (h : n ≤ m) :
    prefixSeq p n <+: prefixSeq p m := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ k _ ih => exact ih.trans (prefixSeq_prefix_succ p k)

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/branchSeq_mono.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

theorem branchSeq_mono (p : ℕ → Bool) : Monotone (branchSeq p) := by
  intro n m h
  exact (sigmaBot_le_iff (prefixSeq p n) (prefixSeq p m)).mpr (prefixSeq_mono p h)

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/branch.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The limit/total element of an infinite path** `p`: the ascending union `⋃ₙ (p ↾ n)⊥`
(Theorem 1.11(ii)). These are the "limit nodes all along the top" of Scott's picture. -/
def branch (p : ℕ → Bool) : B.Element := B.iUnion (branchSeq p) (branchSeq_mono p)

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/branch_mem_iff.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- `cone σ ∈ branch p` iff `σ` is an initial segment of some `p ↾ n`, i.e. `σ` lies on the path. -/
theorem branch_mem_iff (p : ℕ → Bool) {σ : Str} :
    (branch p).mem (cone σ) ↔ ∃ n, σ <+: prefixSeq p n := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mp h
    exact ⟨n, cone_subset_cone.mp hn.2⟩
  · rintro ⟨n, hn⟩
    exact (B.mem_iUnion (branchSeq p) (branchSeq_mono p)).mpr
      ⟨n, memB_cone σ, cone_subset_cone.mpr hn⟩

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/prefix_comparable_of_mem.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Two neighbourhoods present in a common element of `|B|` have comparable generating prefixes
(their cones cannot be disjoint, since the intersection is a nonempty cone). -/
theorem prefix_comparable_of_mem {σ τ : Str} (y : B.Element)
    (hσ : y.mem (cone σ)) (hτ : y.mem (cone τ)) : σ <+: τ ∨ τ <+: σ := by
  have hi : y.mem (cone σ ∩ cone τ) := y.inter_mem hσ hτ
  obtain ⟨ρ, hρ⟩ := y.sub hi
  rcases cone_trichotomy σ τ with h | h | h
  · exact Or.inr (cone_subset_cone.mp h)
  · exact Or.inl (cone_subset_cone.mp h)
  · exfalso
    have hmem : ρ ∈ cone ρ := mem_cone.mpr List.prefix_rfl
    rw [← hρ, h] at hmem
    simp at hmem

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113/branch_isTotal.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/- concordance: source L454 EXERCISE 1.13 infinite binary tree -/
/-- **Exercise 1.13 (total elements).** Each infinite path `p` gives a *total* (maximal) element
`branch p`: any `y` it approximates approximates it back. (These maximal elements are exactly the
limit nodes along the top of the binary-tree picture.) -/
theorem branch_isTotal (p : ℕ → Bool) : B.IsTotal (branch p) := by
  intro y hy X hX
  obtain ⟨σ, rfl⟩ := y.sub hX
  have hk : y.mem (cone (prefixSeq p σ.length)) :=
    hy _ ((branch_mem_iff p).mpr ⟨σ.length, List.prefix_rfl⟩)
  rcases prefix_comparable_of_mem y hX hk with h | h
  · exact (branch_mem_iff p).mpr ⟨σ.length, h⟩
  · have hlen : (prefixSeq p σ.length).length = σ.length := prefixSeq_length p σ.length
    have hσ : prefixSeq p σ.length = σ := h.eq_of_length hlen
    exact (branch_mem_iff p).mpr ⟨σ.length, by rw [hσ]⟩

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Exercise113.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

set_option linter.unusedVariables false

theorem example_113 : ∀ (p : Nat → Bool),
  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsTotal DomainTheory.NeighbourhoodSystems.ExampleB.Str
    DomainTheory.NeighbourhoodSystems.ExampleB.B (DomainTheory.NeighbourhoodSystems.Exercise113.branch p) :=
  DomainTheory.NeighbourhoodSystems.Exercise113.branch_isTotal

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- Theorem111/le_iInter.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `⋂ₙ xₙ` is the **greatest** lower bound: anything approximating all `xₙ` approximates `⋂ₙ xₙ`. -/
theorem le_iInter (x : ℕ → V.Element) (y : V.Element) (h : ∀ n, y ≤ x n) :
    y ≤ V.iInter x :=
  fun X hX n => h n X hX

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Theorem111/le_iUnion.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


/-- `xₙ ⊑ ⋃ₙ xₙ`: every member of the sequence approximates the union. -/
theorem le_iUnion (x : ℕ → V.Element) (hmono : Monotone x) (n : ℕ) :
    x n ≤ V.iUnion x hmono :=
  fun _ hX => ⟨n, hX⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise113/branchSeq_le_branch.lean
namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB


/-- Every finite approximation `(p ↾ n)⊥` approximates the limit element `branch p`. -/
theorem branchSeq_le_branch (p : ℕ → Bool) (n : ℕ) : branchSeq p n ≤ branch p :=
  B.le_iUnion (branchSeq p) (branchSeq_mono p) n

end DomainTheory.NeighbourhoodSystems.Exercise113
end

section
-- interUpTo_antitone.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The finite intersection is antitone in its length: a longer prefix is contained in a shorter
one. -/
theorem interUpTo_antitone (X : ℕ → Set α) {j k : ℕ} (h : j ≤ k) :
    V.interUpTo X k ⊆ V.interUpTo X j := by
  induction k with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [h']
    · exact Set.inter_subset_left.trans (ih (Nat.lt_succ_iff.mp h'))

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
end

section
-- state.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- Greedy *state*: `state n = (Yₙ, ⋂_{i≤n} Yᵢ)`. The running intersection in the second
component lets the consistency test `V.mem (acc ∩ enum (n+1))` be self-contained (Theorem 1.1c:
the prefix `Y₀,…,Yₙ,enum (n+1)` is consistent iff this intersection is a neighbourhood). -/
def state : ℕ → Set α × Set α
  | 0 => (enum 0, V.master ∩ enum 0)
  | (n + 1) =>
      if V.mem ((state n).2 ∩ enum (n + 1)) then
        (enum (n + 1), (state n).2 ∩ enum (n + 1))
      else
        state n

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- Y.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The greedy sequence `Yₙ = (state n).1`. -/
def Y (n : ℕ) : Set α := (state V enum n).1

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- Y_zero.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

@[simp] theorem Y_zero : Y V enum 0 = enum 0 := rfl

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- acc.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The running intersection `acc n = ⋂_{i≤n} Yᵢ = (state n).2`. -/
def acc (n : ℕ) : Set α := (state V enum n).2

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- acc_zero.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

@[simp] theorem acc_zero : acc V enum 0 = V.master ∩ enum 0 := rfl

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- cond.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The consistency test at stage `n+1`: is `enum (n+1)` consistent with the prefix `Y₀,…,Yₙ`?
An `abbrev` so the `[DecidablePred V.mem]` instance is found through it. -/
abbrev cond (n : ℕ) : Prop := V.mem (acc V enum n ∩ enum (n + 1))

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- state_succ.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The defining equation of `state` at a successor, written with the named `cond`/`acc`. -/
theorem state_succ (n : ℕ) :
    state V enum (n + 1) =
      if cond V enum n then (enum (n + 1), acc V enum n ∩ enum (n + 1)) else state V enum n :=
  rfl

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- Y_succ_neg.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

theorem Y_succ_neg {n : ℕ} (h : ¬ cond V enum n) : Y V enum (n + 1) = Y V enum n := by
  show (state V enum (n + 1)).1 = (state V enum n).1
  rw [state_succ, ite_eq_right h]

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- Y_succ_pos.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

theorem Y_succ_pos {n : ℕ} (h : cond V enum n) : Y V enum (n + 1) = enum (n + 1) := by
  show (state V enum (n + 1)).1 = enum (n + 1)
  rw [state_succ, ite_eq_left h]

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- acc_succ_neg.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

theorem acc_succ_neg {n : ℕ} (h : ¬ cond V enum n) :
    acc V enum (n + 1) = acc V enum n := by
  show (state V enum (n + 1)).2 = (state V enum n).2
  rw [state_succ, ite_eq_right h]

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- acc_succ_pos.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

theorem acc_succ_pos {n : ℕ} (h : cond V enum n) :
    acc V enum (n + 1) = acc V enum n ∩ enum (n + 1) := by
  show (state V enum (n + 1)).2 = acc V enum n ∩ enum (n + 1)
  rw [state_succ, ite_eq_left h]

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- acc_eq_interUpTo.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- `acc n = ⋂_{i<n+1} Yᵢ`: the carried intersection is exactly the prefix intersection. -/
theorem acc_eq_interUpTo : ∀ n, acc V enum n = V.interUpTo (Y V enum) (n + 1) := by
  intro n
  induction n with
  | zero =>
    rw [acc_zero, interUpTo_succ, interUpTo_zero, Y_zero]
  | succ n ih =>
    rw [interUpTo_succ, ← ih]
    by_cases h : cond V enum n
    · rw [acc_succ_pos V enum h, Y_succ_pos V enum h]
    · rw [acc_succ_neg V enum h, Y_succ_neg V enum h]
      have hsub : acc V enum n ⊆ Y V enum n := by
        rw [ih]; exact V.interUpTo_subset (Y V enum) (Nat.lt_succ_self n)
      rw [Set.inter_eq_left.mpr hsub]

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- acc_mem.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

variable (henum : ∀ n, V.mem (enum n))

include henum

/-- The running intersection `acc n` is always a neighbourhood — the greedy choice guarantees it.
This is the content of Scott's hint (consistency of the prefix). -/
theorem acc_mem : ∀ n, V.mem (acc V enum n) := by
  intro n
  induction n with
  | zero =>
    rw [acc_zero, Set.inter_eq_right.mpr (V.sub_master (henum 0))]
    exact henum 0
  | succ n ih =>
    by_cases h : cond V enum n
    · rw [acc_succ_pos V enum h]; exact h
    · rw [acc_succ_neg V enum h]; exact ih

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- mem_interUpTo_Y.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

variable (henum : ∀ n, V.mem (enum n))

include henum

/-- `⋂_{i<n} Yᵢ` is always a neighbourhood. -/
theorem mem_interUpTo_Y : ∀ n, V.mem (V.interUpTo (Y V enum) n) := by
  intro n
  cases n with
  | zero => rw [interUpTo_zero]; exact V.master_mem
  | succ n => rw [← acc_eq_interUpTo V enum]; exact acc_mem V enum henum n

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- greedyElement.lean
namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

variable (henum : ∀ n, V.mem (enum n))

include henum

/- concordance: source L514 EXERCISE 1.23 decidable total elements -/
/-- **Exercise 1.23 — the greedy element.** The filter generated by all `Yₙ`:
`{X ∈ 𝒟 ∣ ⋂_{i<n} Yᵢ ⊆ X for some n}`. The prefix intersections `⋂_{i<n} Yᵢ` are a descending
chain of neighbourhoods, so this is a genuine filter. -/
def greedyElement : V.Element where
  mem X := V.mem X ∧ ∃ n, V.interUpTo (Y V enum) n ⊆ X
  sub h := h.1
  master_mem := ⟨V.master_mem, 0, by rw [interUpTo_zero]⟩
  inter_mem := by
    rintro X X' ⟨hX, n, hn⟩ ⟨hX', m, hm⟩
    have hsub : V.interUpTo (Y V enum) (max n m) ⊆ X ∩ X' :=
      Set.subset_inter
        ((V.interUpTo_antitone (Y V enum) (le_max_left n m)).trans hn)
        ((V.interUpTo_antitone (Y V enum) (le_max_right n m)).trans hm)
    exact ⟨V.inter_mem hX hX' (mem_interUpTo_Y V enum henum (max n m)) hsub, max n m, hsub⟩
  up_mem := by
    rintro X X' ⟨_, n, hn⟩ hX' hsub
    exact ⟨hX', n, hn.trans hsub⟩

end Exercise123

end DomainTheory.NeighbourhoodSystems
end

section
-- Exercise123.lean
namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)


end NeighborhoodSystem

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]


variable (henum : ∀ n, V.mem (enum n))
include henum

/-- Each `Yₙ` is a neighbourhood. -/
theorem Y_mem : ∀ n, V.mem (Y V enum n) := by
  intro n
  induction n with
  | zero => rw [Y_zero]; exact henum 0
  | succ n ih =>
    by_cases h : cond V enum n
    · rw [Y_succ_pos V enum h]; exact henum (n + 1)
    · rw [Y_succ_neg V enum h]; exact ih


/-- **Exercise 1.23 — the hint.** For every `n`, the prefix `Y₀, …, Y_{n-1}` is consistent in
`𝒟`: its finite intersection is a neighbourhood, so it is its own common lower bound. -/
theorem Y_prefix_consistent (n : ℕ) : V.Consistent (Y V enum) n :=
  ⟨V.interUpTo (Y V enum) n, mem_interUpTo_Y V enum henum n, subset_rfl⟩


/-- Every `Yₙ` belongs to the greedy element. -/
theorem greedyElement_mem_Y (n : ℕ) : (greedyElement V enum henum).mem (Y V enum n) :=
  ⟨Y_mem V enum henum n, n + 1, V.interUpTo_subset (Y V enum) (Nat.lt_succ_self n)⟩

/-- The running intersection `acc n` belongs to the greedy element. -/
theorem greedyElement_mem_acc (n : ℕ) : (greedyElement V enum henum).mem (acc V enum n) := by
  refine ⟨acc_mem V enum henum n, n + 1, ?_⟩
  rw [acc_eq_interUpTo V enum]

variable (hsurj : ∀ {X : Set α}, V.mem X → ∃ n, enum n = X)
include hsurj

/-- **Exercise 1.23 — `{Yₙ}` is a total element.** Maximality: if `z` extends the greedy element
and `W ∈ z`, write `W = enum k` (surjectivity). For `k = 0`, `W = Y₀` is already in the greedy
element. For `k = m+1`: either the greedy step *accepted* `enum k` (then `W = Y_k` is in the
element), or it *rejected* it — but then `acc m ∩ enum k ∉ 𝒟`, contradicting that both `acc m`
(in the greedy element, hence in `z`) and `W` lie in the filter `z`. -/
theorem greedyElement_isTotal : V.IsTotal (greedyElement V enum henum) := by
  intro z hz W hW
  obtain ⟨k, rfl⟩ := hsurj (z.sub hW)
  cases k with
  | zero =>
    have : Y V enum 0 = enum 0 := Y_zero V enum
    rw [← this]
    exact greedyElement_mem_Y V enum henum 0
  | succ m =>
    by_cases h : cond V enum m
    · have hYk : Y V enum (m + 1) = enum (m + 1) := Y_succ_pos V enum h
      rw [← hYk]
      exact greedyElement_mem_Y V enum henum (m + 1)
    · exfalso
      apply h
      have hacc_z : z.mem (acc V enum m) := hz _ (greedyElement_mem_acc V enum henum m)
      have : z.mem (acc V enum m ∩ enum (m + 1)) := z.inter_mem hacc_z hW
      exact z.sub this

omit [DecidablePred V.mem] in
/-- **Exercise 1.23 — "all filters can be determined by sequences".** In a countable system, every
filter `x` is the *limit family* of a sequence of neighbourhoods: take `sₙ = enum n` whenever
`enum n ∈ x` and `sₙ = Δ` otherwise. Every member of `x` is some `enum k` (surjectivity), so it is
caught by `s`; conversely each `sₙ ∈ x`, so anything above some `sₙ` is in `x`. (Classical: it
selects the sequence by deciding membership in `x`.) -/
theorem filters_sequence_determined (x : V.Element) :
    ∃ s : ℕ → Set α, (∀ n, V.mem (s n)) ∧ ∀ Z, x.mem Z ↔ (V.mem Z ∧ ∃ n, s n ⊆ Z) := by
  classical
  refine ⟨fun i => if x.mem (enum i) then enum i else V.master, ?_, ?_⟩
  · intro n
    by_cases h : x.mem (enum n)
    · simp only [ite_eq_left h]; exact henum n
    · simp only [ite_eq_right h]; exact V.master_mem
  · intro Z
    constructor
    · intro hZ
      obtain ⟨k, hk⟩ := hsurj (x.sub hZ)
      have hxk : x.mem (enum k) := by rw [hk]; exact hZ
      refine ⟨x.sub hZ, k, ?_⟩
      show (if x.mem (enum k) then enum k else V.master) ⊆ Z
      rw [ite_eq_left hxk]; exact hk.subset
    · rintro ⟨hZmem, n, hn⟩
      have hsx : x.mem (if x.mem (enum n) then enum n else V.master) := by
        by_cases h : x.mem (enum n)
        · simp only [ite_eq_left h]; exact h
        · simp only [ite_eq_right h]; exact x.master_mem
      exact x.up_mem hsx hZmem hn

end Exercise123

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems.Exercise123

set_option linter.unusedVariables false

theorem example_123.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α) (enum : Nat → Set α)
  [inst : @DecidablePred (Set α) (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V)],
  (∀ (n : Nat), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V (enum n)) →
    ∀ (n : Nat),
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Consistent α V
        (@DomainTheory.NeighbourhoodSystems.Exercise123.Y α V enum inst) n :=
  @DomainTheory.NeighbourhoodSystems.Exercise123.Y_prefix_consistent

end DomainTheory.NeighbourhoodSystems.Exercise123
end
