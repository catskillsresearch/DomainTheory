module

public import Mathlib.CategoryTheory.Category.Basic

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import Mathlib.Tactic.ToAdditive

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
export CategoryTheory (Category)

open scoped CategoryTheory

scoped notation "𝟙" => CategoryTheory.CategoryStruct.id
end

section
variable {α : Type*}

/- concordance: source L3799 DEFINITION 6.10 subdomain -/
/-- **Definition 6.10 (Scott 1981, PRG-19).** The *subsystem* (subdomain) relation `D ◁ E` for two
neighbourhood systems over the same token type. It records that `D` and `E` are systems over the
same `Δ` (`master_eq`), that `D` is a subfamily of `E` (`sub`), and — the essential clause — that
consistency is inherited from `E`: an intersection of two `D`-neighbourhoods that happens to be an
`E`-neighbourhood is already a `D`-neighbourhood (`inter_closed`). -/
structure Subsystem (D E : NeighborhoodSystem α) : Prop where
  /-- `D` and `E` are systems over the same set of tokens `Δ`. -/
  master_eq : D.master = E.master
  /-- `D ⊆ E`: every neighbourhood of `D` is a neighbourhood of `E`. -/
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  /-- Consistency in `D` is the same as in `E`: if `X, Y ∈ D` and `X ∩ Y ∈ E`, then `X ∩ Y ∈ D`. -/
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

@[inherit_doc] infix:50 " ◁ " => Subsystem

namespace Subsystem

/-- Two neighbourhood systems with the same `mem` and the same `master` are equal (the remaining
fields of `NeighborhoodSystem` are `Prop`s). -/
theorem _root_.DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.ext {D E : NeighborhoodSystem α}
    (hmem : ∀ X, D.mem X ↔ E.mem X) (hmaster : D.master = E.master) : D = E := by
  rcases D with ⟨Dmem, Dmaster, _, _, _⟩
  rcases E with ⟨Emem, Emaster, _, _, _⟩
  have hm : Dmem = Emem := funext fun X => propext (hmem X)
  subst hm
  subst hmaster
  rfl

/-- The subsystem relation is **antisymmetric**: `D ◁ E` and `E ◁ D` force `D = E`. (Mutual `sub`
gives equal `mem`, and `master_eq` gives equal masters.) -/
theorem antisymm {D E : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ D) : D = E :=
  NeighborhoodSystem.ext (fun _ => ⟨fun h => h₁.sub h, fun h => h₂.sub h⟩) h₁.master_eq

/-- The subsystem relation is **reflexive**: `D ◁ D`. (The `inter_closed` clause is trivial — the
hypothesis is already the conclusion.) -/
theorem refl (D : NeighborhoodSystem α) : D ◁ D where
  master_eq := rfl
  sub h := h
  inter_closed _ _ h := h

/-- The subsystem relation is **transitive**: `D ◁ E` and `E ◁ F` give `D ◁ F`.

The `inter_closed` clause threads through `E`: from `X, Y ∈ D ⊆ E` and `X ∩ Y ∈ F`, the relation
`E ◁ F` puts `X ∩ Y ∈ E`, and then `D ◁ E` puts `X ∩ Y ∈ D`. -/
theorem trans {D E F : NeighborhoodSystem α} (h₁ : D ◁ E) (h₂ : E ◁ F) : D ◁ F where
  master_eq := h₁.master_eq.trans h₂.master_eq
  sub h := h₂.sub (h₁.sub h)
  inter_closed hX hY hXY :=
    h₁.inter_closed hX hY (h₂.inter_closed (h₁.sub hX) (h₁.sub hY) hXY)

/-- **Scott's remark (the prose after Definition 6.10).** Once `D₀` and `D₁` both sit inside a
common system `E` as subdomains, the subdomain relation between them is just inclusion of
neighbourhood families: `D₀ ◁ D₁ ↔ D₀ ⊆ D₁`.

* `→` is the `sub` clause of `D₀ ◁ D₁`.
* `←` builds `D₀ ◁ D₁` from `D₀ ⊆ D₁`: the masters agree because both equal `E`'s master, and
  the `inter_closed` clause routes through `E` — an intersection `X ∩ Y` of `D₀`-neighbourhoods
  lying in `D₁` lies in `E` (since `D₁ ⊆ E`), and `D₀ ◁ E` then returns it to `D₀`. -/
theorem subsystem_iff_subset_of_common {D₀ D₁ E : NeighborhoodSystem α}
    (h₀ : D₀ ◁ E) (h₁ : D₁ ◁ E) :
    D₀ ◁ D₁ ↔ ∀ {X : Set α}, D₀.mem X → D₁.mem X := by
  constructor
  · intro h _ hX; exact h.sub hX
  · intro hsub
    refine ⟨h₀.master_eq.trans h₁.master_eq.symm, hsub, ?_⟩
    intro X Y hX hY hXY
    exact h₀.inter_closed hX hY (h₁.sub hXY)

end Subsystem

end

end DomainTheory.NeighbourhoodSystems
end

section
-- DomainObj.lean
universe w

namespace DomainTheory.NeighbourhoodSystems

/-- An object of the category of domains: a token type together with a neighbourhood system on it. -/
structure DomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system (the "domain"). -/
  sys : NeighborhoodSystem carrier

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- The master neighbourhood `Γ = {1,2}* 0 Δ` of `D^§`: any path, `D`-token in `Δ`. -/
def Gamma (D : NeighborhoodSystem α) : Set (List Bool × α) := {t | t.2 ∈ D.master}

/-- `1P = {(1::p, a) ∣ (p, a) ∈ P}`: the `1`-prefixed copy of a `D^§`-neighbourhood `P`. -/
def embL (P : Set (List Bool × α)) : Set (List Bool × α) := {t | ∃ p', t.1 = true :: p' ∧ (p', t.2) ∈ P}

/-- `2Q = {(2::q, a) ∣ (q, a) ∈ Q}`: the `2`-prefixed copy of a `D^§`-neighbourhood `Q`. -/
def embR (Q : Set (List Bool × α)) : Set (List Bool × α) := {t | ∃ q', t.1 = false :: q' ∧ (q', t.2) ∈ Q}

/-- `1P ∪ 2Q`: the product-style neighbourhood of `D^§`. -/
def embPair (P Q : Set (List Bool × α)) : Set (List Bool × α) := embL P ∪ embR Q

/-- `0X = {([], a) ∣ a ∈ X}`: the `0`-tagged copy of a `D`-neighbourhood `X` (empty `{1,2}`-path). -/
def embZero (X : Set α) : Set (List Bool × α) := {t | t.1 = [] ∧ t.2 ∈ X}

end Example61
end
end DomainTheory.NeighbourhoodSystems
end
