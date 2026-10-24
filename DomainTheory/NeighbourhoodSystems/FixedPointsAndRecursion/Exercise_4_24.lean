module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_25
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_24
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_8
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Definition_2_1
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Theorem_2_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_2
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_2_3
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_11
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_8
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise_2_9

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise_4_14
public import Mathlib.Algebra.Group.End

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise424
open DomainTheory.NeighbourhoodSystems.Exercise414 Function

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- Tarski's operator `T(X) = (A − g(B)) ∪ g(f(X))` on `P A`. -/
def sbOp (f : A → B) (g : B → A) (X : Set A) : Set A := (Set.range g)ᶜ ∪ g '' (f '' X)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbOp_monotone (f : A → B) (g : B → A) : Monotone (sbOp f g) := by
  intro X Y hXY a ha
  rcases ha with ha | ⟨b, ⟨x, hx, rfl⟩, rfl⟩
  · exact Or.inl ha
  · exact Or.inr ⟨f x, ⟨x, hXY hx, rfl⟩, rfl⟩
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- The Tarski fixed point `X` with `X = (A − g(B)) ∪ g(f(X))` (`lfpSet`, Exercise 4.14). -/
def sbSet (f : A → B) (g : B → A) : Set A := lfpSet (sbOp f g)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbSet_isFixed (f : A → B) (g : B → A) : sbOp f g (sbSet f g) = sbSet f g :=
  lfpSet_isFixed (sbOp f g) (sbOp_monotone f g)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- `g(f(a)) ∈ X` whenever `a ∈ X` (the `g(f(X)) ⊆ T(X) = X` half). -/
theorem g_f_mem_of_mem {a : A} (ha : a ∈ sbSet f g) : g (f a) ∈ sbSet f g := by
  rw [← sbSet_isFixed]
  exact Or.inr ⟨f a, ⟨a, ha, rfl⟩, rfl⟩
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- Anything outside the fixed set `X` lies in the range of `g` (so it has a `g`-preimage). -/
theorem mem_range_of_not_mem {a : A} (ha : a ∉ sbSet f g) : a ∈ Set.range g := by
  have hne : a ∉ sbOp f g (sbSet f g) := by rw [sbSet_isFixed]; exact ha
  have : ¬ a ∉ Set.range g := fun h => hne (Or.inl h)
  exact not_not.mp this
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

open Classical in
end
end DomainTheory.NeighbourhoodSystems.Exercise424

section
namespace DomainTheory.NeighbourhoodSystems.Exercise424
open DomainTheory.NeighbourhoodSystems.Exercise414 Function
section
variable {A B : Type*} {f : A → B} {g : B → A}
open Classical in
/- concordance: source L2363 EXERCISE 4.24 Schroeder-Bernstein theorem -/
/-- **Exercise 4.24 (Scott 1981, PRG-19).** Tarski's bijection `h : A → B`: `f` on the fixed set
`X`, and the `g`-inverse off it. -/
noncomputable def sbFun (f : A → B) (g : B → A) (a : A) : B :=
  if ha : a ∈ sbSet f g then f a else Classical.choose (mem_range_of_not_mem ha)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- Off the fixed set, `h(a)` is a genuine `g`-preimage of `a`: `g(h(a)) = a`. -/
theorem g_sbFun_not_mem {a : A} (ha : a ∉ sbSet f g) : g (sbFun f g a) = a := by
  rw [sbFun, dite_eq_right ha]
  exact Classical.choose_spec (mem_range_of_not_mem ha)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_mem {a : A} (ha : a ∈ sbSet f g) : sbFun f g a = f a := dite_eq_left ha
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_injective (hf : Injective f) : Injective (sbFun f g) := by
  intro a₁ a₂ heq
  by_cases h1 : a₁ ∈ sbSet f g <;> by_cases h2 : a₂ ∈ sbSet f g
  · rw [sbFun_mem h1, sbFun_mem h2] at heq
    exact hf heq
  · -- `a₁ ∈ X`, `a₂ ∉ X`: `f a₁ = g⁻¹ a₂` ⟹ `a₂ = g(f a₁) ∈ X`, contradiction.
    exfalso
    rw [sbFun_mem h1] at heq
    have : a₂ = g (f a₁) := by rw [heq, g_sbFun_not_mem h2]
    exact h2 (this ▸ g_f_mem_of_mem h1)
  · exfalso
    rw [sbFun_mem h2] at heq
    have : a₁ = g (f a₂) := by rw [← heq, g_sbFun_not_mem h1]
    exact h1 (this ▸ g_f_mem_of_mem h2)
  · -- both off `X`: apply `g` and use injectivity of `g`.
    have : g (sbFun f g a₁) = g (sbFun f g a₂) := by rw [heq]
    rw [g_sbFun_not_mem h1, g_sbFun_not_mem h2] at this
    exact this
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

theorem sbFun_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  intro b
  by_cases hb : g b ∈ sbSet f g
  · -- `g b ∈ X = T X`; not in `(range g)ᶜ`, so `g b ∈ g(f(X))`.
    rw [← sbSet_isFixed] at hb
    rcases hb with hb | ⟨y, ⟨a, ha, rfl⟩, hgy⟩
    · exact absurd ⟨b, rfl⟩ hb
    · refine ⟨a, ?_⟩
      rw [sbFun_mem ha, hg hgy]
  · -- `g b ∉ X`: then `h (g b) = b`.
    refine ⟨g b, ?_⟩
    exact hg (g_sbFun_not_mem hb)
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

/-- **Exercise 4.24 (Scott 1981, PRG-19).** The one-one correspondence as an `Equiv A ≃ B`. -/
noncomputable def schroeder_bernstein_equiv (hf : Injective f) (hg : Injective g) : A ≃ B :=
  Equiv.ofBijective (sbFun f g) ⟨sbFun_injective hf, sbFun_surjective hg⟩
end

section
variable {A B : Type*} {f : A → B} {g : B → A}

open Classical in


/-- **Exercise 4.24 (Scott 1981, PRG-19) — Schröder–Bernstein.** Injections `f : A → B` and
`g : B → A` yield a bijection `A → B`. -/
theorem schroeder_bernstein (hf : Injective f) (hg : Injective g) :
    ∃ h : A → B, Bijective h :=
  ⟨sbFun f g, sbFun_injective hf, sbFun_surjective hg⟩
end

section
set_option linter.unusedVariables false

theorem example_424.{u_1, u_2} : ∀ {A : Type u_1} {B : Type u_2} {f : A → B} {g : B → A},
  @Function.Injective A B f → @Function.Injective B A g → ∃ (h : A → B), @Function.Bijective A B h :=
  @DomainTheory.NeighbourhoodSystems.Exercise424.schroeder_bernstein
end

end DomainTheory.NeighbourhoodSystems.Exercise424
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

section
variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

end ApproximableMap
end
end DomainTheory.NeighbourhoodSystems
end
