module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_1
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

section
variable {α β γ δ : Type*}

structure ApproximableMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) where

  rel : Set α → Set β → Prop

  rel_dom : ∀ {X Y}, rel X Y → V₀.mem X

  rel_cod : ∀ {X Y}, rel X Y → V₁.mem Y

  master_rel : rel V₀.master V₁.master

  inter_right : ∀ {X Y Y'}, rel X Y → rel X Y' → rel X (Y ∩ Y')

  mono : ∀ {X X' Y Y'}, rel X Y → X' ⊆ X → Y ⊆ Y' → V₀.mem X' → V₁.mem Y' → rel X' Y'

namespace ApproximableMap

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

theorem ext {f g : ApproximableMap V₀ V₁} (h : ∀ X Y, f.rel X Y ↔ g.rel X Y) : f = g := by
  obtain ⟨rf, _, _, _, _, _⟩ := f
  obtain ⟨rg, _, _, _, _, _⟩ := g
  have : rf = rg := by funext X Y; exact propext (h X Y)
  subst this; rfl

end ApproximableMap

namespace NeighborhoodSystem

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
end

end DomainTheory.NeighbourhoodSystems
