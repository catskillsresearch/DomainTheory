/-ai
A sum element cannot contain both a left token and a right token.

The finite set obtained by inserting the left token into the singleton of the right token is contained in the element, so the element makes it sum-consistent. Both projections of that set are nonempty, because each inserted token lies in the corresponding projection. Each disjunct of sum consistency forces one of those projections to be empty.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


theorem not_mem_right_of_mem_left (z : (sumSystem A B).Element)
    {x : α} {y : β} (hx : SumToken.left x ∈ z.carrier)
    (hy : SumToken.right y ∈ z.carrier) : False := by
  let u : Finset (SumToken α β) := insert (.left x) {SumToken.right y}
  have hsub : (↑u : Set _) ⊆ z.carrier := by
    intro p hp
    rcases Finset.mem_insert.mp (Finset.mem_coe.1 hp) with h | h
    · subst h; exact hx
    · have : p = .right y := Finset.mem_singleton.mp h
      subst this; exact hy
  have hCon := z.consistent u hsub
  have hlne : lftFinset u ≠ ∅ := by
    intro h
    have : x ∈ lftFinset u := (mem_lftFinset).2 (Finset.mem_insert_self _ _)
    rw [h] at this
    exact Finset.notMem_empty _ this
  have hrne : rhtFinset u ≠ ∅ := by
    intro h
    have : y ∈ rhtFinset u :=
      (mem_rhtFinset).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [h] at this
    exact Finset.notMem_empty _ this
  rcases hCon with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hrne hr
  · exact hlne hl

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
