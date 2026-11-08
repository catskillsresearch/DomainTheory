module

public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.inf

@[expose] public section

namespace DomainTheory.InformationSystems
namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def familyInfCarrier (S : Set sys.Element) : Set α :=
  {a | ∀ x ∈ S, a ∈ x.carrier}

def familyInf (S : Set sys.Element) (hne : S.Nonempty) : sys.Element where
  carrier := sys.familyInfCarrier S
  consistent := by
    intro Y hY
    obtain ⟨x₀, hx₀⟩ := hne
    have hYx : (Y : Set α) ⊆ x₀.carrier := fun a ha => (hY ha) x₀ hx₀
    exact x₀.consistent Y hYx
  closed := by
    intro Y a hY hEnt x hx
    have hYx : (Y : Set α) ⊆ x.carrier := fun b hb => (hY hb) x hx
    exact x.closed Y a hYx hEnt

namespace familyInf

theorem le (S : Set sys.Element) (hne : S.Nonempty) {x : sys.Element}
    (hx : x ∈ S) : sys.familyInf S hne ≤ x :=
  fun _a ha => ha x hx

theorem le_of (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element}
    (h : ∀ x ∈ S, z ≤ x) : z ≤ sys.familyInf S hne :=
  fun _a ha x hx => h x hx ha

theorem le_iff (S : Set sys.Element) (hne : S.Nonempty) {z : sys.Element} :
    z ≤ sys.familyInf S hne ↔ ∀ x ∈ S, z ≤ x :=
  ⟨fun hz _x hx => le_trans hz (le sys S hne hx), le_of sys S hne⟩

theorem pair (x y : sys.Element) :
    sys.familyInf ({x, y} : Set sys.Element) ⟨x, Set.mem_insert x {y}⟩ = sys.inf x y := by
  refine le_antisymm ?_ ?_
  · exact inf.le_inf sys
      (le sys _ _ (Set.mem_insert x {y}))
      (le sys _ _ (Set.mem_insert_of_mem _ rfl))
  · apply le_of sys
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hy
    · exact inf.le_left sys _ _
    · have : z = y := hy
      subst this
      exact inf.le_right sys _ _

end familyInf

end InfoSys
end DomainTheory.InformationSystems
