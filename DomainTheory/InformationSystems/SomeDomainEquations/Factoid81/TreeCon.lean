module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

inductive TreeCon : Finset (TreeToken α) → Prop where
  | left (u : Finset (TreeToken α))
      (hA : atomFinset u ∈ A.Con)
      (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅) : TreeCon u
  | right (u : Finset (TreeToken α))
      (hA : atomFinset u = ∅)
      (hL : TreeCon (pairLFinset u)) (hR : TreeCon (pairRFinset u)) : TreeCon u

theorem TreeCon.atom_con_of_atoms {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hne : atomFinset u ≠ ∅) : atomFinset u ∈ A.Con := by
  cases hu with
  | left _ hA _ _ => exact hA
  | right _ hA _ _ => exact False.elim (hne hA)

theorem TreeCon.atoms_empty_of_right {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hP : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    atomFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR =>
    rcases hP with h | h
    · exact False.elim (h hL)
    · exact False.elim (h hR)
  | right _ hA _ _ => exact hA

theorem TreeCon.pairs_empty_of_left {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (hA : atomFinset u ≠ ∅) :
    pairLFinset u = ∅ ∧ pairRFinset u = ∅ := by
  cases hu with
  | left _ _ hL hR => exact ⟨hL, hR⟩
  | right _ hAt _ _ => exact False.elim (hA hAt)

end InfoSys

end DomainTheory.InformationSystems
