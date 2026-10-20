module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_atoms_empty_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_atom_con_of_atoms
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairL_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairR_of_right

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeEntPayload_of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEntPayload A u p := by
  induction p generalizing u with
  | bot => exact trivial
  | atom x =>
    have hx : x ∈ atomFinset u := mem_atomFinset.2 hp
    exact ⟨Finset.ne_empty_of_mem hx,
      A.ent_refl (TreeCon_atom_con_of_atoms A hu (Finset.ne_empty_of_mem hx)) hx⟩
  | pairL t ih =>
    have ht : t ∈ pairLFinset u := mem_pairLFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon_atoms_empty_of_right A hu (Or.inl hne)
    exact ⟨hAt, TreeCon_pairL_of_right A hu hAt, TreeCon_pairR_of_right A hu hAt,
      Or.inl ⟨hne, ih (TreeCon_pairL_of_right A hu hAt) ht⟩⟩
  | pairR t ih =>
    have ht : t ∈ pairRFinset u := mem_pairRFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon_atoms_empty_of_right A hu (Or.inr hne)
    exact ⟨hAt, TreeCon_pairR_of_right A hu hAt, TreeCon_pairL_of_right A hu hAt,
      Or.inl ⟨hne, ih (TreeCon_pairR_of_right A hu hAt) ht⟩⟩

end InfoSys

end DomainTheory.InformationSystems
