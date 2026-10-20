module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairs_empty_of_left
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_insert_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_insert_of_ent {u : Finset (TreeToken α)} {p : TreeToken α}
    (h : TreeEnt A u p) : TreeCon A (insert p u) := by
  induction p generalizing u with
  | bot =>
    exact TreeCon_insert_bot A h.1
  | atom x =>
    rcases h with ⟨hu, hne, hA⟩
    have hLR := TreeCon_pairs_empty_of_left A hu hne
    exact TreeCon.left _
      (by rw [atomFinset_insert_atom]; exact A.ent_con hA)
      (by rw [pairLFinset_insert_atom]; exact hLR.1)
      (by rw [pairRFinset_insert_atom]; exact hLR.2)
  | pairL t ih =>
    rcases h with ⟨_, hAt, hConL, hConR, hOr⟩
    refine TreeCon.right _
      (by rw [atomFinset_insert_pairL]; exact hAt) ?_
      (by rw [pairRFinset_insert_pairL]; exact hConR)
    rw [pairLFinset_insert_pairL]
    rcases hOr with ⟨_, hPay⟩ | ⟨rfl, _⟩
    · exact ih ⟨hConL, hPay⟩
    · exact TreeCon_insert_bot A hConL
  | pairR t ih =>
    rcases h with ⟨_, hAt, hConR, hConL, hOr⟩
    refine TreeCon.right _
      (by rw [atomFinset_insert_pairR]; exact hAt)
      (by rw [pairLFinset_insert_pairR]; exact hConL) ?_
    rw [pairRFinset_insert_pairR]
    rcases hOr with ⟨_, hPay⟩ | ⟨rfl, _⟩
    · exact ih ⟨hConR, hPay⟩
    · exact TreeCon_insert_bot A hConR

end InfoSys

end DomainTheory.InformationSystems
