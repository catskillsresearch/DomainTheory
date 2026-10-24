module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.mem_pairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairL_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairR_of_right

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

/-- Payload of tree entailment (Scott §8 (8)–(12)), recursive on the token.

The extra disjuncts for `pairL bot` / `pairR bot` match official product
`ent_bot`: any nonempty pair-set entails the unique product bottom, which
`treeUnfold` identifies as both constructors. Without them, closed tree
elements could contain one encoding of `(Δ,Δ)` but not the other, and
`|T|` would fail to be order-isomorphic to `|A + (T × T)|`. -/
def TreeEntPayload (u : Finset (TreeToken α)) : TreeToken α → Prop
  | .bot => True
  | .atom x => atomFinset u ≠ ∅ ∧ A.Ent (atomFinset u) x
  | .pairL t =>
      atomFinset u = ∅ ∧ TreeCon A (pairLFinset u) ∧ TreeCon A (pairRFinset u) ∧
        ((pairLFinset u ≠ ∅ ∧ TreeEntPayload (pairLFinset u) t) ∨
          (t = .bot ∧ pairRFinset u ≠ ∅))
  | .pairR t =>
      atomFinset u = ∅ ∧ TreeCon A (pairRFinset u) ∧ TreeCon A (pairLFinset u) ∧
        ((pairRFinset u ≠ ∅ ∧ TreeEntPayload (pairRFinset u) t) ∨
          (t = .bot ∧ pairLFinset u ≠ ∅))

theorem TreeEntPayload.of_mem {u : Finset (TreeToken α)} {p : TreeToken α}
    (hu : TreeCon A u) (hp : p ∈ u) : TreeEntPayload A u p := by
  induction p generalizing u with
  | bot => exact trivial
  | atom x =>
    have hx : x ∈ atomFinset u := mem_atomFinset.2 hp
    exact ⟨Finset.ne_empty_of_mem hx,
      A.ent_refl (TreeCon.atom_con_of_atoms A hu (Finset.ne_empty_of_mem hx)) hx⟩
  | pairL t ih =>
    have ht : t ∈ pairLFinset u := mem_pairLFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon.atoms_empty_of_right A hu (Or.inl hne)
    exact ⟨hAt, TreeCon.pairL_of_right A hu hAt, TreeCon.pairR_of_right A hu hAt,
      Or.inl ⟨hne, ih (TreeCon.pairL_of_right A hu hAt) ht⟩⟩
  | pairR t ih =>
    have ht : t ∈ pairRFinset u := mem_pairRFinset.2 hp
    have hne := Finset.ne_empty_of_mem ht
    have hAt := TreeCon.atoms_empty_of_right A hu (Or.inr hne)
    exact ⟨hAt, TreeCon.pairR_of_right A hu hAt, TreeCon.pairL_of_right A hu hAt,
      Or.inl ⟨hne, ih (TreeCon.pairR_of_right A hu hAt) ht⟩⟩

theorem TreeEntPayload.of_no_atoms_no_pairs {u : Finset (TreeToken α)} {t : TreeToken α}
    (hAt : atomFinset u = ∅) (hL : pairLFinset u = ∅) (hR : pairRFinset u = ∅)
    (h : TreeEntPayload A u t) : t = .bot := by
  cases t with
  | bot => rfl
  | atom x => exact False.elim (h.1 hAt)
  | pairL t =>
    rcases h with ⟨_, _, _, hOr⟩
    rcases hOr with ⟨hne, _⟩ | ⟨_, hRne⟩
    · exact False.elim (hne hL)
    · exact False.elim (hRne hR)
  | pairR t =>
    rcases h with ⟨_, _, _, hOr⟩
    rcases hOr with ⟨hne, _⟩ | ⟨_, hLne⟩
    · exact False.elim (hne hR)
    · exact False.elim (hLne hL)

end InfoSys


end DomainTheory.InformationSystems
