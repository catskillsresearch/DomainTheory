/-ai
Entailment payloads are transitive. If two finite sets of tree tokens are consistent, every token of the intermediate set is entailed by the stronger set, and the intermediate set has a token in its entailment payload, then the stronger set has that token in its entailment payload.

Induct on the token. The bottom payload holds outright. For an atom, every atom of the nonempty atom projection of the intermediate set is a token of that set and hence entailed by the stronger set, so those atoms are entailed from the atom projection of the stronger set, which is nonempty for the same reason; transitivity of entailment in the atom information system, applied to the two consistent atom projections, gives the atom payload. For a left-pair token there are two alternatives. If the left pair projection of the intermediate set is nonempty and carries the payload, some left-pair token of that set is entailed by the stronger set, so the stronger set has empty atom projection and consistent pair projections, and the left-pair entailments restrict to entailments of the inner tokens. Either the left pair projection of the stronger set is nonempty, and the inductive hypothesis applies, or the intermediate left pair projection is contained in the singleton of the bottom and hence equals that singleton, so the inner token is the bottom; the chosen entailment then either restores a nonempty left pair projection, and the inductive hypothesis applies again, or supplies a nonempty right pair projection for the bottom disjunct. If instead the inner token is the bottom and the right pair projection of the intermediate set is nonempty, some right-pair token is entailed by the stronger set, the atom projection of the stronger set is empty, both pair projections of the stronger set are consistent, and that entailment's disjunction yields either a nonempty right pair projection or a nonempty left pair projection. The right-pair case is symmetric.
ai-/
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_atom_con_of_atoms
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairL_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon_pairR_of_right
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeEntPayload_of_no_atoms_no_pairs
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairL_ne_or_subset_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairR_ne_or_subset_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.eq_singleton_bot_of_subset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeEntPayload_trans {u v : Finset (TreeToken α)} {c : TreeToken α}
    (hv : TreeCon A v) (hu : TreeCon A u)
    (hEnts : ∀ y ∈ u, TreeEnt A v y) (hPay : TreeEntPayload A u c) :
    TreeEntPayload A v c := by
  induction c generalizing u v with
  | bot => exact trivial
  | atom x =>
    rcases hPay with ⟨hne, hA⟩
    have hlft : ∀ y ∈ atomFinset u, A.Ent (atomFinset v) y := by
      intro y hy
      exact (hEnts _ (mem_atomFinset.1 hy)).2.2
    have hne' : atomFinset v ≠ ∅ := by
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty hne
      exact (hEnts _ (mem_atomFinset.1 hy)).2.1
    exact ⟨hne', A.ent_trans (TreeCon_atom_con_of_atoms A hv hne')
      (TreeCon_atom_con_of_atoms A hu hne) hlft hA⟩
  | pairL t ih =>
    rcases hPay with ⟨hAt, hConL, hConR, hOr⟩
    rcases hOr with ⟨hne, hPayL⟩ | ⟨rfl, hRne⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      have hEy := hEnts _ (mem_pairLFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      have hConLv : TreeCon A (pairLFinset v) := TreeCon_pairL_of_right A hv hAtv
      have hConRv : TreeCon A (pairRFinset v) := hEy.2.2.2.1
      have hEntsL : ∀ y ∈ pairLFinset u, TreeEnt A (pairLFinset v) y := by
        intro y hy
        have hEy' := hEnts _ (mem_pairLFinset.1 hy)
        rcases hEy'.2.2.2.2 with ⟨_, hPay'⟩ | ⟨rfl, _⟩
        · exact ⟨hEy'.2.2.1, hPay'⟩
        · exact ⟨hConLv, trivial⟩
      refine ⟨hAtv, hConLv, hConRv, ?_⟩
      have hEntsPair : ∀ y ∈ pairLFinset u, TreeEnt A v (.pairL y) :=
        fun y hy => hEnts _ (mem_pairLFinset.1 hy)
      rcases pairL_ne_or_subset_bot A hEntsPair with hneV | hsub
      · exact Or.inl ⟨hneV, ih hConLv hConL hEntsL hPayL⟩
      · have huBot : pairLFinset u = {.bot} :=
          eq_singleton_bot_of_subset hne hsub
        have ht : t = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (huBot ▸ hPayL)
        rcases hEy.2.2.2.2 with ⟨hneV, _⟩ | ⟨_, hR⟩
        · exact Or.inl ⟨hneV, ih hConLv hConL hEntsL hPayL⟩
        · exact Or.inr ⟨ht, hR⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hRne
      have hEy := hEnts _ (mem_pairRFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      refine ⟨hAtv, TreeCon_pairL_of_right A hv hAtv, hEy.2.2.1, ?_⟩
      rcases hEy.2.2.2.2 with ⟨hneR, _⟩ | ⟨_, hneL⟩
      · exact Or.inr ⟨rfl, hneR⟩
      · exact Or.inl ⟨hneL, trivial⟩
  | pairR t ih =>
    rcases hPay with ⟨hAt, hConR, hConL, hOr⟩
    rcases hOr with ⟨hne, hPayR⟩ | ⟨rfl, hLne⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
      have hEy := hEnts _ (mem_pairRFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      have hConRv : TreeCon A (pairRFinset v) := TreeCon_pairR_of_right A hv hAtv
      have hConLv : TreeCon A (pairLFinset v) := hEy.2.2.2.1
      have hEntsR : ∀ y ∈ pairRFinset u, TreeEnt A (pairRFinset v) y := by
        intro y hy
        have hEy' := hEnts _ (mem_pairRFinset.1 hy)
        rcases hEy'.2.2.2.2 with ⟨_, hPay'⟩ | ⟨rfl, _⟩
        · exact ⟨hEy'.2.2.1, hPay'⟩
        · exact ⟨hConRv, trivial⟩
      refine ⟨hAtv, hConRv, hConLv, ?_⟩
      have hEntsPair : ∀ y ∈ pairRFinset u, TreeEnt A v (.pairR y) :=
        fun y hy => hEnts _ (mem_pairRFinset.1 hy)
      rcases pairR_ne_or_subset_bot A hEntsPair with hneV | hsub
      · exact Or.inl ⟨hneV, ih hConRv hConR hEntsR hPayR⟩
      · have huBot : pairRFinset u = {.bot} :=
          eq_singleton_bot_of_subset hne hsub
        have ht : t = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (huBot ▸ hPayR)
        rcases hEy.2.2.2.2 with ⟨hneV, _⟩ | ⟨_, hL⟩
        · exact Or.inl ⟨hneV, ih hConRv hConR hEntsR hPayR⟩
        · exact Or.inr ⟨ht, hL⟩
    · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hLne
      have hEy := hEnts _ (mem_pairLFinset.1 hs)
      have hAtv : atomFinset v = ∅ := hEy.2.1
      refine ⟨hAtv, TreeCon_pairR_of_right A hv hAtv, hEy.2.2.1, ?_⟩
      rcases hEy.2.2.2.2 with ⟨hneL, _⟩ | ⟨_, hneR⟩
      · exact Or.inr ⟨rfl, hneL⟩
      · exact Or.inl ⟨hneR, trivial⟩

end InfoSys

end DomainTheory.InformationSystems
