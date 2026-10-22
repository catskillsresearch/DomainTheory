module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.unfoldFinset
public import DomainTheory.BridgeTheorems.mem_unfoldFinset
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem rhtFinset_image_unfold_mem (u : Finset (TreeToken α))
    (y : ProdToken (treeSystem A) (treeSystem A)) :
    y ∈ rhtFinset (unfoldFinset A u) ↔
      (∃ t, .pairL t ∈ u ∧ y = ⟨(t, treeBot), ⟨Or.inr rfl⟩⟩) ∨
        (∃ t, .pairR t ∈ u ∧ y = ⟨(treeBot, t), ⟨Or.inl rfl⟩⟩) := by
  constructor
  · intro hy
    have : SumToken.right y ∈ unfoldFinset A u := (mem_rhtFinset).1 hy
    rcases (mem_unfoldFinset A).1 this with ⟨t, ht, hU⟩
    cases t with
    | pairL s =>
      refine Or.inl ⟨s, ht, ?_⟩
      exact SumToken.right.inj hU.symm
    | pairR s =>
      refine Or.inr ⟨s, ht, ?_⟩
      exact SumToken.right.inj hU.symm
    | bot | atom _ => exact nomatch hU
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact (mem_rhtFinset).2 ((mem_unfoldFinset A).2 ⟨.pairL t, ht, rfl⟩)
    · exact (mem_rhtFinset).2 ((mem_unfoldFinset A).2 ⟨.pairR t, ht, rfl⟩)

end DomainTheory.BridgeTheorems
