
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_con {w : Finset (FunToken A A)} {n : Nat} {v : Finset α}
    (h : FixChain A w n v) : v ∈ A.Con := by
  match n with
  | 0 =>
    rw [h]
    exact A.con_empty
  | n + 1 =>
    obtain ⟨_, _, _, hv, _⟩ := h
    exact hv

end InfoSys

end DomainTheory.InformationSystems
