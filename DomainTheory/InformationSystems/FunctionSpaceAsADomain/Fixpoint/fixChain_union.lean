module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.funEnt_union_step

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_union {w : Finset (FunToken A A)} {n : Nat} {v v' : Finset α}
    (hw : FunCon A A w) (h : FixChain A w n v) (h' : FixChain A w n v') :
    FixChain A w n (v ∪' v') := by
  induction n generalizing v v' with
  | zero =>
    rw [h, h']
    rfl
  | succ n ih =>
    obtain ⟨u, hu, huC, hvC, hEnt⟩ := h
    obtain ⟨u', hu', huC', hvC', hEnt'⟩ := h'
    have huU : u ∪' u' ∈ A.Con := fixChain_con A (ih hu hu')
    obtain ⟨hvU, hEntU⟩ := funEnt_union_step A hw huC huC' hvC hvC' hEnt hEnt' huU
    exact ⟨u ∪' u', ih hu hu', huU, hvU, hEntU⟩

end InfoSys

end DomainTheory.InformationSystems
