
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_mono_w {w w' : Finset (FunToken A A)} {n : Nat} {v : Finset α}
    (hw : FunCon A A w) (hw' : FunCon A A w') (h : FixChain A w n v)
    (hEntw : (functionSystem A A).EntSet w' w) : FixChain A w' n v := by
  induction n generalizing v with
  | zero => exact h
  | succ n ih =>
    obtain ⟨u, hu, huC, hvC, hEnt⟩ := h
    refine ⟨u, ih hu, huC, hvC, ?_⟩
    exact (functionSystem A A).ent_trans hw' hw hEntw hEnt

end InfoSys

end DomainTheory.InformationSystems
