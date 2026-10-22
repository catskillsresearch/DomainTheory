
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_pad_front
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_pad
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.funEnt_union_step
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_mono_w
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_mono_w

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_approxMap_toElement
@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


namespace ApproximableMap


/-- Tokens of `w ⊆ approxMap_toElement f` satisfy `f.rel`. -/
theorem rel_of_mem_approx (f : ApproximableMap A A)
    {w : Finset (FunToken A A)}
    (hw : ↑w ⊆ (approxMap_toElement A A f).carrier) {p : FunToken A A}
    (hp : p ∈ w) : f.rel p.val.1 p.val.2 := by
  simpa [mem_approxMap_toElement] using hw (Finset.mem_coe.2 hp)
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
