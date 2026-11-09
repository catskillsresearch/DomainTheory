module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ApproximableMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.rel_input_output_union

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem funCon_of_approxMap (f : ApproximableMap A B) (w : Finset (FunToken A B))
    (hw : ∀ p ∈ w, f.rel p.val.1 p.val.2) : FunCon A B w :=
  fun s hs hin =>
    f.rel_cod (rel_input_output_union A B f s (fun q hq => hw q (hs hq)) hin)

end InfoSys

end DomainTheory.InformationSystems
