/-ai
Set-level entailment is transitive: if u and v are consistent, u set-entails v, and v set-entails w, then u set-entails w.

A token of w is entailed by v, and the cut axiom, applied to the set-entailment of v by u, yields the entailment by u.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Proposition 2.3(iv).** Transitivity of `EntSet`. -/
theorem proposition_2_3_iv {u v w : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huv : sys.EntSet u v) (hvw : sys.EntSet v w) : sys.EntSet u w :=
  fun X hX => sys.ent_trans hu hv huv (hvw X hX)

end InfoSys
end DomainTheory.InformationSystems
