/-ai
Set-level entailment is monotone: if u and u' are consistent, u is contained in u', u set-entails v, and v' is contained in v, then u' set-entails v'.

A token of v' lies in v, so u entails it. Cut from u' through u applies, because u' entails every member of u by reflexivity and the inclusion of u in u'.
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

/-- **Proposition 2.3(v).** Monotonicity: `u ⊆ u'`, `u ⊢ v`, `v' ⊆ v` ⇒ `u' ⊢ v'`. -/
theorem proposition_2_3_v {u u' v v' : Finset α}
    (hu : u ∈ sys.Con) (hu' : u' ∈ sys.Con)
    (hsubu : u ⊆ u') (huv : sys.EntSet u v) (hsubv : v' ⊆ v) :
    sys.EntSet u' v' := by
  intro X hX
  have hEnt : sys.Ent u X := huv X (hsubv hX)
  refine sys.ent_trans hu' hu ?_ hEnt
  intro y hy
  exact sys.ent_refl hu' (hsubu hy)

end InfoSys
end DomainTheory.InformationSystems
