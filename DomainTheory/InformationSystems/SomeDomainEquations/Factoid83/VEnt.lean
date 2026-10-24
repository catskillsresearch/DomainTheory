module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.mem_vPairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- Entailment on `V` (Scott (3)–(6)). -/
inductive VEnt : Finset VToken → VToken → Prop where
  | bot {u : Finset VToken} : VEnt u .bot
  | top_mem {u : Finset VToken} (h : .top ∈ u) : VEnt u .top
  | top_both {u : Finset VToken}
      (hL : VEnt (vPairLFinset u) .top) (hR : VEnt (vPairRFinset u) .top) :
      VEnt u .top
  | pairL_top {u : Finset VToken} {x : VToken} (h : .top ∈ u) : VEnt u (.pairL x)
  | pairL_proj {u : Finset VToken} {x : VToken}
      (h : VEnt (vPairLFinset u) x) : VEnt u (.pairL x)
  | pairR_top {u : Finset VToken} {y : VToken} (h : .top ∈ u) : VEnt u (.pairR y)
  | pairR_proj {u : Finset VToken} {y : VToken}
      (h : VEnt (vPairRFinset u) y) : VEnt u (.pairR y)

end InfoSys
end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- If `u ⊢ ∇`, then `u` entails every token (rogue top). -/
theorem VEnt.of_ent_top {u : Finset VToken} (h : VEnt u .top) (c : VToken) :
    VEnt u c := by
  match c with
  | .bot => exact VEnt.bot
  | .top => exact h
  | .pairL x =>
    cases h with
    | top_mem hm => exact VEnt.pairL_top hm
    | top_both hL _ => exact VEnt.pairL_proj (VEnt.of_ent_top hL x)
  | .pairR y =>
    cases h with
    | top_mem hm => exact VEnt.pairR_top hm
    | top_both _ hR => exact VEnt.pairR_proj (VEnt.of_ent_top hR y)

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt.of_mem {u : Finset VToken} {c : VToken}
    (hc : c ∈ u) : VEnt u c := by
  induction c generalizing u with
  | bot => exact VEnt.bot
  | top => exact VEnt.top_mem hc
  | pairL x ih =>
    exact VEnt.pairL_proj (ih (mem_vPairLFinset.2 hc))
  | pairR y ih =>
    exact VEnt.pairR_proj (ih (mem_vPairRFinset.2 hc))

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- From `v ⊢ (X, Δ)`, either `∇ ∈ v` or the left projection entails `X`. -/
theorem VEnt.pairL_inv {v : Finset VToken} {x : VToken}
    (h : VEnt v (.pairL x)) : .top ∈ v ∨ VEnt (vPairLFinset v) x := by
  cases h with
  | pairL_top hm => exact Or.inl hm
  | pairL_proj h' => exact Or.inr h'

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

/-- Push an `EntSet` through the left projection (or absorb via top). -/
theorem VEnt.pairLFinset_of_EntSet {u v : Finset VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) :
    .top ∈ v ∨ (∀ y ∈ vPairLFinset u, VEnt (vPairLFinset v) y) := by
  by_cases htop : .top ∈ v
  · exact Or.inl htop
  · refine Or.inr ?_
    intro y hy
    have hy' := hEnts _ (mem_vPairLFinset.1 hy)
    rcases VEnt.pairL_inv hy' with hm | hproj
    · exact False.elim (htop hm)
    · exact hproj

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt.pairR_inv {v : Finset VToken} {y : VToken}
    (h : VEnt v (.pairR y)) : .top ∈ v ∨ VEnt (vPairRFinset v) y := by
  cases h with
  | pairR_top hm => exact Or.inl hm
  | pairR_proj h' => exact Or.inr h'

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt.pairRFinset_of_EntSet {u v : Finset VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) :
    .top ∈ v ∨ (∀ y ∈ vPairRFinset u, VEnt (vPairRFinset v) y) := by
  by_cases htop : .top ∈ v
  · exact Or.inl htop
  · refine Or.inr ?_
    intro y hy
    have hy' := hEnts _ (mem_vPairRFinset.1 hy)
    rcases VEnt.pairR_inv hy' with hm | hproj
    · exact False.elim (htop hm)
    · exact hproj

end InfoSys

end DomainTheory.InformationSystems

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem VEnt.trans {u v : Finset VToken} {c : VToken}
    (hEnts : ∀ y ∈ u, VEnt v y) (h : VEnt u c) : VEnt v c := by
  induction h generalizing v with
  | bot => exact VEnt.bot
  | top_mem hm => exact hEnts _ hm
  | top_both _ _ ihL ihR =>
    rcases VEnt.pairLFinset_of_EntSet hEnts with hm | hL
    · exact VEnt.of_ent_top (VEnt.top_mem hm) .top
    · rcases VEnt.pairRFinset_of_EntSet hEnts with hm | hR
      · exact VEnt.of_ent_top (VEnt.top_mem hm) .top
      · exact VEnt.top_both (ihL hL) (ihR hR)
  | pairL_top hm => exact VEnt.of_ent_top (hEnts _ hm) _
  | pairL_proj _ ih =>
    rcases VEnt.pairLFinset_of_EntSet hEnts with hm | hL
    · exact VEnt.pairL_top hm
    · exact VEnt.pairL_proj (ih hL)
  | pairR_top hm => exact VEnt.of_ent_top (hEnts _ hm) _
  | pairR_proj _ ih =>
    rcases VEnt.pairRFinset_of_EntSet hEnts with hm | hR
    · exact VEnt.pairR_top hm
    · exact VEnt.pairR_proj (ih hR)

end InfoSys

end DomainTheory.InformationSystems
