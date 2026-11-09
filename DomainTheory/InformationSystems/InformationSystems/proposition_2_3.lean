module

public import DomainTheory.InformationSystems.InformationSystems.EntSet

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem proposition_2_3 :
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α),
      sys.EntSet ∅ ({sys.bot} : Finset α)) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u v : Finset α},
      u ∈ sys.Con → sys.EntSet u v → u ∪' v ∈ sys.Con) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u : Finset α},
      u ∈ sys.Con → sys.EntSet u u) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u v w : Finset α},
      u ∈ sys.Con → v ∈ sys.Con → sys.EntSet u v → sys.EntSet v w → sys.EntSet u w) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u u' v v' : Finset α},
      u ∈ sys.Con → u' ∈ sys.Con → u ⊆ u' → sys.EntSet u v → v' ⊆ v → sys.EntSet u' v') ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) {u v v' : Finset α},
      sys.EntSet u v → sys.EntSet u v' → sys.EntSet u (v ∪' v')) :=
  ⟨@EntSet.bot, @EntSet.union_mem, @EntSet.refl,
    @EntSet.trans, @EntSet.mono, @EntSet.union⟩

end InfoSys

end DomainTheory.InformationSystems
