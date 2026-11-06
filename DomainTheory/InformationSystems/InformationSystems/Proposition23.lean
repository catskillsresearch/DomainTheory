module

public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_i
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_ii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iii
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_iv
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_v
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.proposition_2_3_vi

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.Constructive

theorem theorem_23 :
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
  ⟨@proposition_2_3_i, @proposition_2_3_ii, @proposition_2_3_iii,
    @proposition_2_3_iv, @proposition_2_3_v, @proposition_2_3_vi⟩

end DomainTheory.InformationSystems.InfoSys
